#![cfg_attr(not(feature = "std"), no_std)]
//! A crate for the Marlin preprocessing zkSNARK for R1CS.
//!
//! # Note
//!
//! Currently, Marlin only supports R1CS instances where the number of inputs
//! is the same as the number of constraints (i.e., where the constraint
//! matrices are square). Furthermore, Marlin only supports instances where the
//! public inputs are of size one less than a power of 2 (i.e., 2^n - 1).
#![deny(unused_import_braces, unused_qualifications, trivial_casts)]
#![deny(trivial_numeric_casts, private_in_public)]
#![deny(stable_features, unreachable_pub, non_shorthand_field_patterns)]
#![deny(unused_attributes, unused_imports, unused_mut, missing_docs)]
#![deny(renamed_and_removed_lints, stable_features, unused_allocation)]
#![deny(unused_comparisons, bare_trait_objects, unused_must_use, const_err)]
#![forbid(unsafe_code)]

#[macro_use]
extern crate bench_utils;

use algebra_core::to_bytes;
use algebra_core::PrimeField;
use algebra_core::ToBytes;
use algebra_core::UniformRand;
use core::marker::PhantomData;
use digest::Digest;
use poly_commit::Evaluations;
use poly_commit::{LabeledCommitment, PCUniversalParams, PolynomialCommitment};
use r1cs_core::ConstraintSynthesizer;
use rand_core::RngCore;

#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc;

#[cfg(not(feature = "std"))]
use alloc::{
    borrow::Cow,
    collections::BTreeMap,
    string::{String, ToString},
    vec::Vec,
};

#[cfg(feature = "std")]
use std::{
    borrow::Cow,
    collections::BTreeMap,
    string::{String, ToString},
    vec::Vec,
};

#[cfg(not(feature = "std"))]
macro_rules! eprintln {
    () => {};
    ($($arg: tt)*) => {};
}

/// Implements a Fiat-Shamir based Rng that allows one to incrementally update
/// the seed based on new messages in the proof transcript.
pub mod rng;
use rng::FiatShamirRng;

mod error;
pub use error::*;

mod data_structures;
pub use data_structures::*;

/// Implements an Algebraic Holographic Proof (AHP) for the R1CS indexed relation.
pub mod ahp;
pub use ahp::AHPForR1CS;
use ahp::EvaluationsProvider;

#[cfg(test)]
mod test;

/// The compiled argument system.
pub struct Marlin<F: PrimeField, PC: PolynomialCommitment<F>, D: Digest>(
    #[doc(hidden)] PhantomData<F>,
    #[doc(hidden)] PhantomData<PC>,
    #[doc(hidden)] PhantomData<D>,
);

impl<F: PrimeField, PC: PolynomialCommitment<F>, D: Digest> Marlin<F, PC, D> {
    /// The personalization string for this protocol. Used to personalize the
    /// Fiat-Shamir rng.
    pub const PROTOCOL_NAME: &'static [u8] = b"MARLIN-2019";

    /// Generate the universal prover and verifier keys for the
    /// argument system.
    pub fn universal_setup<R: RngCore>(
        num_constraints: usize,
        num_variables: usize,
        num_non_zero: usize,
        rng: &mut R,
    ) -> Result<UniversalSRS<F, PC>, Error<PC::Error>> {
        let max_degree = AHPForR1CS::<F>::max_degree(num_constraints, num_variables, num_non_zero)?;
        let setup_time = start_timer!(|| {
            format!(
            "Marlin::UniversalSetup with max_degree {}, computed for a maximum of {} constraints, {} vars, {} non_zero",
            max_degree, num_constraints, num_variables, num_non_zero,
        )
        });

        let srs = PC::setup(max_degree, rng).map_err(Error::from_pc_err);
        end_timer!(setup_time);
        srs
    }

    /// Generate the index-specific (i.e., circuit-specific) prover and verifier
    /// keys. This is a deterministic algorithm that anyone can rerun.
    pub fn index<C: ConstraintSynthesizer<F>>(
        srs: &UniversalSRS<F, PC>,
        c: C,
    ) -> Result<(IndexProverKey<F, PC, C>, IndexVerifierKey<F, PC, C>), Error<PC::Error>> {
        let index_time = start_timer!(|| "Marlin::Index");

        // TODO: Add check that c is in the correct mode.
        let index = AHPForR1CS::index(c)?;
        if srs.max_degree() < index.max_degree() {
            Err(Error::IndexTooLarge)?;
        }

        let coeff_support = AHPForR1CS::get_degree_bounds::<C>(&index.index_info);
        let (committer_key, verifier_key) =
            PC::trim(srs, index.max_degree(), Some(&coeff_support)).map_err(Error::from_pc_err)?;

        let commit_time = start_timer!(|| "Commit to index polynomials");
        let (index_comms, index_comm_rands): (_, _) =
            PC::commit(&committer_key, index.iter(), None).map_err(Error::from_pc_err)?;
        end_timer!(commit_time);

        let index_comms = index_comms
            .into_iter()
            .map(|c| c.commitment().clone())
            .collect();
        let index_vk = IndexVerifierKey {
            index_info: index.index_info,
            index_comms,
            verifier_key,
        };

        let index_pk = IndexProverKey {
            index,
            index_comm_rands,
            index_vk: index_vk.clone(),
            committer_key,
        };

        end_timer!(index_time);

        Ok((index_pk, index_vk))
    }

    /// Create a zkSNARK asserting that the constraint system is satisfied.
    pub fn prove<C: ConstraintSynthesizer<F>, R: RngCore>(
        index_pk: &IndexProverKey<F, PC, C>,
        c: C,
        zk_rng: &mut R,
    ) -> Result<Proof<F, PC, C>, Error<PC::Error>> {
        let prover_time = start_timer!(|| "Marlin::Prover");
        // Add check that c is in the correct mode.

        let prover_init_state = AHPForR1CS::prover_init(&index_pk.index, c)?;
        let public_input = prover_init_state.public_input();
        let mut fs_rng = FiatShamirRng::<D>::from_seed(
            &to_bytes![&Self::PROTOCOL_NAME, &index_pk.index_vk, &public_input].unwrap(),
        );

        // --------------------------------------------------------------------
        // First round

        let (prover_first_msg, prover_first_oracles, prover_state) =
            AHPForR1CS::prover_first_round(prover_init_state, zk_rng)?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_comms, first_comm_rands) = PC::commit(
            &index_pk.committer_key,
            prover_first_oracles.iter(),
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(first_round_comm_time);

        fs_rng.absorb(&to_bytes![first_comms, prover_first_msg].unwrap());

        let (verifier_first_msg, verifier_state) =
            AHPForR1CS::verifier_first_round(index_pk.index_vk.index_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        let (prover_second_msg, prover_second_oracles, prover_state) =
            AHPForR1CS::prover_second_round(&verifier_first_msg, prover_state, zk_rng);

        let second_round_comm_time = start_timer!(|| "Committing to second round polys");
        let (second_comms, second_comm_rands) = PC::commit(
            &index_pk.committer_key,
            prover_second_oracles.iter(),
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(second_round_comm_time);

        fs_rng.absorb(&to_bytes![second_comms, prover_second_msg].unwrap());

        let (verifier_second_msg, verifier_state) =
            AHPForR1CS::verifier_second_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        let (prover_third_msg, prover_third_oracles) =
            AHPForR1CS::prover_third_round(&verifier_second_msg, prover_state, zk_rng)?;

        let third_round_comm_time = start_timer!(|| "Committing to third round polys");
        let (third_comms, third_comm_rands) = PC::commit(
            &index_pk.committer_key,
            prover_third_oracles.iter(),
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(third_round_comm_time);

        fs_rng.absorb(&to_bytes![third_comms, prover_third_msg].unwrap());

        let verifier_state = AHPForR1CS::verifier_third_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = index_pk
            .index
            .iter()
            .chain(prover_first_oracles.iter())
            .chain(prover_second_oracles.iter())
            .chain(prover_third_oracles.iter())
            .collect();

        // Gather commitments in one vector.
        #[rustfmt::skip]
        let commitments = vec![
            first_comms.iter().map(|p| p.commitment().clone()).collect(),
            second_comms.iter().map(|p| p.commitment().clone()).collect(),
            third_comms.iter().map(|p| p.commitment().clone()).collect(),
        ];

        // Gather commitment randomness together.
        let comm_rands: Vec<PC::Randomness> = index_pk
            .index_comm_rands
            .clone()
            .into_iter()
            .chain(first_comm_rands)
            .chain(second_comm_rands)
            .chain(third_comm_rands)
            .collect();

        // Compute the AHP verifier's query set.
        let (query_set, verifier_state) =
            AHPForR1CS::verifier_query_set(verifier_state, &mut fs_rng);
        let lc_s = AHPForR1CS::construct_linear_combinations(
            &public_input,
            &polynomials,
            &verifier_state,
        )?;

        let eval_time = start_timer!(|| "Evaluating linear combinations over query set");
        let mut evaluations = Vec::new();
        for (label, point) in &query_set {
            let lc = lc_s
                .iter()
                .find(|lc| &lc.label == label)
                .ok_or(ahp::Error::MissingEval(label.to_string()))?;
            let eval = polynomials.get_lc_eval(&lc, *point)?;
            if !AHPForR1CS::<F>::LC_WITH_ZERO_EVAL.contains(&lc.label.as_ref()) {
                evaluations.push(eval);
            }
        }
        end_timer!(eval_time);

        fs_rng.absorb(&evaluations);
        let opening_challenge: F = u128::rand(&mut fs_rng).into();

        let pc_proof = PC::open_combinations(
            &index_pk.committer_key,
            &lc_s,
            polynomials,
            &query_set,
            opening_challenge,
            &comm_rands,
        )
        .map_err(Error::from_pc_err)?;

        // Gather prover messages together.
        let prover_messages = vec![prover_first_msg, prover_second_msg, prover_third_msg];

        let proof = Proof::new(commitments, evaluations, prover_messages, pc_proof);
        proof.print_size_info();
        end_timer!(prover_time);
        Ok(proof)
    }

    /// Verify that a proof for the constrain system defined by `C` asserts that
    /// all constraints are satisfied.
    pub fn verify<C: ConstraintSynthesizer<F>, R: RngCore>(
        index_vk: &IndexVerifierKey<F, PC, C>,
        public_input: &[F],
        proof: &Proof<F, PC, C>,
        rng: &mut R,
    ) -> Result<bool, Error<PC::Error>> {
        let verifier_time = start_timer!(|| "Marlin::Verify");

        let mut fs_rng = FiatShamirRng::<D>::from_seed(
            &to_bytes![&Self::PROTOCOL_NAME, &index_vk, &public_input].unwrap(),
        );

        // --------------------------------------------------------------------
        // First round

        let first_comms = &proof.commitments[0];
        fs_rng.absorb(&to_bytes![first_comms, proof.prover_messages[0]].unwrap());

        let (_, verifier_state) =
            AHPForR1CS::verifier_first_round(index_vk.index_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round
        let second_comms = &proof.commitments[1];
        fs_rng.absorb(&to_bytes![second_comms, proof.prover_messages[1]].unwrap());

        let (_, verifier_state) = AHPForR1CS::verifier_second_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        let third_comms = &proof.commitments[2];
        fs_rng.absorb(&to_bytes![third_comms, proof.prover_messages[2]].unwrap());

        let verifier_state = AHPForR1CS::verifier_third_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // Collect degree bounds for commitments. Indexed polynomials have *no*
        // degree bounds because we know the committed index polynomial has the
        // correct degree.
        let index_info = index_vk.index_info;
        let degree_bounds = vec![None; index_vk.index_comms.len()]
            .into_iter()
            .chain(AHPForR1CS::prover_first_round_degree_bounds(&index_info))
            .chain(AHPForR1CS::prover_second_round_degree_bounds(&index_info))
            .chain(AHPForR1CS::prover_third_round_degree_bounds(&index_info))
            .collect::<Vec<_>>();

        // Gather commitments in one vector.
        let commitments: Vec<_> = index_vk
            .iter()
            .chain(first_comms)
            .chain(second_comms)
            .chain(third_comms)
            .cloned()
            .zip(&AHPForR1CS::<F>::ALL_POLYNOMIALS)
            .zip(degree_bounds)
            .map(|((comm, label), degree_bound)| {
                LabeledCommitment::new(label.to_string(), comm, degree_bound)
            })
            .collect();

        let (query_set, verifier_state) =
            AHPForR1CS::verifier_query_set(verifier_state, &mut fs_rng);

        fs_rng.absorb(&proof.evaluations);
        let opening_challenge: F = u128::rand(&mut fs_rng).into();

        let mut evaluations = Evaluations::new();
        let mut proof_evals = proof.evaluations.iter();
        for q in query_set.iter().cloned() {
            if AHPForR1CS::<F>::LC_WITH_ZERO_EVAL.contains(&q.0.as_ref()) {
                evaluations.insert(q, F::zero());
            } else {
                evaluations.insert(q, proof_evals.next().unwrap().clone());
            }
        }

        let lc_s = AHPForR1CS::construct_linear_combinations(
            &public_input,
            &evaluations,
            &verifier_state,
        )?;

        let evaluations_are_correct = PC::check_combinations(
            &index_vk.verifier_key,
            &lc_s,
            &commitments,
            &query_set,
            &evaluations,
            &proof.pc_proof,
            opening_challenge,
            rng,
        )
        .map_err(Error::from_pc_err)?;

        if !evaluations_are_correct {
            eprintln!("PC::Check failed");
        }
        end_timer!(verifier_time, || format!(
            " PC::Check for AHP Verifier linear equations: {}",
            evaluations_are_correct
        ));
        Ok(evaluations_are_correct)
    }
}
