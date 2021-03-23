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
#![deny(unused_attributes, unused_imports, unused_mut)]
#![deny(renamed_and_removed_lints, stable_features, unused_allocation)]
#![deny(unused_comparisons, bare_trait_objects, unused_must_use, const_err)]
#![forbid(unsafe_code)]
#![allow(clippy::op_ref)]

#[macro_use]
extern crate ark_std;

use ark_ff::{to_bytes, PrimeField, ToConstraintField};
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit::Evaluations;
use ark_poly_commit::LabeledPolynomial;
use ark_poly_commit::{LabeledCommitment, PCUniversalParams, PolynomialCommitment};
use ark_relations::r1cs::{ConstraintSynthesizer, SynthesisError};
use ark_std::rand::RngCore;

#[macro_use]
extern crate ark_std;

use ark_std::{
    boxed::Box,
    collections::BTreeMap,
    format,
    marker::PhantomData,
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
pub mod fiat_shamir;
use crate::fiat_shamir::FiatShamirRng;

mod error;
pub use error::*;

mod data_structures;
pub use data_structures::*;

pub mod constraints;

/// Implements an Algebraic Holographic Proof (AHP) for the R1CS indexed relation.
pub mod ahp;
use crate::ahp::prover::ProverMsg;
pub use ahp::AHPForR1CS;
use ahp::EvaluationsProvider;
use ark_nonnative_field::params::OptimizationType;

#[cfg(test)]
mod test;

pub trait MarlinConfig: Clone {
    const FOR_RECURSION: bool;
}

#[derive(Clone)]
pub struct MarlinDefaultConfig;

impl MarlinConfig for MarlinDefaultConfig {
    const FOR_RECURSION: bool = false;
}

#[derive(Clone)]
pub struct MarlinRecursiveConfig;

impl MarlinConfig for MarlinRecursiveConfig {
    const FOR_RECURSION: bool = true;
}

/// The compiled argument system.
pub struct Marlin<
    F: PrimeField,
    FSF: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    FS: FiatShamirRng<F, FSF>,
    MC: MarlinConfig,
>(
    #[doc(hidden)] PhantomData<F>,
    #[doc(hidden)] PhantomData<FSF>,
    #[doc(hidden)] PhantomData<PC>,
    #[doc(hidden)] PhantomData<FS>,
    #[doc(hidden)] PhantomData<MC>,
);

fn compute_vk_hash<F, FSF, PC, FS>(vk: &IndexVerifierKey<F, PC>) -> Vec<FSF>
where
    F: PrimeField,
    FSF: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    FS: FiatShamirRng<F, FSF>,
    PC::Commitment: ToConstraintField<FSF>,
{
    let mut vk_hash_rng = FS::new();
    vk_hash_rng.absorb_native_field_elements(&vk.index_comms);
    vk_hash_rng.squeeze_native_field_elements(1)
}

impl<F: PrimeField, FSF: PrimeField, PC, FS, MC: MarlinConfig> Marlin<F, FSF, PC, FS, MC>
where
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    PC::VerifierKey: ToConstraintField<FSF>,
    PC::Commitment: ToConstraintField<FSF>,
    FS: FiatShamirRng<F, FSF>,
{
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

        let srs = PC::setup(max_degree, None, rng).map_err(Error::from_pc_err);
        end_timer!(setup_time);
        srs
    }

    /// Generate the index-specific (i.e., circuit-specific) prover and verifier
    /// keys. This is a trusted setup.
    #[allow(clippy::type_complexity)]
    pub fn circuit_specific_setup<C: ConstraintSynthesizer<F>, R: RngCore>(
        c: C,
        rng: &mut R,
    ) -> Result<(IndexProverKey<F, PC>, IndexVerifierKey<F, PC>), Error<PC::Error>> {
        let index_time = start_timer!(|| "Marlin::Index");

        let for_recursion = MC::FOR_RECURSION;

        // TODO: Add check that c is in the correct mode.
        let index = AHPForR1CS::index(c)?;
        let srs = PC::setup(
            index.max_degree(),
            Some(index.index_info.num_variables),
            rng,
        )
        .map_err(Error::from_pc_err)?;

        let coeff_support = AHPForR1CS::get_degree_bounds(&index.index_info);

        // Marlin only needs degree 2 random polynomials
        let supported_hiding_bound = 1;
        let (committer_key, verifier_key) = PC::trim(
            &srs,
            index.max_degree(),
            supported_hiding_bound,
            Some(&coeff_support),
        )
        .map_err(Error::from_pc_err)?;

        let mut vanishing_polys = vec![];
        if for_recursion {
            let domain_h = GeneralEvaluationDomain::new(index.index_info.num_constraints)
                .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
            let domain_k = GeneralEvaluationDomain::new(index.index_info.num_non_zero)
                .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

            vanishing_polys = vec![
                LabeledPolynomial::new(
                    "vanishing_poly_h".to_string(),
                    domain_h.vanishing_polynomial().into(),
                    None,
                    None,
                ),
                LabeledPolynomial::new(
                    "vanishing_poly_k".to_string(),
                    domain_k.vanishing_polynomial().into(),
                    None,
                    None,
                ),
            ];
        }

        let commit_time = start_timer!(|| "Commit to index polynomials");
        let (index_comms, index_comm_rands): (_, _) = PC::commit(
            &committer_key,
            index.iter().chain(vanishing_polys.iter()),
            None,
        )
        .map_err(Error::from_pc_err)?;
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

    /// Generate the index-specific (i.e., circuit-specific) prover and verifier
    /// keys. This is a deterministic algorithm that anyone can rerun.
    #[allow(clippy::type_complexity)]
    pub fn index<C: ConstraintSynthesizer<F>>(
        srs: &UniversalSRS<F, PC>,
        c: C,
    ) -> Result<(IndexProverKey<F, PC>, IndexVerifierKey<F, PC>), Error<PC::Error>> {
        let index_time = start_timer!(|| "Marlin::Index");

        let for_recursion = MC::FOR_RECURSION;

        // TODO: Add check that c is in the correct mode.
        let index = AHPForR1CS::index(c)?;
        if srs.max_degree() < index.max_degree() {
            return Err(Error::IndexTooLarge(index.max_degree()));
        }

        let coeff_support = AHPForR1CS::get_degree_bounds(&index.index_info);

        // Marlin only needs degree 2 random polynomials
        let supported_hiding_bound = 1;
        let (committer_key, verifier_key) = PC::trim(
            &srs,
            index.max_degree(),
            supported_hiding_bound,
            Some(&coeff_support),
        )
        .map_err(Error::from_pc_err)?;

        let mut vanishing_polys = vec![];
        if for_recursion {
            let domain_h = GeneralEvaluationDomain::new(index.index_info.num_constraints)
                .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
            let domain_k = GeneralEvaluationDomain::new(index.index_info.num_non_zero)
                .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

            vanishing_polys = vec![
                LabeledPolynomial::new(
                    "vanishing_poly_h".to_string(),
                    domain_h.vanishing_polynomial().into(),
                    None,
                    None,
                ),
                LabeledPolynomial::new(
                    "vanishing_poly_k".to_string(),
                    domain_k.vanishing_polynomial().into(),
                    None,
                    None,
                ),
            ];
        }

        let commit_time = start_timer!(|| "Commit to index polynomials");
        let (index_comms, index_comm_rands): (_, _) = PC::commit(
            &committer_key,
            index.iter().chain(vanishing_polys.iter()),
            None,
        )
        .map_err(Error::from_pc_err)?;
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
        index_pk: &IndexProverKey<F, PC>,
        c: C,
        zk_rng: &mut R,
    ) -> Result<Proof<F, PC>, Error<PC::Error>> {
        let prover_time = start_timer!(|| "Marlin::Prover");
        // TODO: Add check that c is in the correct mode.

        let for_recursion = MC::FOR_RECURSION;

        let prover_init_state = AHPForR1CS::prover_init(&index_pk.index, c)?;
        let public_input = prover_init_state.public_input();

        let mut fs_rng = FS::new();

        let hiding = !for_recursion;

        if for_recursion {
            fs_rng.absorb_bytes(&to_bytes![&Self::PROTOCOL_NAME].unwrap());
            fs_rng.absorb_native_field_elements(&compute_vk_hash::<F, FSF, PC, FS>(
                &index_pk.index_vk,
            ));
            fs_rng.absorb_nonnative_field_elements(&public_input, OptimizationType::Weight);
        } else {
            fs_rng.absorb_bytes(
                &to_bytes![&Self::PROTOCOL_NAME, &index_pk.index_vk, &public_input].unwrap(),
            );
        }

        // --------------------------------------------------------------------
        // First round

        let (prover_first_msg, prover_first_oracles, prover_state) =
            AHPForR1CS::prover_first_round(prover_init_state, zk_rng, hiding)?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_comms, first_comm_rands) = PC::commit(
            &index_pk.committer_key,
            prover_first_oracles.iter(),
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(first_round_comm_time);

        if for_recursion {
            fs_rng.absorb_native_field_elements(&first_comms);
            match prover_first_msg.clone() {
                ProverMsg::EmptyMessage => (),
                ProverMsg::FieldElements(v) => {
                    fs_rng.absorb_nonnative_field_elements(&v, OptimizationType::Weight)
                }
            }
        } else {
            fs_rng.absorb_bytes(&to_bytes![first_comms, prover_first_msg].unwrap());
        }

        let (verifier_first_msg, verifier_state) =
            AHPForR1CS::verifier_first_round(index_pk.index_vk.index_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        let (prover_second_msg, prover_second_oracles, prover_state) =
            AHPForR1CS::prover_second_round(&verifier_first_msg, prover_state, zk_rng, hiding);

        let second_round_comm_time = start_timer!(|| "Committing to second round polys");
        let (second_comms, second_comm_rands) = PC::commit(
            &index_pk.committer_key,
            prover_second_oracles.iter(),
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(second_round_comm_time);

        if for_recursion {
            fs_rng.absorb_native_field_elements(&second_comms);
            match prover_second_msg.clone() {
                ProverMsg::EmptyMessage => (),
                ProverMsg::FieldElements(v) => {
                    fs_rng.absorb_nonnative_field_elements(&v, OptimizationType::Weight)
                }
            }
        } else {
            fs_rng.absorb_bytes(&to_bytes![second_comms, prover_second_msg].unwrap());
        }

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

        if for_recursion {
            fs_rng.absorb_native_field_elements(&third_comms);
            match prover_third_msg.clone() {
                ProverMsg::EmptyMessage => (),
                ProverMsg::FieldElements(v) => {
                    fs_rng.absorb_nonnative_field_elements(&v, OptimizationType::Weight)
                }
            }
        } else {
            fs_rng.absorb_bytes(&to_bytes![third_comms, prover_third_msg].unwrap());
        }

        let verifier_state = AHPForR1CS::verifier_third_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        let vanishing_polys = if for_recursion {
            let domain_h = GeneralEvaluationDomain::new(index_pk.index.index_info.num_constraints)
                .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
            let domain_k = GeneralEvaluationDomain::new(index_pk.index.index_info.num_non_zero)
                .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

            vec![
                LabeledPolynomial::new(
                    "vanishing_poly_h".to_string(),
                    domain_h.vanishing_polynomial().into(),
                    None,
                    None,
                ),
                LabeledPolynomial::new(
                    "vanishing_poly_k".to_string(),
                    domain_k.vanishing_polynomial().into(),
                    None,
                    None,
                ),
            ]
        } else {
            vec![]
        };

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = index_pk
            .index
            .iter()
            .chain(vanishing_polys.iter())
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

        let indexer_polynomials = if for_recursion {
            AHPForR1CS::<F>::INDEXER_POLYNOMIALS_WITH_VANISHING
                .clone()
                .to_vec()
        } else {
            AHPForR1CS::<F>::INDEXER_POLYNOMIALS.clone().to_vec()
        };

        let labeled_comms: Vec<_> = index_pk
            .index_vk
            .iter()
            .cloned()
            .zip(indexer_polynomials)
            .map(|(c, l)| LabeledCommitment::new(l.to_string(), c, None))
            .chain(first_comms.iter().cloned())
            .chain(second_comms.iter().cloned())
            .chain(third_comms.iter().cloned())
            .collect();

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
            AHPForR1CS::verifier_query_set(verifier_state, &mut fs_rng, for_recursion);
        let lc_s = AHPForR1CS::construct_linear_combinations(
            &public_input,
            &polynomials,
            &verifier_state,
            for_recursion,
        )?;

        let eval_time = start_timer!(|| "Evaluating linear combinations over query set");
        let mut evaluations_unsorted = Vec::<(String, F)>::new();
        for (label, (_, point)) in &query_set {
            let lc = lc_s
                .iter()
                .find(|lc| &lc.label == label)
                .ok_or_else(|| ahp::Error::MissingEval(label.to_string()))?;
            let eval = polynomials.get_lc_eval(&lc, *point)?;
            if !AHPForR1CS::<F>::LC_WITH_ZERO_EVAL.contains(&lc.label.as_ref()) {
                evaluations_unsorted.push((label.to_string(), eval));
            }
        }

        evaluations_unsorted.sort_by(|a, b| a.0.cmp(&b.0));
        let evaluations = evaluations_unsorted.iter().map(|x| x.1).collect::<Vec<F>>();
        end_timer!(eval_time);

        if for_recursion {
            fs_rng.absorb_nonnative_field_elements(&evaluations, OptimizationType::Weight);
        } else {
            fs_rng.absorb_bytes(&to_bytes![&evaluations].unwrap());
        }

        let pc_proof = if for_recursion {
            let num_open_challenges: usize = 7;

            let mut opening_challenges = Vec::<F>::new();
            opening_challenges
                .append(&mut fs_rng.squeeze_128_bits_nonnative_field_elements(num_open_challenges));

            let opening_challenges_f = |i| opening_challenges[i as usize];

            PC::open_combinations_individual_opening_challenges(
                &index_pk.committer_key,
                &lc_s,
                polynomials,
                &labeled_comms,
                &query_set,
                &opening_challenges_f,
                &comm_rands,
                Some(zk_rng),
            )
            .map_err(Error::from_pc_err)?
        } else {
            let opening_challenge: F = fs_rng.squeeze_128_bits_nonnative_field_elements(1)[0];

            PC::open_combinations(
                &index_pk.committer_key,
                &lc_s,
                polynomials,
                &labeled_comms,
                &query_set,
                opening_challenge,
                &comm_rands,
                Some(zk_rng),
            )
            .map_err(Error::from_pc_err)?
        };

        // Gather prover messages together.
        let prover_messages = vec![prover_first_msg, prover_second_msg, prover_third_msg];

        let proof = Proof::new(commitments, evaluations, prover_messages, pc_proof);
        proof.print_size_info();
        end_timer!(prover_time);
        Ok(proof)
    }

    /// Verify that a proof for the constrain system defined by `C` asserts that
    /// all constraints are satisfied.
    pub fn verify(
        index_vk: &IndexVerifierKey<F, PC>,
        public_input: &[F],
        proof: &Proof<F, PC>,
    ) -> Result<bool, Error<PC::Error>> {
        let verifier_time = start_timer!(|| "Marlin::Verify");

        let public_input = {
            let domain_x = GeneralEvaluationDomain::<F>::new(public_input.len() + 1).unwrap();

            let mut unpadded_input = public_input.to_vec();
            unpadded_input.resize(
                core::cmp::max(public_input.len(), domain_x.size() - 1),
                F::zero(),
            );

            unpadded_input
        };

        let for_recursion = MC::FOR_RECURSION;

        let mut fs_rng = FS::new();

        if for_recursion {
            fs_rng.absorb_bytes(&to_bytes![&Self::PROTOCOL_NAME].unwrap());
            fs_rng.absorb_native_field_elements(&compute_vk_hash::<F, FSF, PC, FS>(index_vk));
            fs_rng.absorb_nonnative_field_elements(&public_input, OptimizationType::Weight);
        } else {
            fs_rng
                .absorb_bytes(&to_bytes![&Self::PROTOCOL_NAME, &index_vk, &public_input].unwrap());
        }

        // --------------------------------------------------------------------
        // First round
        let first_comms = &proof.commitments[0];
        if for_recursion {
            fs_rng.absorb_native_field_elements(&first_comms);
            match proof.prover_messages[0].clone() {
                ProverMsg::EmptyMessage => (),
                ProverMsg::FieldElements(v) => {
                    fs_rng.absorb_nonnative_field_elements(&v, OptimizationType::Weight)
                }
            };
        } else {
            fs_rng.absorb_bytes(&to_bytes![first_comms, proof.prover_messages[0]].unwrap());
        }

        let (_, verifier_state) =
            AHPForR1CS::verifier_first_round(index_vk.index_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round
        let second_comms = &proof.commitments[1];

        if for_recursion {
            fs_rng.absorb_native_field_elements(&second_comms);
            match proof.prover_messages[1].clone() {
                ProverMsg::EmptyMessage => (),
                ProverMsg::FieldElements(v) => {
                    fs_rng.absorb_nonnative_field_elements(&v, OptimizationType::Weight)
                }
            };
        } else {
            fs_rng.absorb_bytes(&to_bytes![second_comms, proof.prover_messages[1]].unwrap());
        }

        let (_, verifier_state) = AHPForR1CS::verifier_second_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        let third_comms = &proof.commitments[2];

        if for_recursion {
            fs_rng.absorb_native_field_elements(&third_comms);
            match proof.prover_messages[2].clone() {
                ProverMsg::EmptyMessage => (),
                ProverMsg::FieldElements(v) => {
                    fs_rng.absorb_nonnative_field_elements(&v, OptimizationType::Weight)
                }
            };
        } else {
            fs_rng.absorb_bytes(&to_bytes![third_comms, proof.prover_messages[2]].unwrap());
        }

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

        let polynomial_labels: Vec<String> = if for_recursion {
            AHPForR1CS::<F>::polynomial_labels_with_vanishing().collect()
        } else {
            AHPForR1CS::<F>::polynomial_labels().collect()
        };

        // Gather commitments in one vector.
        let commitments: Vec<_> = index_vk
            .iter()
            .chain(first_comms)
            .chain(second_comms)
            .chain(third_comms)
            .cloned()
            .zip(polynomial_labels)
            .zip(degree_bounds)
            .map(|((c, l), d)| LabeledCommitment::new(l, c, d))
            .collect();

        let (query_set, verifier_state) =
            AHPForR1CS::verifier_query_set(verifier_state, &mut fs_rng, for_recursion);

        if for_recursion {
            fs_rng.absorb_nonnative_field_elements(&proof.evaluations, OptimizationType::Weight);
        } else {
            fs_rng.absorb_bytes(&to_bytes![&proof.evaluations].unwrap());
        }

        let mut evaluations = Evaluations::new();

        let mut evaluation_labels = Vec::<(String, F)>::new();

        for q in query_set.iter().cloned() {
            if AHPForR1CS::<F>::LC_WITH_ZERO_EVAL.contains(&q.0.as_ref()) {
                evaluations.insert((q.0.clone(), (q.1).1), F::zero());
            } else {
                evaluation_labels.push((q.0.clone(), (q.1).1));
            }
        }
        evaluation_labels.sort_by(|a, b| a.0.cmp(&b.0));
        for (q, eval) in evaluation_labels.into_iter().zip(&proof.evaluations) {
            evaluations.insert(q, *eval);
        }

        let lc_s = AHPForR1CS::construct_linear_combinations(
            &public_input,
            &evaluations,
            &verifier_state,
            for_recursion,
        )?;

        let evaluations_are_correct = if for_recursion {
            let num_open_challenges: usize = 7;

            let mut opening_challenges = Vec::<F>::new();
            opening_challenges
                .append(&mut fs_rng.squeeze_128_bits_nonnative_field_elements(num_open_challenges));

            let opening_challenges_f = |i| opening_challenges[i as usize];

            PC::check_combinations_individual_opening_challenges(
                &index_vk.verifier_key,
                &lc_s,
                &commitments,
                &query_set,
                &evaluations,
                &proof.pc_proof,
                &opening_challenges_f,
                &mut fs_rng,
            )
            .map_err(Error::from_pc_err)?
        } else {
            let opening_challenge: F = fs_rng.squeeze_128_bits_nonnative_field_elements(1)[0];

            PC::check_combinations(
                &index_vk.verifier_key,
                &lc_s,
                &commitments,
                &query_set,
                &evaluations,
                &proof.pc_proof,
                opening_challenge,
                &mut fs_rng,
            )
            .map_err(Error::from_pc_err)?
        };

        if !evaluations_are_correct {
            eprintln!("PC::Check failed");
        }
        end_timer!(verifier_time, || format!(
            " PC::Check for AHP Verifier linear equations: {}",
            evaluations_are_correct
        ));
        Ok(evaluations_are_correct)
    }

    pub fn prepared_verify(
        prepared_vk: &PreparedIndexVerifierKey<F, PC>,
        public_input: &[F],
        proof: &Proof<F, PC>,
    ) -> Result<bool, Error<PC::Error>> {
        Self::verify(&prepared_vk.orig_vk, public_input, proof)
    }
}
