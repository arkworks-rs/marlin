use crate::{
    ahp::{CryptographicSpongeVarNonNative, CryptographicSpongeWithDefault},
    constraints::ahp::AHPForR1CS,
    constraints::data_structures::{IndexVerifierKeyVar, PreparedIndexVerifierKeyVar, ProofVar},
    Error, PhantomData, PrimeField, String, Vec,
};
use ark_nonnative_field::NonNativeFieldVar;
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::{PCCheckRandomDataVar, PCCheckVar, PolynomialCommitment};
use ark_r1cs_std::{bits::boolean::Boolean, fields::FieldVar, R1CSVar, ToConstraintFieldGadget};
use ark_relations::ns;
use ark_sponge::{Absorb, CryptographicSponge};

pub struct Marlin<
    F: PrimeField,
    CF: PrimeField,
    S: CryptographicSponge,
    PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
    PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF, S>,
>(
    PhantomData<F>,
    PhantomData<CF>,
    PhantomData<S>,
    PhantomData<PC>,
    PhantomData<PCG>,
);

impl<F, CF, S, PC, PCG> Marlin<F, CF, S, PC, PCG>
where
    F: PrimeField,
    CF: PrimeField + Absorb,
    S: CryptographicSpongeWithDefault,
    PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
    PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF, S>,
    PCG::VerifierKeyVar: ToConstraintFieldGadget<CF>,
    PCG::CommitmentVar: ToConstraintFieldGadget<CF>,
{
    pub const PROTOCOL_NAME: &'static [u8] = b"MARLIN-2019";

    /// verify with an established hashchain initial state
    #[tracing::instrument(target = "r1cs", skip(index_pvk, proof))]
    pub fn prepared_verify<SVN: CryptographicSpongeVarNonNative<F, CF, S>>(
        index_pvk: &PreparedIndexVerifierKeyVar<F, CF, S, SVN, PC, PCG>,
        public_input: &[NonNativeFieldVar<F, CF>],
        proof: &ProofVar<F, CF, S, PC, PCG>,
    ) -> Result<Boolean<CF>, Error<PC::Error>> {
        let cs = index_pvk
            .cs
            .clone()
            .or(public_input.cs())
            .or(proof.cs.clone());

        let mut sponge_var = index_pvk.sponge_var.clone();

        eprintln!("before AHP: constraints: {}", cs.num_constraints());

        sponge_var.absorb_nonnative(&public_input)?;

        let (_, verifier_state) = AHPForR1CS::<F, CF, S, SVN, PC, PCG>::verifier_first_round(
            index_pvk.domain_h_size,
            index_pvk.domain_k_size,
            &mut sponge_var,
            &proof.commitments[0],
            &proof.prover_messages[0].field_elements,
        )?;

        let (_, verifier_state) = AHPForR1CS::<F, CF, S, SVN, PC, PCG>::verifier_second_round(
            verifier_state,
            &mut sponge_var,
            &proof.commitments[1],
            &proof.prover_messages[1].field_elements,
        )?;

        let verifier_state = AHPForR1CS::<F, CF, S, SVN, PC, PCG>::verifier_third_round(
            verifier_state,
            &mut sponge_var,
            &proof.commitments[2],
            &proof.prover_messages[2].field_elements,
        )?;

        let mut formatted_public_input = vec![NonNativeFieldVar::one()];
        for elem in public_input.iter().cloned() {
            formatted_public_input.push(elem);
        }

        let lc = AHPForR1CS::<F, CF, S, SVN, PC, PCG>::verifier_decision(
            ns!(cs, "ahp").cs(),
            &formatted_public_input,
            &proof.evaluations,
            verifier_state.clone(),
            &index_pvk.domain_k_size_gadget,
        )?;

        let (num_opening_challenges, _num_batching_rands, comm, query_set, evaluations) =
            AHPForR1CS::<F, CF, S, SVN, PC, PCG>::verifier_comm_query_eval_set(
                &index_pvk,
                &proof,
                &verifier_state,
            )?;

        let mut evaluations_labels = Vec::<(String, NonNativeFieldVar<F, CF>)>::new();
        for q in query_set.0.iter().cloned() {
            evaluations_labels.push((q.0.clone(), (q.1).value.clone()));
        }
        evaluations_labels.sort_by(|a, b| a.0.cmp(&b.0));

        let mut evals_vec: Vec<NonNativeFieldVar<F, CF>> = Vec::new();
        for (label, point) in evaluations_labels.iter() {
            if label != "outer_sumcheck" && label != "inner_sumcheck" {
                evals_vec.push(evaluations.get_lc_eval(label, point).unwrap());
            }
        }

        sponge_var.absorb_nonnative(&evals_vec)?;

        let (opening_challenges, opening_challenges_bits) =
            sponge_var.squeeze_nonnative_field_elements(num_opening_challenges)?;

        let (batching_rands, batching_rands_bits) =
            sponge_var.squeeze_nonnative_field_elements(num_opening_challenges)?;

        eprintln!("before PC checks: constraints: {}", cs.num_constraints());

        let rand_data = PCCheckRandomDataVar::<F, CF> {
            opening_challenges: opening_challenges,
            opening_challenges_bits: opening_challenges_bits,
            batching_rands: batching_rands,
            batching_rands_bits: batching_rands_bits,
        };

        Ok(PCG::prepared_check_combinations(
            ns!(cs, "pc_check").cs(),
            &index_pvk.prepared_verifier_key,
            &lc,
            &comm,
            &query_set,
            &evaluations,
            &proof.pc_batch_proof,
            &rand_data,
        )?)
    }

    #[tracing::instrument(target = "r1cs", skip(index_vk, proof))]
    pub fn verify<SVN: CryptographicSpongeVarNonNative<F, CF, S>>(
        index_vk: &IndexVerifierKeyVar<F, CF, S, PC, PCG>,
        public_input: &[NonNativeFieldVar<F, CF>],
        proof: &ProofVar<F, CF, S, PC, PCG>,
    ) -> Result<Boolean<CF>, Error<PC::Error>> {
        let index_pvk = PreparedIndexVerifierKeyVar::<F, CF, S, SVN, PC, PCG>::prepare(&index_vk)?;
        Self::prepared_verify(&index_pvk, public_input, proof)
    }
}
