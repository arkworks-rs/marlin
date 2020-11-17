use crate::{
    ahp::Error,
    constraints::{
        data_structures::{PreparedIndexVerifierKeyVar, ProofVar},
        lagrange_interpolation::LagrangeInterpolationVar,
        polynomial::AlgebraForAHP,
    },
    fiat_shamir::{constraints::FiatShamirRngVar, FiatShamirRng},
    PhantomData, PrimeField, String, ToString, Vec,
};
use ark_nonnative_field::NonNativeFieldVar;
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::{
    EvaluationsVar, LCTerm, LinearCombinationVar, PCCheckVar, PolynomialCommitment, PrepareVar,
    QuerySetVar,
};
use ark_r1cs_std::{
    alloc::AllocVar,
    bits::boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    ToBitsGadget, ToConstraintFieldGadget,
};
use ark_relations::r1cs::ConstraintSystemRef;
use hashbrown::{HashMap, HashSet};

#[derive(Clone)]
pub struct VerifierStateVar<TargetField: PrimeField, BaseField: PrimeField> {
    domain_h_size: u64,
    domain_k_size: u64,

    first_round_msg: Option<VerifierFirstMsgVar<TargetField, BaseField>>,
    second_round_msg: Option<VerifierSecondMsgVar<TargetField, BaseField>>,

    gamma: Option<NonNativeFieldVar<TargetField, BaseField>>,
}

#[derive(Clone)]
pub struct VerifierFirstMsgVar<TargetField: PrimeField, BaseField: PrimeField> {
    pub alpha: NonNativeFieldVar<TargetField, BaseField>,
    pub eta_a: NonNativeFieldVar<TargetField, BaseField>,
    pub eta_b: NonNativeFieldVar<TargetField, BaseField>,
    pub eta_c: NonNativeFieldVar<TargetField, BaseField>,
}

#[derive(Clone)]
pub struct VerifierSecondMsgVar<TargetField: PrimeField, BaseField: PrimeField> {
    pub beta: NonNativeFieldVar<TargetField, BaseField>,
}

#[derive(Clone)]
pub struct VerifierThirdMsgVar<TargetField: PrimeField, BaseField: PrimeField> {
    pub gamma: NonNativeFieldVar<TargetField, BaseField>,
}

pub struct AHPForR1CS<
    F: PrimeField,
    CF: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF>,
> where
    PCG::VerifierKeyVar: ToConstraintFieldGadget<CF>,
    PCG::CommitmentVar: ToConstraintFieldGadget<CF>,
{
    field: PhantomData<F>,
    constraint_field: PhantomData<CF>,
    polynomial_commitment: PhantomData<PC>,
    pc_check: PhantomData<PCG>,
}

impl<
        F: PrimeField,
        CF: PrimeField,
        PC: PolynomialCommitment<F, DensePolynomial<F>>,
        PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF>,
    > AHPForR1CS<F, CF, PC, PCG>
where
    PCG::VerifierKeyVar: ToConstraintFieldGadget<CF>,
    PCG::CommitmentVar: ToConstraintFieldGadget<CF>,
{
    /// Output the first message and next round state.
    #[tracing::instrument(target = "r1cs", skip(fs_rng, comms))]
    #[allow(clippy::type_complexity)]
    pub fn verifier_first_round<
        CommitmentVar: ToConstraintFieldGadget<CF>,
        PR: FiatShamirRng<F, CF>,
        R: FiatShamirRngVar<F, CF, PR>,
    >(
        domain_h_size: u64,
        domain_k_size: u64,
        fs_rng: &mut R,
        comms: &[CommitmentVar],
        message: &[NonNativeFieldVar<F, CF>],
    ) -> Result<(VerifierFirstMsgVar<F, CF>, VerifierStateVar<F, CF>), Error> {
        // absorb the first commitments and messages
        {
            let mut elems = Vec::<FpVar<CF>>::new();
            comms.iter().for_each(|comm| {
                elems.append(&mut comm.to_constraint_field().unwrap());
            });
            fs_rng.absorb_native_field_elements(&elems)?;
            fs_rng.absorb_nonnative_field_elements(&message)?;
        }

        // obtain four elements from the sponge
        let elems = fs_rng.squeeze_field_elements(4)?;
        let alpha = elems[0].clone();
        let eta_a = elems[1].clone();
        let eta_b = elems[2].clone();
        let eta_c = elems[3].clone();

        let msg = VerifierFirstMsgVar {
            alpha,
            eta_a,
            eta_b,
            eta_c,
        };

        let new_state = VerifierStateVar {
            domain_h_size,
            domain_k_size,
            first_round_msg: Some(msg.clone()),
            second_round_msg: None,
            gamma: None,
        };

        Ok((msg, new_state))
    }

    #[tracing::instrument(target = "r1cs", skip(state, fs_rng, comms))]
    #[allow(clippy::type_complexity)]
    pub fn verifier_second_round<
        CommitmentVar: ToConstraintFieldGadget<CF>,
        PR: FiatShamirRng<F, CF>,
        R: FiatShamirRngVar<F, CF, PR>,
    >(
        state: VerifierStateVar<F, CF>,
        fs_rng: &mut R,
        comms: &[CommitmentVar],
        message: &[NonNativeFieldVar<F, CF>],
    ) -> Result<(VerifierSecondMsgVar<F, CF>, VerifierStateVar<F, CF>), Error> {
        let VerifierStateVar {
            domain_h_size,
            domain_k_size,
            first_round_msg,
            ..
        } = state;

        // absorb the second commitments and messages
        {
            let mut elems = Vec::<FpVar<CF>>::new();
            comms.iter().for_each(|comm| {
                elems.append(&mut comm.to_constraint_field().unwrap());
            });
            fs_rng.absorb_native_field_elements(&elems)?;
            fs_rng.absorb_nonnative_field_elements(&message)?;
        }

        // obtain one element from the sponge
        let elems = fs_rng.squeeze_field_elements(1)?;
        let beta = elems[0].clone();

        let msg = VerifierSecondMsgVar { beta };

        let new_state = VerifierStateVar {
            domain_h_size,
            domain_k_size,
            first_round_msg,
            second_round_msg: Some(msg.clone()),
            gamma: None,
        };

        Ok((msg, new_state))
    }

    #[tracing::instrument(target = "r1cs", skip(state, fs_rng, comms))]
    pub fn verifier_third_round<
        CommitmentVar: ToConstraintFieldGadget<CF>,
        PR: FiatShamirRng<F, CF>,
        R: FiatShamirRngVar<F, CF, PR>,
    >(
        state: VerifierStateVar<F, CF>,
        fs_rng: &mut R,
        comms: &[CommitmentVar],
        message: &[NonNativeFieldVar<F, CF>],
    ) -> Result<VerifierStateVar<F, CF>, Error> {
        let VerifierStateVar {
            domain_h_size,
            domain_k_size,
            first_round_msg,
            second_round_msg,
            ..
        } = state;

        // absorb the third commitments and messages
        {
            let mut elems = Vec::<FpVar<CF>>::new();
            comms.iter().for_each(|comm| {
                elems.append(&mut comm.to_constraint_field().unwrap());
            });
            fs_rng.absorb_native_field_elements(&elems)?;
            fs_rng.absorb_nonnative_field_elements(&message)?;
        }

        // obtain one element from the sponge
        let elems = fs_rng.squeeze_field_elements(1)?;
        let gamma = elems[0].clone();

        let new_state = VerifierStateVar {
            domain_h_size,
            domain_k_size,
            first_round_msg,
            second_round_msg,
            gamma: Some(gamma),
        };

        Ok(new_state)
    }

    #[tracing::instrument(target = "r1cs", skip(state))]
    pub fn verifier_decision(
        cs: ConstraintSystemRef<CF>,
        public_input: &[NonNativeFieldVar<F, CF>],
        evals: &HashMap<String, NonNativeFieldVar<F, CF>>,
        state: VerifierStateVar<F, CF>,
        domain_k_size_in_vk: &FpVar<CF>,
    ) -> Result<Vec<LinearCombinationVar<F, CF>>, Error> {
        let VerifierStateVar {
            domain_k_size,
            first_round_msg,
            second_round_msg,
            gamma,
            ..
        } = state;

        let first_round_msg = first_round_msg.expect(
            "VerifierState should include first_round_msg when verifier_decision is called",
        );
        let second_round_msg = second_round_msg.expect(
            "VerifierState should include second_round_msg when verifier_decision is called",
        );

        let zero = NonNativeFieldVar::<F, CF>::zero();

        let VerifierFirstMsgVar {
            alpha,
            eta_a,
            eta_b,
            eta_c,
        } = first_round_msg;
        let beta: NonNativeFieldVar<F, CF> = second_round_msg.beta;

        let v_h_at_alpha = evals
            .get("vanishing_poly_h_alpha")
            .ok_or_else(|| Error::MissingEval("vanishing_poly_h_alpha".to_string()))?;

        v_h_at_alpha.enforce_not_equal(&zero)?;

        let v_h_at_beta = evals
            .get("vanishing_poly_h_beta")
            .ok_or_else(|| Error::MissingEval("vanishing_poly_h_beta".to_string()))?;
        v_h_at_beta.enforce_not_equal(&zero)?;

        let gamma: NonNativeFieldVar<F, CF> =
            gamma.expect("VerifierState should include gamma when verifier_decision is called");

        let t_at_beta = evals
            .get("t")
            .ok_or_else(|| Error::MissingEval("t".to_string()))?;

        let v_k_at_gamma = evals
            .get("vanishing_poly_k_gamma")
            .ok_or_else(|| Error::MissingEval("vanishing_poly_k_gamma".to_string()))?;

        let r_alpha_at_beta = AlgebraForAHP::prepared_eval_bivariable_vanishing_polynomial(
            &alpha,
            &beta,
            &v_h_at_alpha,
            &v_h_at_beta,
        )?;

        let z_b_at_beta = evals
            .get("z_b")
            .ok_or_else(|| Error::MissingEval("z_b".to_string()))?;

        let x_padded_len = public_input.len().next_power_of_two() as u64;

        let mut interpolation_gadget = LagrangeInterpolationVar::<F, CF>::new(
            F::get_root_of_unity(x_padded_len as usize).unwrap(),
            x_padded_len,
            public_input,
        );

        let f_x_at_beta = interpolation_gadget.interpolate_constraints(&beta)?;

        let g_1_at_beta = evals
            .get("g_1")
            .ok_or_else(|| Error::MissingEval("g_1".to_string()))?;

        // Compute linear combinations
        let mut linear_combinations = Vec::new();

        // Only compute for linear combination optimization.
        let pow_x_at_beta = AlgebraForAHP::prepare(&beta, x_padded_len)?;
        let v_x_at_beta = AlgebraForAHP::prepared_eval_vanishing_polynomial(&pow_x_at_beta)?;

        // Outer sumcheck
        let z_b_lc_gadget = LinearCombinationVar::<F, CF> {
            label: "z_b".to_string(),
            terms: vec![(None, "z_b".into(), false)],
        };

        let g_1_lc_gadget = LinearCombinationVar::<F, CF> {
            label: "g_1".to_string(),
            terms: vec![(None, "g_1".into(), false)],
        };

        let t_lc_gadget = LinearCombinationVar::<F, CF> {
            label: "t".to_string(),
            terms: vec![(None, "t".into(), false)],
        };

        let eta_c_mul_z_b_at_beta = &eta_c * z_b_at_beta;
        let eta_a_add_above = &eta_a + &eta_c_mul_z_b_at_beta;

        let outer_sumcheck_lc_gadget = LinearCombinationVar::<F, CF> {
            label: "outer_sumcheck".to_string(),
            terms: vec![
                (None, "mask_poly".into(), false),
                (
                    Some(&r_alpha_at_beta * &eta_a_add_above),
                    "z_a".into(),
                    false,
                ),
                (
                    Some(&r_alpha_at_beta * &eta_b * z_b_at_beta),
                    LCTerm::One,
                    false,
                ),
                (Some(t_at_beta * &v_x_at_beta), "w".into(), true),
                (Some(t_at_beta * &f_x_at_beta), LCTerm::One, true),
                (Some(v_h_at_beta.clone()), "h_1".into(), true),
                (Some(&beta * g_1_at_beta), LCTerm::One, true),
            ],
        };

        linear_combinations.push(g_1_lc_gadget);
        linear_combinations.push(z_b_lc_gadget);
        linear_combinations.push(t_lc_gadget);
        linear_combinations.push(outer_sumcheck_lc_gadget);

        // Inner sumcheck
        let g_2_lc_gadget = LinearCombinationVar::<F, CF> {
            label: "g_2".to_string(),
            terms: vec![(None, "g_2".into(), false)],
        };

        let beta_alpha = &beta * &alpha;

        let a_denom_lc_gadget = LinearCombinationVar::<F, CF> {
            label: "a_denom".to_string(),
            terms: vec![
                (Some(beta_alpha.clone()), LCTerm::One, false),
                (Some(alpha.clone()), "a_row".into(), true),
                (Some(beta.clone()), "a_col".into(), true),
                (None, "a_row_col".into(), false),
            ],
        };

        let b_denom_lc_gadget = LinearCombinationVar::<F, CF> {
            label: "b_denom".to_string(),
            terms: vec![
                (Some(beta_alpha.clone()), LCTerm::One, false),
                (Some(alpha.clone()), "b_row".into(), true),
                (Some(beta.clone()), "b_col".into(), true),
                (None, "b_row_col".into(), false),
            ],
        };

        let c_denom_lc_gadget = LinearCombinationVar::<F, CF> {
            label: "c_denom".to_string(),
            terms: vec![
                (Some(beta_alpha), LCTerm::One, false),
                (Some(alpha), "c_row".into(), true),
                (Some(beta), "c_col".into(), true),
                (None, "c_row_col".into(), false),
            ],
        };

        let a_denom_at_gamma = evals.get(&a_denom_lc_gadget.label).unwrap();
        let b_denom_at_gamma = evals.get(&b_denom_lc_gadget.label).unwrap();
        let c_denom_at_gamma = evals.get(&c_denom_lc_gadget.label).unwrap();
        let g_2_at_gamma = evals.get(&g_2_lc_gadget.label).unwrap();

        let v_h_at_alpha_beta = v_h_at_alpha * v_h_at_beta;

        let domain_k_size_gadget =
            NonNativeFieldVar::<F, CF>::new_witness(ark_relations::ns!(cs, "domain_k"), || {
                Ok(F::from(domain_k_size as u128))
            })?;
        let inv_domain_k_size_gadget = domain_k_size_gadget.inverse()?;

        let domain_k_size_bit_decomposition = domain_k_size_gadget.to_bits_le()?;

        let domain_k_size_in_vk_bit_decomposition = domain_k_size_in_vk.to_bits_le()?;

        // This is not the most efficient implementation; an alternative is to check if the last limb of domain_k_size_gadget
        // can be bit composed by the bits in domain_k_size_in_vk, which would save a lot of constraints.
        // Nevertheless, doing so is using the nonnative field gadget in a non-black-box manner and is somehow not encouraged.
        for (left, right) in domain_k_size_bit_decomposition
            .iter()
            .take(32)
            .zip(domain_k_size_in_vk_bit_decomposition.iter())
        {
            left.enforce_equal(&right)?;
        }

        for bit in domain_k_size_bit_decomposition.iter().skip(32) {
            bit.enforce_equal(&Boolean::constant(false))?;
        }

        let b_expr_at_gamma_last_term =
            (gamma * g_2_at_gamma) + (t_at_beta * &inv_domain_k_size_gadget);
        let ab_denom_at_gamma = a_denom_at_gamma * b_denom_at_gamma;

        let inner_sumcheck_lc_gadget = LinearCombinationVar::<F, CF> {
            label: "inner_sumcheck".to_string(),
            terms: vec![
                (
                    Some(&eta_a * b_denom_at_gamma * c_denom_at_gamma * &v_h_at_alpha_beta),
                    "a_val".into(),
                    false,
                ),
                (
                    Some(&eta_b * a_denom_at_gamma * c_denom_at_gamma * &v_h_at_alpha_beta),
                    "b_val".into(),
                    false,
                ),
                (
                    Some(&eta_c * &ab_denom_at_gamma * &v_h_at_alpha_beta),
                    "c_val".into(),
                    false,
                ),
                (
                    Some(ab_denom_at_gamma * c_denom_at_gamma * &b_expr_at_gamma_last_term),
                    LCTerm::One,
                    true,
                ),
                (Some(v_k_at_gamma.clone()), "h_2".into(), true),
            ],
        };

        linear_combinations.push(g_2_lc_gadget);
        linear_combinations.push(a_denom_lc_gadget);
        linear_combinations.push(b_denom_lc_gadget);
        linear_combinations.push(c_denom_lc_gadget);
        linear_combinations.push(inner_sumcheck_lc_gadget);

        let vanishing_poly_h_alpha_lc_gadget = LinearCombinationVar::<F, CF> {
            label: "vanishing_poly_h_alpha".to_string(),
            terms: vec![(None, "vanishing_poly_h".into(), false)],
        };
        let vanishing_poly_h_beta_lc_gadget = LinearCombinationVar::<F, CF> {
            label: "vanishing_poly_h_beta".to_string(),
            terms: vec![(None, "vanishing_poly_h".into(), false)],
        };
        let vanishing_poly_k_gamma_lc_gadget = LinearCombinationVar::<F, CF> {
            label: "vanishing_poly_k_gamma".to_string(),
            terms: vec![(None, "vanishing_poly_k".into(), false)],
        };
        linear_combinations.push(vanishing_poly_h_alpha_lc_gadget);
        linear_combinations.push(vanishing_poly_h_beta_lc_gadget);
        linear_combinations.push(vanishing_poly_k_gamma_lc_gadget);

        linear_combinations.sort_by(|a, b| a.label.cmp(&b.label));

        Ok(linear_combinations)
    }

    #[tracing::instrument(target = "r1cs", skip(index_pvk, proof, state))]
    #[allow(clippy::type_complexity)]
    pub fn verifier_comm_query_eval_set<
        PR: FiatShamirRng<F, CF>,
        R: FiatShamirRngVar<F, CF, PR>,
    >(
        index_pvk: &PreparedIndexVerifierKeyVar<F, CF, PC, PCG, PR, R>,
        proof: &ProofVar<F, CF, PC, PCG>,
        state: &VerifierStateVar<F, CF>,
    ) -> Result<
        (
            usize,
            usize,
            Vec<PCG::PreparedLabeledCommitmentVar>,
            QuerySetVar<F, CF>,
            EvaluationsVar<F, CF>,
        ),
        Error,
    > {
        let VerifierStateVar {
            first_round_msg,
            second_round_msg,
            gamma,
            ..
        } = state;

        let first_round_msg = first_round_msg.as_ref().expect(
            "VerifierState should include first_round_msg when verifier_query_set is called",
        );

        let second_round_msg = second_round_msg.as_ref().expect(
            "VerifierState should include second_round_msg when verifier_query_set is called",
        );

        let alpha = first_round_msg.alpha.clone();

        let beta = second_round_msg.beta.clone();

        let gamma_ref = gamma
            .as_ref()
            .expect("VerifierState should include gamma when verifier_query_set is called")
            .clone();

        let gamma = gamma_ref;

        let mut query_set_gadget = QuerySetVar::<F, CF> { 0: HashSet::new() };

        query_set_gadget
            .0
            .insert(("g_1".to_string(), ("beta".to_string(), beta.clone())));
        query_set_gadget
            .0
            .insert(("z_b".to_string(), ("beta".to_string(), beta.clone())));
        query_set_gadget
            .0
            .insert(("t".to_string(), ("beta".to_string(), beta.clone())));
        query_set_gadget.0.insert((
            "outer_sumcheck".to_string(),
            ("beta".to_string(), beta.clone()),
        ));
        query_set_gadget
            .0
            .insert(("g_2".to_string(), ("gamma".to_string(), gamma.clone())));
        query_set_gadget
            .0
            .insert(("a_denom".to_string(), ("gamma".to_string(), gamma.clone())));
        query_set_gadget
            .0
            .insert(("b_denom".to_string(), ("gamma".to_string(), gamma.clone())));
        query_set_gadget
            .0
            .insert(("c_denom".to_string(), ("gamma".to_string(), gamma.clone())));
        query_set_gadget.0.insert((
            "inner_sumcheck".to_string(),
            ("gamma".to_string(), gamma.clone()),
        ));

        query_set_gadget.0.insert((
            "vanishing_poly_h_alpha".to_string(),
            ("alpha".to_string(), alpha.clone()),
        ));
        query_set_gadget.0.insert((
            "vanishing_poly_h_beta".to_string(),
            ("beta".to_string(), beta.clone()),
        ));
        query_set_gadget.0.insert((
            "vanishing_poly_k_gamma".to_string(),
            ("gamma".to_string(), gamma.clone()),
        ));

        let mut evaluations_gadget = EvaluationsVar::<F, CF> { 0: HashMap::new() };

        let zero = NonNativeFieldVar::<F, CF>::zero();

        evaluations_gadget.0.insert(
            ("g_1".to_string(), beta.clone()),
            (*proof.evaluations.get("g_1").unwrap()).clone(),
        );
        evaluations_gadget.0.insert(
            ("z_b".to_string(), beta.clone()),
            (*proof.evaluations.get("z_b").unwrap()).clone(),
        );
        evaluations_gadget.0.insert(
            ("t".to_string(), beta.clone()),
            (*proof.evaluations.get("t").unwrap()).clone(),
        );
        evaluations_gadget
            .0
            .insert(("outer_sumcheck".to_string(), beta.clone()), zero.clone());
        evaluations_gadget.0.insert(
            ("g_2".to_string(), gamma.clone()),
            (*proof.evaluations.get("g_2").unwrap()).clone(),
        );
        evaluations_gadget.0.insert(
            ("a_denom".to_string(), gamma.clone()),
            (*proof.evaluations.get("a_denom").unwrap()).clone(),
        );
        evaluations_gadget.0.insert(
            ("b_denom".to_string(), gamma.clone()),
            (*proof.evaluations.get("b_denom").unwrap()).clone(),
        );
        evaluations_gadget.0.insert(
            ("c_denom".to_string(), gamma.clone()),
            (*proof.evaluations.get("c_denom").unwrap()).clone(),
        );
        evaluations_gadget
            .0
            .insert(("inner_sumcheck".to_string(), gamma.clone()), zero);
        evaluations_gadget.0.insert(
            ("vanishing_poly_h_alpha".to_string(), alpha),
            (*proof.evaluations.get("vanishing_poly_h_alpha").unwrap()).clone(),
        );
        evaluations_gadget.0.insert(
            ("vanishing_poly_h_beta".to_string(), beta),
            (*proof.evaluations.get("vanishing_poly_h_beta").unwrap()).clone(),
        );
        evaluations_gadget.0.insert(
            ("vanishing_poly_k_gamma".to_string(), gamma),
            (*proof.evaluations.get("vanishing_poly_k_gamma").unwrap()).clone(),
        );

        let mut comms = vec![];

        const INDEX_LABELS: [&str; 14] = [
            "a_row",
            "a_col",
            "a_val",
            "a_row_col",
            "b_row",
            "b_col",
            "b_val",
            "b_row_col",
            "c_row",
            "c_col",
            "c_val",
            "c_row_col",
            "vanishing_poly_h",
            "vanishing_poly_k",
        ];

        // 14 comms for gamma from the index_vk
        for (comm, label) in index_pvk
            .prepared_index_comms
            .iter()
            .zip(INDEX_LABELS.iter())
        {
            comms.push(PCG::create_prepared_labeled_commitment_gadget(
                label.to_string(),
                comm.clone(),
                None,
            ));
        }

        // 4 comms for beta from the round 1
        const PROOF_1_LABELS: [&str; 4] = ["w", "z_a", "z_b", "mask_poly"];
        for (comm, label) in proof.commitments[0].iter().zip(PROOF_1_LABELS.iter()) {
            let prepared_comm = if label.eq(&"z_b") {
                PCG::PreparedCommitmentVar::prepare_small(comm)?
            } else {
                PCG::PreparedCommitmentVar::prepare(comm)?
            };
            comms.push(PCG::create_prepared_labeled_commitment_gadget(
                label.to_string(),
                prepared_comm,
                None,
            ));
        }

        let h_minus_2 = index_pvk.domain_h_size_gadget.clone() - CF::from(2u128);

        // 3 comms for beta from the round 2
        const PROOF_2_LABELS: [&str; 3] = ["t", "g_1", "h_1"];
        let proof_2_bounds = [None, Some(h_minus_2), None];
        for ((comm, label), bound) in proof.commitments[1]
            .iter()
            .zip(PROOF_2_LABELS.iter())
            .zip(proof_2_bounds.iter())
        {
            let prepared_comm = if label.eq(&"t") || label.eq(&"g_1") {
                PCG::PreparedCommitmentVar::prepare_small(comm)?
            } else {
                PCG::PreparedCommitmentVar::prepare(comm)?
            };
            comms.push(PCG::create_prepared_labeled_commitment_gadget(
                label.to_string(),
                prepared_comm,
                (*bound).clone(),
            ));
        }

        let k_minus_2 = &index_pvk.domain_k_size_gadget - CF::from(2u128);

        // 2 comms for gamma from the round 3
        const PROOF_3_LABELS: [&str; 2] = ["g_2", "h_2"];
        let proof_3_bounds = [Some(k_minus_2), None];
        for ((comm, label), bound) in proof.commitments[2]
            .iter()
            .zip(PROOF_3_LABELS.iter())
            .zip(proof_3_bounds.iter())
        {
            let prepared_comm = if label.eq(&"g_2") {
                PCG::PreparedCommitmentVar::prepare_small(comm)?
            } else {
                PCG::PreparedCommitmentVar::prepare(comm)?
            };
            comms.push(PCG::create_prepared_labeled_commitment_gadget(
                label.to_string(),
                prepared_comm,
                (*bound).clone(),
            ));
        }

        // For commitments; and combined commitments (degree bounds); and combined commitments again.
        let num_opening_challenges = 7;

        // Combined commitments.
        let num_batching_rands = 2;

        Ok((
            num_opening_challenges,
            num_batching_rands,
            comms,
            query_set_gadget,
            evaluations_gadget,
        ))
    }
}
