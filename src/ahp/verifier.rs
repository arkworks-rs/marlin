#![allow(non_snake_case)]

use crate::ahp::constraint_systems::ProverConstraintSystem;
use crate::ahp::indexer::IndexInfo;
use crate::ahp::prover::*;
use crate::ahp::*;
use r1cs_core::ConstraintSynthesizer;
use rand_core::RngCore;

use algebra_core::PrimeField;
use ff_fft::EvaluationDomain;
use poly_commit::{Evaluations, QuerySet};

/// State of the AHP verifier
pub struct VerifierState<F: PrimeField, C> {
    index_info: IndexInfo<F, C>,
    domain_h: EvaluationDomain<F>,
    domain_k: EvaluationDomain<F>,

    first_round_msg: Option<VerifierFirstMsg<F>>,
    second_round_msg: Option<VerifierSecondMsg<F>>,
    third_round_msg: Option<VerifierThirdMsg<F>>,

    beta_3: Option<F>,
}

/// First message of the verifier.
#[derive(Copy, Clone)]
pub struct VerifierFirstMsg<F> {
    /// Query for the random polynomial.
    pub alpha: F,
    /// Randomizer for the lincheck for `A`.
    pub eta_a: F,
    /// Randomizer for the lincheck for `B`.
    pub eta_b: F,
    /// Randomizer for the lincheck for `C`.
    pub eta_c: F,
}

/// Second verifier message.
#[derive(Copy, Clone)]
pub struct VerifierSecondMsg<F> {
    /// Query for the first and second round of polynomials.
    pub beta_1: F,
}

/// Third verifier message.
#[derive(Copy, Clone)]
pub struct VerifierThirdMsg<F> {
    /// Query for the third round of polynomials.
    pub beta_2: F,
}

impl<F: PrimeField> AHPForR1CS<F> {
    /// Output the first message and next round state.
    pub fn verifier_first_round<R: RngCore, C: ConstraintSynthesizer<F>>(
        index_info: IndexInfo<F, C>,
        rng: &mut R,
    ) -> Result<(VerifierFirstMsg<F>, VerifierState<F, C>), Error> {
        if index_info.num_constraints != index_info.num_variables {
            return Err(Error::NonSquareMatrix);
        }

        let domain_h =
            EvaluationDomain::new(index_info.num_constraints).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_k =
            EvaluationDomain::new(index_info.num_non_zero).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let alpha = F::rand(rng);
        let eta_a = F::rand(rng);
        let eta_b = F::rand(rng);
        let eta_c = F::rand(rng);

        let msg = VerifierFirstMsg {
            alpha,
            eta_a,
            eta_b,
            eta_c,
        };

        let new_state = VerifierState {
            index_info,
            domain_h,
            domain_k,
            first_round_msg: Some(msg),
            second_round_msg: None,
            third_round_msg: None,
            beta_3: None,
        };

        Ok((msg, new_state))
    }

    /// Output the second message and next round state.
    pub fn verifier_second_round<R: RngCore, C: ConstraintSynthesizer<F>>(
        state: VerifierState<F, C>,
        rng: &mut R,
    ) -> (VerifierSecondMsg<F>, VerifierState<F, C>) {
        let VerifierState {
            index_info,
            domain_h,
            domain_k,
            first_round_msg,
            ..
        } = state;

        let beta_1 = domain_h.sample_element_outside_domain(rng);

        let msg = VerifierSecondMsg { beta_1 };

        let new_state = VerifierState {
            index_info,
            domain_h,
            domain_k,
            first_round_msg: first_round_msg,
            second_round_msg: Some(msg),
            third_round_msg: None,
            beta_3: None,
        };

        (msg, new_state)
    }

    /// Output the third message and next round state.
    pub fn verifier_third_round<R: RngCore, C: ConstraintSynthesizer<F>>(
        state: VerifierState<F, C>,
        rng: &mut R,
    ) -> (VerifierThirdMsg<F>, VerifierState<F, C>) {
        let VerifierState {
            index_info,
            domain_h,
            domain_k,
            first_round_msg,
            second_round_msg,
            ..
        } = state;

        let beta_2 = domain_h.sample_element_outside_domain(rng);

        let msg = VerifierThirdMsg { beta_2 };

        let new_state = VerifierState {
            index_info,
            domain_h,
            domain_k,
            first_round_msg: first_round_msg,
            second_round_msg: second_round_msg,
            third_round_msg: Some(msg),
            beta_3: None,
        };

        (msg, new_state)
    }

    /// Output the fourth message and next round state.
    pub fn verifier_fourth_round<R: RngCore, C: ConstraintSynthesizer<F>>(
        state: VerifierState<F, C>,
        rng: &mut R,
    ) -> VerifierState<F, C> {
        let VerifierState {
            index_info,
            domain_h,
            domain_k,
            first_round_msg,
            second_round_msg,
            third_round_msg,
            ..
        } = state;

        let beta_3 = F::rand(rng);

        let new_state = VerifierState {
            index_info,
            domain_h,
            domain_k,
            first_round_msg: first_round_msg,
            second_round_msg: second_round_msg,
            third_round_msg: third_round_msg,
            beta_3: Some(beta_3),
        };

        new_state
    }

    /// Output the query state and next round state.
    pub fn verifier_query_set<'a, 'b, R: RngCore, C: ConstraintSynthesizer<F>>(
        state: VerifierState<F, C>,
        _: &'a mut R,
    ) -> (QuerySet<'b, F>, VerifierState<F, C>) {
        let VerifierState {
            index_info,
            domain_h,
            domain_k,
            first_round_msg,
            second_round_msg,
            third_round_msg,
            beta_3,
            ..
        } = state;

        let first_round_msg =
            first_round_msg.expect("VerifierState should include first_round_msg when verifier_query_set is called");
        let second_round_msg =
            second_round_msg.expect("VerifierState should include second_round_msg when verifier_query_set is called");
        let third_round_msg =
            third_round_msg.expect("VerifierState should include third_round_msg when verifier_query_set is called");

        let beta_1 = second_round_msg.beta_1;
        let beta_2 = third_round_msg.beta_2;

        let beta_3 = beta_3.expect("VerifierState should include beta_3 when verifier_query_set is called");

        let mut query_set = QuerySet::new();
        query_set.insert(("a_row", beta_3));
        query_set.insert(("a_col", beta_3));
        query_set.insert(("a_val", beta_3));
        query_set.insert(("b_row", beta_3));
        query_set.insert(("b_col", beta_3));
        query_set.insert(("b_val", beta_3));
        query_set.insert(("c_row", beta_3));
        query_set.insert(("c_col", beta_3));
        query_set.insert(("c_val", beta_3));

        query_set.insert(("w", beta_1));
        query_set.insert(("z_a", beta_1));
        query_set.insert(("z_b", beta_1));
        query_set.insert(("mask_poly", beta_1));
        query_set.insert(("g_1", beta_1));
        query_set.insert(("h_1", beta_1));

        query_set.insert(("g_2", beta_2));
        query_set.insert(("h_2", beta_2));

        query_set.insert(("g_3", beta_3));
        query_set.insert(("h_3", beta_3));

        let state = VerifierState {
            index_info,
            domain_h,
            domain_k,
            first_round_msg: Some(first_round_msg),
            second_round_msg: Some(second_round_msg),
            third_round_msg: Some(third_round_msg),
            beta_3: Some(beta_3),
        };
        (query_set, state)
    }

    /// Decide whether or not to accept given the queries and their evaluations.
    /// Assumes that `public input` only contains the actual public input, and
    /// is hence one less than a power of two.
    pub fn verifier_decision<C: ConstraintSynthesizer<F>>(
        public_input: &[F],
        evals: &Evaluations<F>,
        prover_messages: &[ProverMsg<F>],
        state: VerifierState<F, C>,
    ) -> Result<bool, Error> {
        let decision_time = start_timer!(|| "AHP::Verifier::Decision");

        let public_input = ProverConstraintSystem::format_public_input(public_input);
        if !Self::formatted_public_input_is_admissible(&public_input) {
            Err(Error::InvalidPublicInputLength)?
        }

        let VerifierState {
            domain_h,
            domain_k,
            first_round_msg,
            second_round_msg,
            third_round_msg,
            beta_3,
            ..
        } = state;

        let first_round_msg =
            first_round_msg.expect("VerifierState should include first_round_msg when verifier_decision is called");
        let second_round_msg =
            second_round_msg.expect("VerifierState should include second_round_msg when verifier_decision is called");
        let third_round_msg =
            third_round_msg.expect("VerifierState should include third_round_msg when verifier_decision is called");

        let VerifierFirstMsg {
            alpha,
            eta_a,
            eta_b,
            eta_c,
        } = first_round_msg;
        let beta_1 = second_round_msg.beta_1;
        let beta_2 = third_round_msg.beta_2;

        let beta_3 = beta_3.expect("VerifierState should include beta_3 when verifier_decision is called");

        let sigma_2 = prover_messages[2].field_elements[0];
        let sigma_3 = prover_messages[3].field_elements[0];

        let h_size = domain_h.size_as_field_element;
        let k_size = domain_k.size_as_field_element;

        let a_row_at_beta_3 = *evals.get(&("a_row", beta_3)).ok_or(Error::MissingEval("a_row"))?;
        let a_col_at_beta_3 = *evals.get(&("a_col", beta_3)).ok_or(Error::MissingEval("a_col"))?;
        let a_val_at_beta_3 = *evals.get(&("a_val", beta_3)).ok_or(Error::MissingEval("a_val"))?;
        let b_row_at_beta_3 = *evals.get(&("b_row", beta_3)).ok_or(Error::MissingEval("b_row"))?;
        let b_col_at_beta_3 = *evals.get(&("b_col", beta_3)).ok_or(Error::MissingEval("b_col"))?;
        let b_val_at_beta_3 = *evals.get(&("b_val", beta_3)).ok_or(Error::MissingEval("b_val"))?;
        let c_row_at_beta_3 = *evals.get(&("c_row", beta_3)).ok_or(Error::MissingEval("c_row"))?;
        let c_col_at_beta_3 = *evals.get(&("c_col", beta_3)).ok_or(Error::MissingEval("c_col"))?;
        let c_val_at_beta_3 = *evals.get(&("c_val", beta_3)).ok_or(Error::MissingEval("c_val"))?;

        let inner_sumcheck_time = start_timer!(|| "Checking inner sumcheck");
        // Inner sumcheck test:
        // h_3(beta_3) v_K(beta_3) = a(beta_3) - b(beta_3) (beta_3 g_3(beta_3) + sigma_3/|K|)
        let h_3_at_beta_3 = *evals.get(&("h_3", beta_3)).ok_or(Error::MissingEval("h_3"))?;
        let g_3_at_beta_3 = *evals.get(&("g_3", beta_3)).ok_or(Error::MissingEval("g_3"))?;
        let v_K_at_beta_3 = domain_k.evaluate_vanishing_polynomial(beta_3);

        let v_H_at_beta_1 = domain_h.evaluate_vanishing_polynomial(beta_1);
        let v_H_at_beta_2 = domain_h.evaluate_vanishing_polynomial(beta_2);
        let a_at_beta_3 =
            eta_a * &v_H_at_beta_2 * &v_H_at_beta_1 * &a_val_at_beta_3
                  * &(beta_2 - &b_row_at_beta_3) * &(beta_1 - &b_col_at_beta_3)
                  * &(beta_2 - &c_row_at_beta_3) * &(beta_1 - &c_col_at_beta_3)
          + &(eta_b * &v_H_at_beta_2 * &v_H_at_beta_1 * &b_val_at_beta_3
                    * &(beta_2 - &a_row_at_beta_3) * &(beta_1 - &a_col_at_beta_3)
                    * &(beta_2 - &c_row_at_beta_3) * &(beta_1 - &c_col_at_beta_3))
          + &(eta_c * &v_H_at_beta_2 * &v_H_at_beta_1 * &c_val_at_beta_3
                    * &(beta_2 - &a_row_at_beta_3) * &(beta_1 - &a_col_at_beta_3)
                    * &(beta_2 - &b_row_at_beta_3) * &(beta_1 - &b_col_at_beta_3));
        let b_at_beta_3 =
             (beta_2 - &a_row_at_beta_3) * &(beta_1 - &a_col_at_beta_3)
          * &(beta_2 - &b_row_at_beta_3) * &(beta_1 - &b_col_at_beta_3)
          * &(beta_2 - &c_row_at_beta_3) * &(beta_1 - &c_col_at_beta_3);

        let lhs = h_3_at_beta_3 * &v_K_at_beta_3;
        let rhs = a_at_beta_3 - &(b_at_beta_3 * &(beta_3 * &g_3_at_beta_3 + &(sigma_3 / &k_size)));
        end_timer!(inner_sumcheck_time);
        if lhs != rhs {
            eprintln!("Inner sumcheck test failed");
            end_timer!(decision_time);
            return Ok(false);
        }

        let middle_sumcheck_time = start_timer!(|| "Checking middle sumcheck");
        // Middle sumcheck test:
        // r(alpha, beta_2) sigma_3 = h_2(beta_2) v_H(beta_2) + beta_2 g_2(beta_2) + sigma_2/|H|
        let r_alpha_at_beta_2 = domain_h.eval_unnormalized_bivariate_lagrange_poly(alpha, beta_2);
        let g_2_at_beta_2 = *evals.get(&("g_2", beta_2)).ok_or(Error::MissingEval("g_2"))?;
        let h_2_at_beta_2 = *evals.get(&("h_2", beta_2)).ok_or(Error::MissingEval("h_2"))?;

        let lhs = r_alpha_at_beta_2 * &sigma_3;
        let rhs = h_2_at_beta_2 * &v_H_at_beta_2 + &(beta_2 * &g_2_at_beta_2 + &(sigma_2 / &h_size));
        end_timer!(middle_sumcheck_time);
        if lhs != rhs {
            eprintln!("Middle sumcheck test failed");
            end_timer!(decision_time);
            return Ok(false);
        }

        let outer_sumcheck_time = start_timer!(|| "Checking middle sumcheck");
        // Outer sumcheck test:
        //   s(beta_1) + r(alpha, beta_1) (sum_M eta_M z_M(beta_1)) - sigma_2 z(beta_1)
        // = h_1(beta_1) v_H(beta_1) + beta_1 g_1(beta_1)
        let mask_poly_at_beta_1 = *evals.get(&("mask_poly", beta_1)).ok_or(Error::MissingEval("mask_poly"))?;
        let r_alpha_at_beta_1 = domain_h.eval_unnormalized_bivariate_lagrange_poly(alpha, beta_1);

        let z_a_at_beta_1 = *evals.get(&("z_a", beta_1)).ok_or(Error::MissingEval("z_a"))?;
        let z_b_at_beta_1 = *evals.get(&("z_b", beta_1)).ok_or(Error::MissingEval("z_b"))?;
        let z_c_at_beta_1 = z_a_at_beta_1 * &z_b_at_beta_1;
        let sum_of_z_m = eta_a * &z_a_at_beta_1 + &(eta_b * &z_b_at_beta_1) + &(eta_c * &z_c_at_beta_1);

        let x_domain = EvaluationDomain::new(public_input.len())
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)
            .unwrap();
        let x_poly_at_beta_1 = x_domain
            .evaluate_all_lagrange_coefficients(beta_1)
            .into_iter()
            .zip(public_input)
            .map(|(l, x)| l * &x)
            .fold(F::zero(), |x, y| x + &y);
        let w_at_beta_1 = *evals.get(&("w", beta_1)).ok_or(Error::MissingEval("w"))?;
        let z_at_beta_1 = w_at_beta_1 * &x_domain.evaluate_vanishing_polynomial(beta_1) + &x_poly_at_beta_1;

        let g_1_at_beta_1 = *evals.get(&("g_1", beta_1)).ok_or(Error::MissingEval("g_1"))?;
        let h_1_at_beta_1 = *evals.get(&("h_1", beta_1)).ok_or(Error::MissingEval("h_1"))?;

        let lhs = mask_poly_at_beta_1 + &(r_alpha_at_beta_1 * &sum_of_z_m) - &(sigma_2 * &z_at_beta_1);
        let rhs = h_1_at_beta_1 * &v_H_at_beta_1 + &(beta_1 * &g_1_at_beta_1);

        end_timer!(outer_sumcheck_time);
        if lhs != rhs {
            eprintln!("Outer sumcheck test failed");
            end_timer!(decision_time);
            return Ok(false);
        }

        end_timer!(decision_time);
        Ok(true)
    }
}
