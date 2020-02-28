#![allow(non_snake_case)]

use crate::ahp::constraint_systems::ProverConstraintSystem;
use crate::ahp::indexer::*;
use crate::ahp::verifier::*;
use crate::ahp::*;

use algebra_core::{Field, PrimeField};
use ff_fft::{cfg_iter_mut, cfg_iter, cfg_into_iter, EvaluationDomain, Evaluations as EvaluationsOnDomain};
use poly_commit::{LabeledPolynomial, Polynomial};
use r1cs_core::{ConstraintSynthesizer, SynthesisError};
use rand_core::RngCore;
use crate::{Vec, BTreeMap, ToString};
use core::marker::PhantomData;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub(crate) struct MatrixEvals<'a, F: PrimeField> {
    a_row_evals: &'a EvaluationsOnDomain<F>,
    a_col_evals: &'a EvaluationsOnDomain<F>,
    a_val_evals: &'a EvaluationsOnDomain<F>,

    b_row_evals: &'a EvaluationsOnDomain<F>,
    b_col_evals: &'a EvaluationsOnDomain<F>,
    b_val_evals: &'a EvaluationsOnDomain<F>,

    c_row_evals: &'a EvaluationsOnDomain<F>,
    c_col_evals: &'a EvaluationsOnDomain<F>,
    c_val_evals: &'a EvaluationsOnDomain<F>,
}

/// State for the AHP prover.
pub struct ProverState<'a, 'b, F: PrimeField, C> {
    formatted_input_assignment: Vec<F>,
    witness_assignment: Vec<F>,
    /// Az
    z_a: Option<Vec<F>>,
    /// Bz
    z_b: Option<Vec<F>>,
    /// query bound b
    zk_bound: usize,

    w_poly: Option<LabeledPolynomial<'b, F>>,
    mz_polys: Option<(LabeledPolynomial<'b, F>, LabeledPolynomial<'b, F>)>,

    /// Evaluations on K of the row, col, and val polynomials for each M
    matrix_evals_on_K: MatrixEvals<'a, F>,

    /// Evaluations on B of the row, col, and val polynomials for each M
    matrix_evals_on_B: MatrixEvals<'a, F>,

    /// the random values sent by the verifier in the first round
    verifier_first_msg: Option<VerifierFirstMsg<F>>,

    /// the random values sent by the verifier in the second round
    verifier_second_msg: Option<VerifierSecondMsg<F>>,

    /// the blinding polynomial for the first round
    mask_poly: Option<LabeledPolynomial<'b, F>>,

    /// the polynomial r(alpha, X)
    r_alpha_poly: Option<Polynomial<F>>,

    /// domain H, sized for constraints
    domain_h: EvaluationDomain<F>,

    /// domain K, sized for matrix nonzero elements
    domain_k: EvaluationDomain<F>,

    #[doc(hidden)]
    _field: PhantomData<C>,
    _cs: PhantomData<C>,
}

impl<'a, 'b, F: PrimeField, C> ProverState<'a, 'b, F, C> {
    /// Get the public input.
    pub fn public_input(&self) -> Vec<F> {
        ProverConstraintSystem::unformat_public_input(&self.formatted_input_assignment)
    }
}

/// Each prover message that is not a list of oracles is a list of field elements.
#[repr(transparent)]
pub struct ProverMsg<F: Field> {
    /// The field elements that make up the message
    pub field_elements: Vec<F>,
}

impl<F: Field> algebra_core::ToBytes for ProverMsg<F> {
    fn write<W: algebra_core::io::Write>(&self, w: W) -> algebra_core::io::Result<()> {
        self.field_elements.write(w)
    }
}

/// The first set of prover oracles.
pub struct ProverFirstOracles<'b, F: Field> {
    /// The LDE of `w`.
    pub w: LabeledPolynomial<'b, F>,
    /// The LDE of `Az`.
    pub z_a: LabeledPolynomial<'b, F>,
    /// The LDE of `Bz`.
    pub z_b: LabeledPolynomial<'b, F>,
    /// The sum-check hiding polynomial.
    pub mask_poly: LabeledPolynomial<'b, F>,
}

impl<'b, F: Field> ProverFirstOracles<'b, F> {
    /// Iterate over the polynomials output by the prover in the first round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<'b, F>> {
        vec![&self.w, &self.z_a, &self.z_b, &self.mask_poly].into_iter()
    }
}

/// The second set of prover oracles.
pub struct ProverSecondOracles<'b, F: Field> {
    /// The polynomial `g` resulting from the first sumcheck.
    pub g_1: LabeledPolynomial<'b, F>,
    /// The polynomial `h` resulting from the first sumcheck.
    pub h_1: LabeledPolynomial<'b, F>,
}

impl<'b, F: Field> ProverSecondOracles<'b, F> {
    /// Iterate over the polynomials output by the prover in the second round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<'b, F>> {
        vec![&self.g_1, &self.h_1].into_iter()
    }
}

/// The third set of prover oracles.
pub struct ProverThirdOracles<'b, F: Field> {
    /// The polynomial `g` resulting from the second sumcheck.
    pub g_2: LabeledPolynomial<'b, F>,
    /// The polynomial `h` resulting from the second sumcheck.
    pub h_2: LabeledPolynomial<'b, F>,
}

impl<'b, F: Field> ProverThirdOracles<'b, F> {
    /// Iterate over the polynomials output by the prover in the third round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<'b, F>> {
        vec![&self.g_2, &self.h_2].into_iter()
    }
}

/// The fourth set of prover oracles.
pub struct ProverFourthOracles<'b, F: Field> {
    /// The polynomial `g` resulting from the third sumcheck.
    pub g_3: LabeledPolynomial<'b, F>,
    /// The polynomial `h` resulting from the third sumcheck.
    pub h_3: LabeledPolynomial<'b, F>,
}

impl<'b, F: Field> ProverFourthOracles<'b, F> {
    /// Iterate over the polynomials output by the prover in the fourth round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<'b, F>> {
        vec![&self.g_3, &self.h_3].into_iter()
    }
}

impl<F: PrimeField> AHPForR1CS<F> {
    /// Initialize the AHP prover.
    pub fn prover_init<'a, 'b, C: ConstraintSynthesizer<F>>(
        index: &'a Index<F, C>,
        c: C,
    ) -> Result<ProverState<'a, 'b, F, C>, Error> {
        let init_time = start_timer!(|| "AHP::Prover::Init");

        let constraint_time = start_timer!(|| "Generating constraints and witnesses");
        let mut pcs = ProverConstraintSystem::new();
        c.generate_constraints(&mut pcs)?;
        end_timer!(constraint_time);
        let padding_time = start_timer!(|| "Padding matrices to make them square");
        pcs.make_matrices_square();
        end_timer!(padding_time);

        let num_non_zero = index.index_info.num_non_zero;

        let ProverConstraintSystem {
            input_assignment: formatted_input_assignment,
            witness_assignment,
            num_constraints,
            ..
        } = pcs;

        let num_input_variables = formatted_input_assignment.len();
        let num_witness_variables = witness_assignment.len();
        if index.index_info.num_constraints != num_constraints
            || num_input_variables + num_witness_variables != index.index_info.num_variables
        {
            Err(Error::InstanceDoesNotMatchIndex)?;
        }

        if !Self::formatted_public_input_is_admissible(&formatted_input_assignment) {
            Err(Error::InvalidPublicInputLength)?
        }

        // Perform matrix multiplications
        let inner_prod_fn = |row: &[(F, usize)]| {
            let mut acc = F::zero();
            for &(ref coeff, i) in row {
                let tmp = if i < num_input_variables {
                    formatted_input_assignment[i]
                } else {
                    witness_assignment[i - num_input_variables]
                };

                acc += &(if coeff.is_one() { tmp } else { tmp * coeff });
            }
            acc
        };

        let eval_z_a_time = start_timer!(|| "Evaluating z_A");
        let z_a = index.a_matrix.iter().map(|row| inner_prod_fn(row)).collect();
        end_timer!(eval_z_a_time);

        let eval_z_b_time = start_timer!(|| "Evaluating z_B");
        let z_b = index.b_matrix.iter().map(|row| inner_prod_fn(row)).collect();
        end_timer!(eval_z_b_time);

        let zk_bound = 1; // One query is sufficient for our desired soundness

        let domain_h = EvaluationDomain::new(num_constraints).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_k = EvaluationDomain::new(num_non_zero).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let matrix_evals_on_K = MatrixEvals {
            a_row_evals: &index.a_row_evals_on_K,
            a_col_evals: &index.a_col_evals_on_K,
            a_val_evals: &index.a_val_evals_on_K,
            b_row_evals: &index.b_row_evals_on_K,
            b_col_evals: &index.b_col_evals_on_K,
            b_val_evals: &index.b_val_evals_on_K,
            c_row_evals: &index.c_row_evals_on_K,
            c_col_evals: &index.c_col_evals_on_K,
            c_val_evals: &index.c_val_evals_on_K,
        };

        let matrix_evals_on_B = MatrixEvals {
            a_row_evals: &index.a_row_evals_on_B,
            a_col_evals: &index.a_col_evals_on_B,
            a_val_evals: &index.a_val_evals_on_B,
            b_row_evals: &index.b_row_evals_on_B,
            b_col_evals: &index.b_col_evals_on_B,
            b_val_evals: &index.b_val_evals_on_B,
            c_row_evals: &index.c_row_evals_on_B,
            c_col_evals: &index.c_col_evals_on_B,
            c_val_evals: &index.c_val_evals_on_B,
        };
        end_timer!(init_time);

        Ok(ProverState {
            formatted_input_assignment,
            witness_assignment,
            z_a: Some(z_a),
            z_b: Some(z_b),
            w_poly: None,
            mz_polys: None,
            zk_bound,
            matrix_evals_on_K,
            matrix_evals_on_B,
            verifier_first_msg: None,
            verifier_second_msg: None,
            mask_poly: None,
            r_alpha_poly: None,
            domain_h,
            domain_k,
            _field: PhantomData,
            _cs: PhantomData,
        })
    }

    /// Output the first round message and the next state.
    pub fn prover_first_round<'a, 'b, R: RngCore, C: ConstraintSynthesizer<F>>(
        s: ProverState<'a, 'b, F, C>,
        rng: &mut R,
    ) -> Result<(ProverMsg<F>, ProverFirstOracles<'b, F>, ProverState<'a, 'b, F, C>), Error> {
        let round_time = start_timer!(|| "AHP::Prover::FirstRound");

        let ProverState {
            formatted_input_assignment,
            witness_assignment,
            z_a,
            z_b,
            zk_bound,
            matrix_evals_on_K,
            matrix_evals_on_B,
            domain_h,
            domain_k,
            ..
        } = s;

        let v_H = domain_h.vanishing_polynomial().into();

        let x_time = start_timer!(|| "Computing x polynomial and evals");
        let domain_x =
            EvaluationDomain::new(formatted_input_assignment.len()).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let x_poly =
            EvaluationsOnDomain::from_vec_and_domain(formatted_input_assignment.clone(), domain_x).interpolate();
        let x_evals = domain_h.fft(&x_poly);
        end_timer!(x_time);

        let ratio = domain_h.size() / domain_x.size();

        let mut w_extended = witness_assignment.clone();
        w_extended.extend(vec![
            F::zero();
            domain_h.size() - domain_x.size() - witness_assignment.len()
        ]);

        let w_poly_time = start_timer!(|| "Computing w polynomial");
        let w_poly_evals = cfg_into_iter!(0..domain_h.size())
            .map(|k| {
                if k % ratio == 0 {
                    F::zero()
                } else {
                    w_extended[k - (k / ratio) - 1] - &x_evals[k]
                }
            })
            .collect();

        let w_poly = EvaluationsOnDomain::from_vec_and_domain(w_poly_evals, domain_h).interpolate();
        let (w_poly, remainder) = w_poly.divide_by_vanishing_poly(domain_x).unwrap();
        assert!(remainder.is_zero());
        end_timer!(w_poly_time);

        let z_a_poly_time = start_timer!(|| "Computing z_A polynomial");
        let z_a_poly = &EvaluationsOnDomain::from_vec_and_domain(z_a.unwrap(), domain_h).interpolate()
            + &(&Polynomial::from_coefficients_slice(&[F::rand(rng)]) * &v_H);
        end_timer!(z_a_poly_time);

        let z_b_poly_time = start_timer!(|| "Computing z_B polynomial");
        let z_b_poly = &EvaluationsOnDomain::from_vec_and_domain(z_b.unwrap(), domain_h).interpolate()
            + &(&Polynomial::from_coefficients_slice(&[F::rand(rng)]) * &v_H);
        end_timer!(z_b_poly_time);

        let mask_poly_time = start_timer!(|| "Computing mask polynomial");
        let mask_poly_degree = 3 * domain_h.size() + 2 * zk_bound - 3;
        let mut mask_poly = Polynomial::rand(mask_poly_degree, rng);
        let scaled_sigma_1 = (mask_poly.divide_by_vanishing_poly(domain_h).unwrap().1)[0];
        mask_poly[0] -= &scaled_sigma_1;
        end_timer!(mask_poly_time);

        let msg = ProverMsg { field_elements: vec![] };

        assert!(w_poly.degree() <= domain_h.size() - domain_x.size() + zk_bound - 1);
        assert!(z_a_poly.degree() <= domain_h.size() + zk_bound - 1);
        assert!(z_b_poly.degree() <= domain_h.size() + zk_bound - 1);
        assert!(mask_poly.degree() <= 3 * domain_h.size() + 2 * zk_bound - 3);
        let w = LabeledPolynomial::new_owned("w".to_string(), w_poly, None, Some(1));
        let z_a = LabeledPolynomial::new_owned("z_a".to_string(), z_a_poly, None, Some(1));
        let z_b = LabeledPolynomial::new_owned("z_b".to_string(), z_b_poly, None, Some(1));
        let mask_poly = LabeledPolynomial::new_owned("mask_poly".to_string(), mask_poly.clone(), None, None);
        let oracles = ProverFirstOracles {
            w: w.clone(),
            z_a: z_a.clone(),
            z_b: z_b.clone(),
            mask_poly: mask_poly.clone(),
        };

        let state = ProverState {
            formatted_input_assignment,
            witness_assignment,
            z_a: None,
            z_b: None,
            w_poly: Some(w.clone()),
            mz_polys: Some((z_a, z_b)),
            zk_bound,
            matrix_evals_on_K,
            matrix_evals_on_B,
            verifier_first_msg: None,
            verifier_second_msg: None,
            mask_poly: Some(mask_poly),
            r_alpha_poly: None,
            domain_h,
            domain_k,
            _field: PhantomData,
            _cs: PhantomData,
        };
        end_timer!(round_time);

        Ok((msg, oracles, state))
    }

    /// Output the number of oracles sent by the prover in the first round.
    pub fn prover_num_first_round_oracles() -> usize {
        4
    }

    /// Output the degree bounds of oracles in the first round.
    pub fn prover_first_round_degree_bounds<C: ConstraintSynthesizer<F>>(
        _info: &IndexInfo<F, C>,
    ) -> impl Iterator<Item = Option<usize>> {
        vec![None; 4].into_iter()
    }

    /// Output the second round message and the next state.
    pub fn prover_second_round<'a, 'b, R: RngCore, C: ConstraintSynthesizer<F>>(
        ver_message: &VerifierFirstMsg<F>,
        prover_state: ProverState<'a, 'b, F, C>,
        _r: &mut R,
    ) -> (ProverMsg<F>, ProverSecondOracles<'b, F>, ProverState<'a, 'b, F, C>) {
        let round_time = start_timer!(|| "AHP::Prover::SecondRound");

        let ProverState {
            formatted_input_assignment,
            witness_assignment,
            z_a,
            z_b,
            w_poly,
            mz_polys,
            zk_bound,
            matrix_evals_on_K,
            matrix_evals_on_B,
            mask_poly,
            domain_h,
            domain_k,
            ..
        } = prover_state;

        let mask_poly = mask_poly.expect("ProverState should include mask_poly when prover_second_round is called");

        let VerifierFirstMsg {
            alpha,
            eta_a,
            eta_b,
            eta_c,
        } = *ver_message;

        let r_alpha_x_evals_time = start_timer!(|| "Compute r_alpha_x evals");
        let r_alpha_x_evals = domain_h.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(alpha);
        end_timer!(r_alpha_x_evals_time);

        let r_alpha_poly_time = start_timer!(|| "Compute r_alpha_x poly");
        let r_alpha_poly = Polynomial::from_coefficients_vec(domain_h.ifft(&r_alpha_x_evals));
        end_timer!(r_alpha_poly_time);

        let mut r_a_alpha_vals_on_H: BTreeMap<F, F> = BTreeMap::new();
        let mut r_b_alpha_vals_on_H: BTreeMap<F, F> = BTreeMap::new();
        let mut r_c_alpha_vals_on_H: BTreeMap<F, F> = BTreeMap::new();

        let r_alpha_pre_comp_time = start_timer!(|| "Compute r_alpha_x precomputation");
        let r_x_x_precomp: BTreeMap<_, _> = domain_h
            .elements()
            .zip(domain_h.batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs())
            .collect();
        let r_alpha_x_precomp: BTreeMap<_, _> = domain_h.elements().zip(r_alpha_x_evals).collect();
        end_timer!(r_alpha_pre_comp_time);

        let r_M_alpha_evals_time = start_timer!(|| "Compute r_M_alpha evals on H");
        for k in 0..prover_state.domain_k.size() {
            let a_row_at_kappa = matrix_evals_on_K.a_row_evals[k];
            let a_col_at_kappa = matrix_evals_on_K.a_col_evals[k];
            let to_add_a = r_x_x_precomp[&a_col_at_kappa]
                * &matrix_evals_on_K.a_val_evals[k]
                * &r_alpha_x_precomp[&a_row_at_kappa]
                * &r_x_x_precomp[&a_row_at_kappa];
            *r_a_alpha_vals_on_H.entry(a_col_at_kappa).or_insert(F::zero()) += &to_add_a;

            let b_row_at_kappa = matrix_evals_on_K.b_row_evals[k];
            let b_col_at_kappa = matrix_evals_on_K.b_col_evals[k];
            let to_add_b = r_x_x_precomp[&b_col_at_kappa]
                * &matrix_evals_on_K.b_val_evals[k]
                * &r_alpha_x_precomp[&b_row_at_kappa]
                * &r_x_x_precomp[&b_row_at_kappa];
            *r_b_alpha_vals_on_H.entry(b_col_at_kappa).or_insert(F::zero()) += &to_add_b;

            let c_row_at_kappa = matrix_evals_on_K.c_row_evals[k];
            let c_col_at_kappa = matrix_evals_on_K.c_col_evals[k];
            let to_add_c = r_x_x_precomp[&c_col_at_kappa]
                * &matrix_evals_on_K.c_val_evals[k]
                * &r_alpha_x_precomp[&c_row_at_kappa]
                * &r_x_x_precomp[&c_row_at_kappa];
            *r_c_alpha_vals_on_H.entry(c_col_at_kappa).or_insert(F::zero()) += &to_add_c;
        }
        end_timer!(r_M_alpha_evals_time);

        let summed_z_m_poly_time = start_timer!(|| "Compute z_m poly");
        let (z_a_poly, z_b_poly) = mz_polys.unwrap();
        let cz_poly = z_a_poly.polynomial() * z_b_poly.polynomial();

        let mut summed_z_m_coeffs = cz_poly.coeffs;
        cfg_iter_mut!(summed_z_m_coeffs).for_each(|c| *c *= &eta_c);
        cfg_iter_mut!(summed_z_m_coeffs)
            .zip(&z_a_poly.polynomial().coeffs)
            .zip(&z_b_poly.polynomial().coeffs)
            .for_each(|((c, a), b)| *c += &(eta_a * a + &(eta_b * b)));

        let summed_z_m = Polynomial::from_coefficients_vec(summed_z_m_coeffs);
        end_timer!(summed_z_m_poly_time);

        let summed_r_m_evals_time = start_timer!(|| "Compute r_m evals");
        let summed_r_m_evals = domain_h
            .elements()
            .map(|h_elem| {
                eta_a * r_a_alpha_vals_on_H.get(&h_elem).unwrap_or(&F::zero())
                    + &(eta_b * r_b_alpha_vals_on_H.get(&h_elem).unwrap_or(&F::zero()))
                    + &(eta_c * r_c_alpha_vals_on_H.get(&h_elem).unwrap_or(&F::zero()))
            })
            .collect::<Vec<_>>();
        end_timer!(summed_r_m_evals_time);

        let summed_r_m_poly_time = start_timer!(|| "Compute r_m poly");
        let summed_r_m = EvaluationsOnDomain::from_vec_and_domain(summed_r_m_evals, domain_h).interpolate();
        end_timer!(summed_r_m_poly_time);

        let z_poly_time = start_timer!(|| "Compute z poly");

        let domain_x = EvaluationDomain::new(formatted_input_assignment.len())
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)
            .unwrap();
        let x_poly =
            EvaluationsOnDomain::from_vec_and_domain(formatted_input_assignment.clone(), domain_x).interpolate();
        let w_poly = w_poly.unwrap();
        let mut z_poly = w_poly.polynomial().mul_by_vanishing_poly(domain_x);
        cfg_iter_mut!(z_poly.coeffs)
            .zip(&x_poly.coeffs)
            .for_each(|(z, x)| *z += x);
        assert!(z_poly.degree() <= domain_h.size() + zk_bound - 1);

        end_timer!(z_poly_time);

        let q_1_time = start_timer!(|| "Compute q_1 poly");

        let mul_domain_size = *[
            mask_poly.len(),
            r_alpha_poly.coeffs.len() + summed_z_m.coeffs.len(),
            summed_r_m.coeffs.len() + z_poly.len(),
        ]
        .iter()
        .max()
        .unwrap();
        let mul_domain =
            EvaluationDomain::new(mul_domain_size).expect("field is not smooth enough to construct domain");
        let mut r_alpha_evals = r_alpha_poly.evaluate_over_domain_by_ref(mul_domain);
        let summed_z_m_evals = summed_z_m.evaluate_over_domain_by_ref(mul_domain);
        let z_poly_evals = z_poly.evaluate_over_domain_by_ref(mul_domain);
        let summed_r_m_evals = summed_r_m.evaluate_over_domain_by_ref(mul_domain);

        cfg_iter_mut!(r_alpha_evals.evals)
            .zip(&summed_z_m_evals.evals)
            .zip(&z_poly_evals.evals)
            .zip(&summed_r_m_evals.evals)
            .for_each(|(((a, b), &c), d)| {
                *a *= b;
                *a -= &(c * d);
            });
        let rhs = r_alpha_evals.interpolate();
        let q_1 = mask_poly.polynomial() + &rhs;
        end_timer!(q_1_time);

        let sumcheck_time = start_timer!(|| "Compute sumcheck h and g polys");
        let (h_1, x_g_1) = q_1.divide_by_vanishing_poly(domain_h).unwrap();
        let g_1 = Polynomial::from_coefficients_slice(&x_g_1.coeffs[1..]);
        end_timer!(sumcheck_time);

        let msg = ProverMsg {
            field_elements: Vec::new(),
        };

        assert!(g_1.degree() <= domain_h.size() - 2);
        assert!(h_1.degree() <= 2 * domain_h.size() + 2 * zk_bound - 2);

        let oracles = ProverSecondOracles {
            g_1: LabeledPolynomial::new_owned("g_1".to_string(), g_1, Some(domain_h.size() - 2), Some(1)),
            h_1: LabeledPolynomial::new_owned("h_1".to_string(), h_1, None, None),
        };

        let state = ProverState {
            formatted_input_assignment,
            witness_assignment,
            z_a,
            z_b,
            w_poly: None,
            mz_polys: Some((z_a_poly, z_b_poly)),
            zk_bound,
            matrix_evals_on_K,
            matrix_evals_on_B,
            verifier_first_msg: Some(*ver_message),
            verifier_second_msg: None,
            mask_poly: Some(mask_poly),
            r_alpha_poly: Some(r_alpha_poly),
            domain_h,
            domain_k,
            _field: PhantomData,
            _cs: PhantomData,
        };
        end_timer!(round_time);

        (msg, oracles, state)
    }

    /// Output the number of oracles sent by the prover in the second round.
    pub fn prover_num_second_round_oracles() -> usize {
        2
    }

    /// Output the degree bounds of oracles in the second round.
    pub fn prover_second_round_degree_bounds<C: ConstraintSynthesizer<F>>(
        info: &IndexInfo<F, C>,
    ) -> impl Iterator<Item = Option<usize>> {
        let h_domain_size = EvaluationDomain::<F>::compute_size_of_domain(info.num_constraints).unwrap();

        vec![Some(h_domain_size - 2), None].into_iter()
    }

    /// Output the third round message and the next state.
    pub fn prover_third_round<'a, 'b, R: RngCore, C: ConstraintSynthesizer<F>>(
        ver_message: &VerifierSecondMsg<F>,
        prover_state: ProverState<'a, 'b, F, C>,
        _r: &mut R,
    ) -> (ProverMsg<F>, ProverThirdOracles<'b, F>, ProverState<'a, 'b, F, C>) {
        let round_time = start_timer!(|| "AHP::Prover::ThirdRound");

        let ProverState {
            formatted_input_assignment,
            witness_assignment,
            z_a,
            z_b,
            mz_polys,
            zk_bound,
            verifier_first_msg,
            mask_poly,
            r_alpha_poly,
            matrix_evals_on_K,
            matrix_evals_on_B,
            domain_h,
            domain_k,
            ..
        } = prover_state;

        let VerifierFirstMsg {
            eta_a,
            eta_b,
            eta_c,
            ..
        } = verifier_first_msg.expect("ProverState should be included in verifier_first_msg");

        let VerifierSecondMsg {
            beta_1
        } = *ver_message;

        let r_alpha_poly = r_alpha_poly.expect("ProverState should include r_alpha_poly when prover_third_round is called");

        let m_beta_1_evals_time = start_timer!(|| "Computing M_beta_1 evals");

        let mut a_beta_1_vals_on_H : BTreeMap<F, F> = BTreeMap::new();
        let mut b_beta_1_vals_on_H : BTreeMap<F, F> = BTreeMap::new();
        let mut c_beta_1_vals_on_H : BTreeMap<F, F> = BTreeMap::new();

        let r_x_x_precomp: BTreeMap<_, _> = domain_h.elements().zip(domain_h.batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs()).collect();
        let r_beta_1_x_precomp: BTreeMap<_, _> = domain_h.elements().zip(domain_h.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(beta_1)).collect();

        for k in 0..prover_state.domain_k.size() {
            // TODO: parallelize
            let a_col_at_kappa = matrix_evals_on_K.a_col_evals[k];
            let a_row_at_kappa = matrix_evals_on_K.a_row_evals[k];
            let to_add_a = r_x_x_precomp[&a_row_at_kappa] * &r_beta_1_x_precomp[&a_col_at_kappa] * &matrix_evals_on_K.a_val_evals[k];
            *a_beta_1_vals_on_H.entry(a_row_at_kappa).or_insert(F::zero()) += &to_add_a;

            let b_col_at_kappa = matrix_evals_on_K.b_col_evals[k];
            let b_row_at_kappa = matrix_evals_on_K.b_row_evals[k];
            let to_add_b = r_x_x_precomp[&b_row_at_kappa] * &r_beta_1_x_precomp[&b_col_at_kappa] * &matrix_evals_on_K.b_val_evals[k];
            *b_beta_1_vals_on_H.entry(b_row_at_kappa).or_insert(F::zero()) += &to_add_b;

            let c_col_at_kappa = matrix_evals_on_K.c_col_evals[k];
            let c_row_at_kappa = matrix_evals_on_K.c_row_evals[k];
            let to_add_c = r_x_x_precomp[&c_row_at_kappa] * &r_beta_1_x_precomp[&c_col_at_kappa] * &matrix_evals_on_K.c_val_evals[k];
            *c_beta_1_vals_on_H.entry(c_row_at_kappa).or_insert(F::zero()) += &to_add_c;
        }
        end_timer!(m_beta_1_evals_time);

        let summed_m_beta_1_time = start_timer!(|| "Computing summed_m_beta_1 poly");
        let summed_m_beta_1_evals = domain_h.elements().map(|h_elem| {
                eta_a * a_beta_1_vals_on_H.get(&h_elem).unwrap_or(&F::zero())
            + &(eta_b * b_beta_1_vals_on_H.get(&h_elem).unwrap_or(&F::zero()))
            + &(eta_c * c_beta_1_vals_on_H.get(&h_elem).unwrap_or(&F::zero()))
        }).collect::<Vec<_>>();

        let summed_m_beta_1 = EvaluationsOnDomain::from_vec_and_domain(summed_m_beta_1_evals, domain_h).interpolate();
        end_timer!(summed_m_beta_1_time);

        let q_2_time = start_timer!(|| "Computing q_2 poly");
        let q_2 = &r_alpha_poly * &summed_m_beta_1;
        end_timer!(q_2_time);

        let sumcheck_time = start_timer!(|| "Computing sumcheck h and g polys");
        let (h_2, x_g_2) = q_2.divide_by_vanishing_poly(domain_h).unwrap();
        let sigma_2 = x_g_2.coeffs[0] * &domain_h.size_as_field_element;
        let g_2 = Polynomial::from_coefficients_slice(&x_g_2.coeffs[1..]);
        drop(x_g_2);
        end_timer!(sumcheck_time);

        let msg = ProverMsg {
            field_elements: vec![sigma_2],
        };

        assert!(g_2.degree() <= domain_h.size() - 2);
        assert!(h_2.degree() <= domain_h.size() - 2);
        let oracles = ProverThirdOracles {
            g_2: LabeledPolynomial::new_owned("g_2".to_string(), g_2, Some(domain_h.size() - 2), None),
            h_2: LabeledPolynomial::new_owned("h_2".to_string(), h_2, None, None),
        };
        end_timer!(round_time);

        let state = ProverState {
            formatted_input_assignment,
            witness_assignment,
            z_a,
            z_b,
            w_poly: None,
            mz_polys,
            zk_bound,
            matrix_evals_on_K,
            matrix_evals_on_B,
            verifier_first_msg: verifier_first_msg,
            verifier_second_msg: Some(*ver_message),
            mask_poly: mask_poly,
            r_alpha_poly: Some(r_alpha_poly),
            domain_h,
            domain_k,
            _field: PhantomData,
            _cs: PhantomData,
        };

        (msg, oracles, state)
    }

    /// Output the number of oracles sent by the prover in the third round.
    pub fn prover_num_third_round_oracles() -> usize {
        2
    }

    /// Output the degree bounds of oracles in the third round.
    pub fn prover_third_round_degree_bounds<C: ConstraintSynthesizer<F>>(
        info: &IndexInfo<F, C>,
    ) -> impl Iterator<Item = Option<usize>> {
        let num_constraints = info.num_constraints;
        let h_size = EvaluationDomain::<F>::compute_size_of_domain(num_constraints).unwrap();

        vec![Some(h_size - 2), None].into_iter()
    }

    /// Output the fourth round message and the next state.
    pub fn prover_fourth_round<'a, 'b, R: RngCore, C: ConstraintSynthesizer<F>>(
        ver_message: &VerifierThirdMsg<F>,
        prover_state: ProverState<'a, 'b, F, C>,
        _r: &mut R,
    ) -> Result<(ProverMsg<F>, ProverFourthOracles<'b, F>), Error> {
        let round_time = start_timer!(|| "AHP::Prover::FourthRound");

        let ProverState {
            matrix_evals_on_K,
            matrix_evals_on_B,
            verifier_first_msg,
            verifier_second_msg,
            domain_h,
            domain_k,
            ..
        } = prover_state;

        let VerifierFirstMsg {
            eta_a, eta_b, eta_c, ..
        } = verifier_first_msg
            .expect("ProverState should include verifier_first_msg when prover_fourth_round is called");

        let VerifierSecondMsg { beta_1 } = verifier_second_msg
            .expect("ProverState should include verifier_second_msg when prover_fourth_round is called");

        let VerifierThirdMsg { beta_2 } = *ver_message;

        let v_H_at_beta_1 = domain_h.evaluate_vanishing_polynomial(beta_1);
        let v_H_at_beta_2 = domain_h.evaluate_vanishing_polynomial(beta_2);

        let f_3_evals_time = start_timer!(|| "Computing f_3 evals on K");
        let mut f_3_vals_on_K = Vec::with_capacity(domain_k.size());
        let mut sigma_3 = F::zero();
        let mut inverses_a = Vec::with_capacity(domain_k.size());
        let mut inverses_b = Vec::with_capacity(domain_k.size());
        let mut inverses_c = Vec::with_capacity(domain_k.size());
        for idx in 0..domain_k.size() {
            inverses_a.push((beta_2 - &matrix_evals_on_K.a_row_evals[idx]) * &(beta_1 - &matrix_evals_on_K.a_col_evals[idx]));
            inverses_b.push((beta_2 - &matrix_evals_on_K.b_row_evals[idx]) * &(beta_1 - &matrix_evals_on_K.b_col_evals[idx]));
            inverses_c.push((beta_2 - &matrix_evals_on_K.c_row_evals[idx]) * &(beta_1 - &matrix_evals_on_K.c_col_evals[idx]));
        }
        algebra_core::batch_inversion(&mut inverses_a);
        algebra_core::batch_inversion(&mut inverses_b);
        algebra_core::batch_inversion(&mut inverses_c);

        for idx in 0..domain_k.size() {
            let f_3_at_kappa =
                v_H_at_beta_2 * &v_H_at_beta_1 *
                &( (eta_a * &matrix_evals_on_K.a_val_evals[idx] * &inverses_a[idx])
                + &(eta_b * &matrix_evals_on_K.b_val_evals[idx] * &inverses_b[idx])
                + &(eta_c * &matrix_evals_on_K.c_val_evals[idx] * &inverses_c[idx]));
            f_3_vals_on_K.push(f_3_at_kappa);

            sigma_3 += &f_3_at_kappa;
        }
        end_timer!(f_3_evals_time);

        let f_3_poly_time = start_timer!(|| "Computing f_3 poly");
        let f_3 = EvaluationsOnDomain::from_vec_and_domain(f_3_vals_on_K, domain_k).interpolate();
        end_timer!(f_3_poly_time);

        let g_3 = Polynomial::from_coefficients_slice(&f_3.coeffs[1..]);

        let domain_b = EvaluationDomain::<F>::new(6 * domain_k.size() - 6).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let beta_minus_matrix_eval_time = start_timer!(|| "Computing beta_{1,2} - M_{row,col,val} evals on B");

        let beta_2_minus_a_row_on_B = cfg_iter!(matrix_evals_on_B.a_row_evals.evals).map(|a| beta_2 - a).collect();
        let beta_2_minus_a_row_on_B = EvaluationsOnDomain::from_vec_and_domain(beta_2_minus_a_row_on_B, domain_b);

        let beta_1_minus_a_col_on_B = cfg_iter!(matrix_evals_on_B.a_col_evals.evals).map(|a| beta_1 - a).collect();
        let beta_1_minus_a_col_on_B = EvaluationsOnDomain::from_vec_and_domain(beta_1_minus_a_col_on_B, domain_b);

        let beta_2_minus_b_row_on_B = cfg_iter!(matrix_evals_on_B.b_row_evals.evals).map(|b| beta_2 - b).collect();
        let beta_2_minus_b_row_on_B = EvaluationsOnDomain::from_vec_and_domain(beta_2_minus_b_row_on_B, domain_b);

        let beta_1_minus_b_col_on_B = cfg_iter!(matrix_evals_on_B.b_col_evals.evals).map(|b| beta_1 - b).collect();
        let beta_1_minus_b_col_on_B = EvaluationsOnDomain::from_vec_and_domain(beta_1_minus_b_col_on_B, domain_b);

        let beta_2_minus_c_row_on_B = cfg_iter!(matrix_evals_on_B.c_row_evals.evals).map(|c| beta_2 - c).collect();
        let beta_2_minus_c_row_on_B = EvaluationsOnDomain::from_vec_and_domain(beta_2_minus_c_row_on_B, domain_b);

        let beta_1_minus_c_col_on_B = cfg_iter!(matrix_evals_on_B.c_col_evals.evals).map(|c| beta_1 - c).collect();
        let beta_1_minus_c_col_on_B = EvaluationsOnDomain::from_vec_and_domain(beta_1_minus_c_col_on_B, domain_b);

        end_timer!(beta_minus_matrix_eval_time);

        let a_evals_time = start_timer!(|| "Computing a evals on B");
        let a_poly_on_B = cfg_into_iter!(0..domain_b.size()).map(|idx| {
                v_H_at_beta_2 * &v_H_at_beta_1 *
                &( (eta_a * &matrix_evals_on_B.a_val_evals.evals[idx] * &beta_2_minus_b_row_on_B.evals[idx] * &beta_1_minus_b_col_on_B.evals[idx]
                                                  * &beta_2_minus_c_row_on_B.evals[idx] * &beta_1_minus_c_col_on_B.evals[idx])
                + &(eta_b * &matrix_evals_on_B.b_val_evals.evals[idx] * &beta_2_minus_a_row_on_B.evals[idx] * &beta_1_minus_a_col_on_B.evals[idx]
                                                  * &beta_2_minus_c_row_on_B.evals[idx] * &beta_1_minus_c_col_on_B.evals[idx])
                + &(eta_c * &matrix_evals_on_B.c_val_evals.evals[idx] * &beta_2_minus_a_row_on_B.evals[idx] * &beta_1_minus_a_col_on_B.evals[idx]
                                                  * &beta_2_minus_b_row_on_B.evals[idx] * &beta_1_minus_b_col_on_B.evals[idx]))
        }).collect();
        end_timer!(a_evals_time);

        let a_poly_time = start_timer!(|| "Computing a poly");
        let a_poly = EvaluationsOnDomain::from_vec_and_domain(a_poly_on_B, domain_b).interpolate();
        end_timer!(a_poly_time);

        let b_evals_time = start_timer!(|| "Computing b evals on B");
        let b_poly_on_B = cfg_into_iter!(0..domain_b.size()).map(|idx| {
                   beta_2_minus_a_row_on_B.evals[idx] * &beta_1_minus_a_col_on_B.evals[idx]
                * &beta_2_minus_b_row_on_B.evals[idx] * &beta_1_minus_b_col_on_B.evals[idx]
                * &beta_2_minus_c_row_on_B.evals[idx] * &beta_1_minus_c_col_on_B.evals[idx]
        }).collect();
        end_timer!(b_evals_time);
        let b_poly_time = start_timer!(|| "Computing b poly");
        let b_poly = EvaluationsOnDomain::from_vec_and_domain(b_poly_on_B, domain_b).interpolate();
        end_timer!(b_poly_time);

        let h_3_poly_time = start_timer!(|| "Computing sumcheck h poly");
        let h_3 = (&a_poly - &(&b_poly * &f_3)).divide_by_vanishing_poly(domain_k).unwrap().0;
        end_timer!(h_3_poly_time);

        let msg = ProverMsg { field_elements: vec![sigma_3] };

        assert!(g_3.degree() <= domain_k.size() - 2);
        assert!(h_3.degree() <= 6 * domain_k.size() - 7);
        let oracles = ProverFourthOracles {
            g_3: LabeledPolynomial::new_owned("g_3".to_string(), g_3, Some(domain_k.size() - 2), None),
            h_3: LabeledPolynomial::new_owned("h_3".to_string(), h_3, None, None),
        };
        end_timer!(round_time);

        Ok((msg, oracles))
    }

    /// Output the number of oracles sent by the prover in the fourth round.
    pub fn prover_num_fourth_round_oracles() -> usize {
        2
    }

    /// Output the degree bounds of oracles in the fourth round.
    pub fn prover_fourth_round_degree_bounds<C: ConstraintSynthesizer<F>>(
        info: &IndexInfo<F, C>,
    ) -> impl Iterator<Item = Option<usize>> {
        let num_non_zero = info.num_non_zero;
        let k_size = EvaluationDomain::<F>::compute_size_of_domain(num_non_zero).unwrap();

        vec![Some(k_size - 2), None].into_iter()
    }
}
