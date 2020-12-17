#![allow(non_snake_case)]

use crate::ahp::indexer::Matrix;
use crate::ahp::*;
use crate::{BTreeMap, ToString};
use ark_ff::{Field, PrimeField};
use ark_poly::{EvaluationDomain, Evaluations as EvaluationsOnDomain, GeneralEvaluationDomain};
use ark_relations::{
    lc,
    r1cs::{ConstraintMatrices, ConstraintSystemRef},
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_std::{
    cfg_iter_mut,
    io::{Read, Write},
};
use derivative::Derivative;

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

pub(crate) fn balance_matrices<F: Field>(a_matrix: &mut Matrix<F>, b_matrix: &mut Matrix<F>) {
    let mut a_density: usize = a_matrix.iter().map(|row| row.len()).sum();
    let mut b_density: usize = b_matrix.iter().map(|row| row.len()).sum();
    let mut max_density = core::cmp::max(a_density, b_density);
    let mut a_is_denser = a_density == max_density;
    for (a_row, b_row) in a_matrix.iter_mut().zip(b_matrix) {
        if a_is_denser {
            let a_row_size = a_row.len();
            let b_row_size = b_row.len();
            core::mem::swap(a_row, b_row);
            a_density = a_density - a_row_size + b_row_size;
            b_density = b_density - b_row_size + a_row_size;
            max_density = core::cmp::max(a_density, b_density);
            a_is_denser = a_density == max_density;
        }
    }
}

pub(crate) fn num_non_zero<F: PrimeField>(matrices: &ConstraintMatrices<F>) -> usize {
    *[
        matrices.a_num_non_zero,
        matrices.b_num_non_zero,
        matrices.c_num_non_zero,
    ]
    .iter()
    .max()
    .unwrap()
}

pub(crate) fn make_matrices_square_for_indexer<F: PrimeField>(cs: ConstraintSystemRef<F>) {
    let num_variables = cs.num_instance_variables() + cs.num_witness_variables();
    let matrix_dim = padded_matrix_dim(num_variables, cs.num_constraints());
    make_matrices_square(cs.clone(), num_variables);
    assert_eq!(
        cs.num_instance_variables() + cs.num_witness_variables(),
        cs.num_constraints(),
        "padding failed!"
    );
    assert_eq!(
        cs.num_instance_variables() + cs.num_witness_variables(),
        matrix_dim,
        "padding does not result in expected matrix size!"
    );
}

/// This must *always* be in sync with `make_matrices_square`.
pub(crate) fn padded_matrix_dim(num_formatted_variables: usize, num_constraints: usize) -> usize {
    core::cmp::max(num_formatted_variables, num_constraints)
}

pub(crate) fn pad_input_for_indexer_and_prover<F: PrimeField>(cs: ConstraintSystemRef<F>) {
    let formatted_input_size = cs.num_instance_variables();

    let domain_x = GeneralEvaluationDomain::<F>::new(formatted_input_size);
    assert!(domain_x.is_some());

    let padded_size = domain_x.unwrap().size();

    if padded_size > formatted_input_size {
        for _ in 0..(padded_size - formatted_input_size) {
            cs.new_input_variable(|| Ok(F::zero())).unwrap();
        }
    }
}

pub(crate) fn make_matrices_square<F: Field>(
    cs: ConstraintSystemRef<F>,
    num_formatted_variables: usize,
) {
    let num_constraints = cs.num_constraints();
    let matrix_padding = ((num_formatted_variables as isize) - (num_constraints as isize)).abs();

    if num_formatted_variables > num_constraints {
        // Add dummy constraints of the form 0 * 0 == 0
        for _ in 0..matrix_padding {
            cs.enforce_constraint(lc!(), lc!(), lc!())
                .expect("enforce 0 * 0 == 0 failed");
        }
    } else {
        // Add dummy unconstrained variables
        for _ in 0..matrix_padding {
            let _ = cs
                .new_witness_variable(|| Ok(F::one()))
                .expect("alloc failed");
        }
    }
}

#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(Clone(bound = "F: PrimeField"))]
pub struct MatrixEvals<F: PrimeField> {
    /// Evaluations of the LDE of row.
    pub row: EvaluationsOnDomain<F>,
    /// Evaluations of the LDE of col.
    pub col: EvaluationsOnDomain<F>,
    /// Evaluations of the LDE of val.
    pub val: EvaluationsOnDomain<F>,
}

/// Contains information about the arithmetization of the matrix M^*.
/// Here `M^*(i, j) := M(j, i) * u_H(j, j)`. For more details, see [COS19].
#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(Clone(bound = "F: PrimeField"))]
pub struct MatrixArithmetization<F: PrimeField> {
    /// LDE of the row indices of M^*.
    pub row: LabeledPolynomial<F>,
    /// LDE of the column indices of M^*.
    pub col: LabeledPolynomial<F>,
    /// LDE of the non-zero entries of M^*.
    pub val: LabeledPolynomial<F>,
    /// LDE of the vector containing entry-wise products of `row` and `col`,
    /// where `row` and `col` are as above.
    pub row_col: LabeledPolynomial<F>,

    /// Evaluation of `self.row`, `self.col`, and `self.val` on the domain `K`.
    pub evals_on_K: MatrixEvals<F>,

    /// Evaluation of `self.row`, `self.col`, and, `self.val` on
    /// an extended domain B (of size > `3K`).
    // TODO: rename B everywhere.
    pub evals_on_B: MatrixEvals<F>,

    /// Evaluation of `self.row_col` on an extended domain B (of size > `3K`).
    pub row_col_evals_on_B: EvaluationsOnDomain<F>,
}

// TODO for debugging: add test that checks result of arithmetize_matrix(M).
pub(crate) fn arithmetize_matrix<F: PrimeField>(
    matrix_name: &str,
    matrix: &mut Matrix<F>,
    interpolation_domain: GeneralEvaluationDomain<F>,
    output_domain: GeneralEvaluationDomain<F>,
    input_domain: GeneralEvaluationDomain<F>,
    expanded_domain: GeneralEvaluationDomain<F>,
) -> MatrixArithmetization<F> {
    let matrix_time = start_timer!(|| "Computing row, col, and val LDEs");

    let elems: Vec<_> = output_domain.elements().collect();

    let mut row_vec = Vec::new();
    let mut col_vec = Vec::new();
    let mut val_vec = Vec::new();

    let eq_poly_vals_time = start_timer!(|| "Precomputing eq_poly_vals");
    let eq_poly_vals: BTreeMap<F, F> = output_domain
        .elements()
        .zip(output_domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs())
        .collect();
    end_timer!(eq_poly_vals_time);

    let lde_evals_time = start_timer!(|| "Computing row, col and val evals");
    let mut inverses = Vec::new();

    let mut count = 0;

    // Recall that we are computing the arithmetization of M^*,
    // where `M^*(i, j) := M(j, i) * u_H(j, j)`.
    for (r, row) in matrix.into_iter().enumerate() {
        if !is_in_ascending_order(&row, |(_, a), (_, b)| a < b) {
            row.sort_by(|(_, a), (_, b)| a.cmp(b));
        };

        for &mut (val, i) in row {
            let row_val = elems[r];
            let col_val = elems[output_domain.reindex_by_subdomain(input_domain, i)];

            // We are dealing with the transpose of M
            row_vec.push(col_val);
            col_vec.push(row_val);
            val_vec.push(val);
            inverses.push(eq_poly_vals[&col_val]);

            count += 1;
        }
    }
    ark_ff::batch_inversion::<F>(&mut inverses);

    cfg_iter_mut!(val_vec)
        .zip(inverses)
        .for_each(|(v, inv)| *v *= &inv);
    end_timer!(lde_evals_time);

    for _ in 0..(interpolation_domain.size() - count) {
        col_vec.push(elems[0]);
        row_vec.push(elems[0]);
        val_vec.push(F::zero());
    }
    let row_col_vec: Vec<_> = row_vec
        .iter()
        .zip(&col_vec)
        .map(|(row, col)| *row * col)
        .collect();

    let interpolate_time = start_timer!(|| "Interpolating on K and B");
    let row_evals_on_K = EvaluationsOnDomain::from_vec_and_domain(row_vec, interpolation_domain);
    let col_evals_on_K = EvaluationsOnDomain::from_vec_and_domain(col_vec, interpolation_domain);
    let val_evals_on_K = EvaluationsOnDomain::from_vec_and_domain(val_vec, interpolation_domain);
    let row_col_evals_on_K =
        EvaluationsOnDomain::from_vec_and_domain(row_col_vec, interpolation_domain);

    let row = row_evals_on_K.clone().interpolate();
    let col = col_evals_on_K.clone().interpolate();
    let val = val_evals_on_K.clone().interpolate();
    let row_col = row_col_evals_on_K.interpolate();

    let row_evals_on_B =
        EvaluationsOnDomain::from_vec_and_domain(expanded_domain.fft(&row), expanded_domain);
    let col_evals_on_B =
        EvaluationsOnDomain::from_vec_and_domain(expanded_domain.fft(&col), expanded_domain);
    let val_evals_on_B =
        EvaluationsOnDomain::from_vec_and_domain(expanded_domain.fft(&val), expanded_domain);
    let row_col_evals_on_B =
        EvaluationsOnDomain::from_vec_and_domain(expanded_domain.fft(&row_col), expanded_domain);
    end_timer!(interpolate_time);

    end_timer!(matrix_time);
    let evals_on_K = MatrixEvals {
        row: row_evals_on_K,
        col: col_evals_on_K,
        val: val_evals_on_K,
    };
    let evals_on_B = MatrixEvals {
        row: row_evals_on_B,
        col: col_evals_on_B,
        val: val_evals_on_B,
    };

    let m_name = matrix_name.to_string();
    MatrixArithmetization {
        row: LabeledPolynomial::new(m_name.clone() + "_row", row, None, None),
        col: LabeledPolynomial::new(m_name.clone() + "_col", col, None, None),
        val: LabeledPolynomial::new(m_name.clone() + "_val", val, None, None),
        row_col: LabeledPolynomial::new(m_name + "_row_col", row_col, None, None),
        evals_on_K,
        evals_on_B,
        row_col_evals_on_B: row_col_evals_on_B,
    }
}

fn is_in_ascending_order<T: Ord>(x_s: &[T], is_less_than: impl Fn(&T, &T) -> bool) -> bool {
    if x_s.is_empty() {
        true
    } else {
        let mut i = 0;
        let mut is_sorted = true;
        while i < (x_s.len() - 1) {
            is_sorted &= is_less_than(&x_s[i], &x_s[i + 1]);
            i += 1;
        }
        is_sorted
    }
}

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// Formats the public input according to the requirements of the constraint
/// system
pub(crate) fn format_public_input<F: PrimeField>(public_input: &[F]) -> Vec<F> {
    let mut input = vec![F::one()];
    input.extend_from_slice(public_input);
    input
}

/// Takes in a previously formatted public input and removes the formatting
/// imposed by the constraint system.
pub(crate) fn unformat_public_input<F: PrimeField>(input: &[F]) -> Vec<F> {
    input[1..].to_vec()
}

pub(crate) fn make_matrices_square_for_prover<F: PrimeField>(cs: ConstraintSystemRef<F>) {
    let num_variables = cs.num_instance_variables() + cs.num_witness_variables();
    make_matrices_square(cs.clone(), num_variables);
    assert_eq!(
        cs.num_instance_variables() + cs.num_witness_variables(),
        cs.num_constraints(),
        "padding failed!"
    );
}
