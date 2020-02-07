use algebra::{Field, PrimeField};
use ff_fft::EvaluationDomain;
use r1cs_core::SynthesisError;
use std::marker::PhantomData;

pub(crate) mod constraint_systems;
/// Describes data structures and the algorithms used by the AHP indexer.
pub mod indexer;
/// Describes data structures and the algorithms used by the AHP prover.
pub mod prover;
/// Describes data structures and the algorithms used by the AHP verifier.
pub mod verifier;

/// The algebraic holographic proof defined in [CHMMVW19](https://eprint.iacr.org/2019/1047).
/// Currently, this AHP only supports inputs of size one
/// less than a power of 2 (i.e., of the form 2^n - 1).
pub struct AHPForR1CS<F: Field> {
    field: PhantomData<F>,
}

impl<F: PrimeField> AHPForR1CS<F> {

    /// The labels for the polynomials output by the AHP indexer and prover.
    pub const ALL_POLYNOMIALS: [&'static str; 19] = [
        "a_row", "a_col", "a_val", "b_row", "b_col", "b_val", "c_row", "c_col", "c_val",
        "w", "z_a", "z_b", "mask_poly", "g_1", "h_1",
        "g_2", "h_2",
        "g_3", "h_3",
    ];

    /// Check that the (formatted) public input is of the form 2^n for some integer n.
    pub fn num_formatted_public_inputs_is_admissible(num_inputs: usize) -> bool {
        num_inputs.count_ones() == 1
    }

    /// Check that the (formatted) public input is of the form 2^n for some integer n.
    pub fn formatted_public_input_is_admissible(input: &[F]) -> bool {
        Self::num_formatted_public_inputs_is_admissible(input.len())
    }

    /// The maximum degree of polynomials produced by the indexer and prover
    /// of this protocol.
    /// The number of the variables must include the "one" variable. That is, it
    /// must be with respect to the number of formatted public inputs.
    pub fn max_degree(num_constraints: usize, num_variables: usize, num_non_zero: usize) -> Result<usize, Error> {
        let padded_matrix_dim = constraint_systems::padded_matrix_dim(num_variables, num_constraints);
        let zk_bound = 1;
        let domain_h_size = EvaluationDomain::<F>::compute_size_of_domain(padded_matrix_dim)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k_size = EvaluationDomain::<F>::compute_size_of_domain(num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        Ok(*[
           2 * domain_h_size + zk_bound - 2,
           3 * domain_h_size + 2 * zk_bound - 3, //  mask_poly
           domain_h_size,
           domain_h_size,
           6 * domain_k_size - 6,
        ]
        .iter()
        .max()
        .unwrap())
    }

    /// Get all the strict degree bounds enforced in the AHP.
    pub fn get_degree_bounds<C>(info: &indexer::IndexInfo<F, C>) -> [usize; 3] {
        let mut degree_bounds = [0usize; 3];
        let num_constraints = info.num_constraints;
        let num_non_zero = info.num_non_zero;
        let h_size = EvaluationDomain::<F>::compute_size_of_domain(num_constraints).unwrap();
        let k_size = EvaluationDomain::<F>::compute_size_of_domain(num_non_zero).unwrap();

        degree_bounds[0] = h_size - 2;
        degree_bounds[1] = h_size - 2;
        degree_bounds[2] = k_size - 2;
        degree_bounds
    }
}

/// Describes the failure modes of the AHP scheme.
#[derive(Debug)]
pub enum Error {
    /// During verification, a required evaluation is missing
    MissingEval(&'static str),
    /// The number of public inputs is incorrect.
    InvalidPublicInputLength,
    /// The instance generated during proving does not match that in the index.
    InstanceDoesNotMatchIndex,
    /// Currently we only support square constraint matrices.
    NonSquareMatrix,
    /// An error occurred during constraint generation.
    ConstraintSystemError(SynthesisError),
}

impl From<SynthesisError> for Error {
    fn from(other: SynthesisError) -> Self {
        Error::ConstraintSystemError(other)
    }
}

/// The derivative of the vanishing polynomial
pub trait UnnormalizedBivariateLagrangePoly<F: PrimeField> {
    /// Evaluate the polynomial
    fn eval_unnormalized_bivariate_lagrange_poly(&self, x: F, y: F) -> F;

    /// Evaluate over a batch of inputs
    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(&self, x: F) -> Vec<F>;

    /// Evaluate the magic polynomial over `self`
    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs(&self) -> Vec<F>;
}

impl<F: PrimeField> UnnormalizedBivariateLagrangePoly<F> for EvaluationDomain<F> {
    fn eval_unnormalized_bivariate_lagrange_poly(&self, x: F, y: F) -> F {
        if x != y {
            (self.evaluate_vanishing_polynomial(x) - &self.evaluate_vanishing_polynomial(y)) / &(x - &y)
        } else {
            self.size_as_field_element * &x.pow(&[(self.size() - 1) as u64])
        }
    }

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(&self, x: F) -> Vec<F> {
        let vanish_x = self.evaluate_vanishing_polynomial(x);
        let mut inverses: Vec<F> = self.elements().map(|y| x - &y).collect();
        algebra::fields::batch_inversion(&mut inverses);

        inverses
            .iter_mut()
            .for_each(|denominator| *denominator *= &vanish_x);
        inverses
    }

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs(&self) -> Vec<F> {
        let mut elems: Vec<F> = self.elements().map(|e| e * &self.size_as_field_element).collect();
        elems[1..].reverse();
        elems
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::fields::bls12_381::fr::Fr;
    use algebra::UniformRand;

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly() {
        for domain_size in 1..10 {
            let domain = EvaluationDomain::<Fr>::new(1 << domain_size).unwrap();
            let manual: Vec<_> = domain
                .elements()
                .map(|elem| domain.eval_unnormalized_bivariate_lagrange_poly(elem, elem))
                .collect();
            let fast = domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs();
            assert_eq!(fast, manual);
        }
    }

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly_diff_inputs() {
        let rng = &mut algebra::test_rng();
        for domain_size in 1..10 {
            let domain = EvaluationDomain::<Fr>::new(1 << domain_size).unwrap();
            let x = Fr::rand(rng);
            let manual: Vec<_> = domain
                .elements()
                .map(|y| domain.eval_unnormalized_bivariate_lagrange_poly(x, y))
                .collect();
            let fast = domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(x);
            assert_eq!(fast, manual);
        }
    }
}
