use algebra::{PrimeField, Field};
use ff_fft::EvaluationDomain;
use std::marker::PhantomData;
use r1cs_core::SynthesisError;


/// Describes data structures and the algorithms used by the AHP indexer.
pub mod indexer;
/// Describes data structures and the algorithms used by the AHP prover.
pub mod prover;
/// Describes data structures and the algorithms used by the AHP verifier.
pub mod verifier;
pub(crate) mod constraint_systems;

/// The holographic IOP defined in [CHMMVW19](TODO: insert link here).
pub struct AHPForR1CS<F: Field> {
    field: PhantomData<F>,
}

impl<F: PrimeField> AHPForR1CS<F> {
    /// Check that the (formatted) public input is of the form 2^n for some integer n.
    pub fn num_formatted_public_inputs_is_admissible(num_inputs: usize) -> bool {
        num_inputs.count_ones() == 1
    }

    /// Check that the (formatted) public input is of the form 2^n for some integer n.
    pub fn formatted_public_input_is_admissible(input: &[F]) -> bool {
        Self::num_formatted_public_inputs_is_admissible(input.len())
    }

    /// The maximum degree of polynomials produced by the indexer and prover
    /// of this protocol. Currently, `marlin` only supports inputs of size one
    /// less than a power of 2 (i.e., of the form 2^n - 1).
    pub fn max_degree(
        num_constraints: usize,
        num_variables: usize,
        num_non_zero: usize
    ) -> Result<usize, Error> {
        if num_constraints != num_variables {
            Err(Error::NonSquareMatrix)
        } else {
            let zk_bound = 1;
            let domain_h_size = EvaluationDomain::<F>::compute_size_of_domain(num_constraints).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
            let domain_k_size = EvaluationDomain::<F>::compute_size_of_domain(num_non_zero).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
            Ok(*[
               2 * domain_h_size + zk_bound - 2,
               domain_h_size,
               domain_h_size,
               6 * domain_k_size - 6
            ].iter().max().unwrap())
        }
    }

}

/// Describes the failure modes of the AHP scheme.
#[derive(Debug)]
pub enum Error {
    /// During verification, a required evaluation is missing
    MissingEval(usize),
    /// The number of public inputs is incorrect.
    InvalidPublicInputLength,
    /// The instance generated during proving does not match that in the index.
    InstanceDoesNotMatchIndex,
    /// Currently we only support square constraint matrices.
    NonSquareMatrix,
    /// An error occurred during constraint generation.
    ConstraintSystemError(SynthesisError)
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

        inverses.iter_mut().for_each(|denominator| {
            *denominator = vanish_x * denominator
        });
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
    use rand::Rand;

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly() {
        for domain_size in 1..10 {
            let domain = EvaluationDomain::<Fr>::new(1 << domain_size).unwrap();
            let manual: Vec<_> = domain.elements().map(|elem| domain.eval_unnormalized_bivariate_lagrange_poly(elem, elem)).collect();
            let fast = domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs();
            assert_eq!(fast, manual);
        }
    }

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly_diff_inputs() {
        let rng = &mut rand::thread_rng();
        for domain_size in 1..10 {
            let domain = EvaluationDomain::<Fr>::new(1 << domain_size).unwrap();
            let x = Fr::rand(rng);
            let manual: Vec<_> = domain.elements().map(|y| domain.eval_unnormalized_bivariate_lagrange_poly(x, y)).collect();
            let fast = domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(x);
            assert_eq!(fast, manual);
        }
    }
}
