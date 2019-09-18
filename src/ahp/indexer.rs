#![allow(non_snake_case)]

use crate::ahp::{constraint_systems::matrix_to_polys, constraint_systems::IndexerConstraintSystem, AHPForR1CS, Error};
use algebra::PrimeField;
use derivative::Derivative;
use ff_fft::{EvaluationDomain, Evaluations as EvaluationsOnDomain};
use poly_commit::LabeledPolynomial;
use r1cs_core::{ConstraintSynthesizer, SynthesisError};

use std::marker::PhantomData;

/// Information about the index, including the field of definition, the number of
/// public input variables, the number of secret witness variables, the number of
/// constraints, and the maximum number of non-zero entries in any of the
/// constraint matrices.
#[derive(Derivative)]
#[derivative(Clone(bound = ""), Copy(bound = ""))]
pub struct IndexInfo<F, C> {
    /// The number of public input variables.
    pub num_input_variables: usize,
    /// The number of secret witness variables.
    pub num_witness_variables: usize,
    /// The number of constraints.
    pub num_constraints: usize,
    /// The maximum number of non-zero entries in any constraint matrix.
    pub num_non_zero: usize,

    #[doc(hidden)]
    f: PhantomData<F>,
    #[doc(hidden)]
    cs: PhantomData<C>,
}

impl<F: PrimeField, C: ConstraintSynthesizer<F>> algebra::ToBytes for IndexInfo<F, C> {
    fn write<W: std::io::Write>(&self, mut w: W) -> std::io::Result<()> {
        (self.num_input_variables as u64).write(&mut w)?;
        (self.num_witness_variables as u64).write(&mut w)?;
        (self.num_constraints as u64).write(&mut w)?;
        (self.num_non_zero as u64).write(&mut w)
    }
}

impl<F, C> IndexInfo<F, C> {
    /// The maximum degree of polynomial required to represent this index in the
    /// the AHP.
    pub fn max_degree(&self) -> usize {
        *[
            self.num_input_variables,
            self.num_witness_variables,
            self.num_constraints,
            self.num_non_zero,
        ]
        .iter()
        .max()
        .unwrap()
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = "F: PrimeField"))]
/// The indexed version of the constraint system.
pub struct Index<'a, F: PrimeField, C: ConstraintSynthesizer<F>> {
    /// Information about the index.
    pub index_info: IndexInfo<F, C>,

    /// The A matrix for the R1CS instance
    pub a_matrix: Vec<Vec<(F, usize)>>,
    /// The B matrix for the R1CS instance
    pub b_matrix: Vec<Vec<(F, usize)>>,
    /// The C matrix for the R1CS instance
    pub c_matrix: Vec<Vec<(F, usize)>>,

    /// LDE of the row-indices of the non-zero entries of A.
    pub a_row_poly: LabeledPolynomial<'a, F>,
    /// LDE of the rol-indices of the non-zero entries of A.
    pub a_col_poly: LabeledPolynomial<'a, F>,
    /// LDE of the ralues of the non-zero entries of A.
    pub a_val_poly: LabeledPolynomial<'a, F>,

    /// LDE of the row-indices of the non-zero entries of B.
    pub b_row_poly: LabeledPolynomial<'a, F>,
    /// LDE of the rol-indices of the non-zero entries of B.
    pub b_col_poly: LabeledPolynomial<'a, F>,
    /// LDE of the ralues of the non-zero entries of B.
    pub b_val_poly: LabeledPolynomial<'a, F>,

    /// LDE of the row-indices of the non-zero entries of C.
    pub c_row_poly: LabeledPolynomial<'a, F>,
    /// LDE of the rol-indices of the non-zero entries of C.
    pub c_col_poly: LabeledPolynomial<'a, F>,
    /// LDE of the ralues of the non-zero entries of C.
    pub c_val_poly: LabeledPolynomial<'a, F>,

    /// Row-indices of the non-zero entries of A.
    pub a_row_evals_on_K: EvaluationsOnDomain<F>,
    /// Col-indices of the non-zero entries of A.
    pub a_col_evals_on_K: EvaluationsOnDomain<F>,
    /// Values of the non-zero entries of A.
    pub a_val_evals_on_K: EvaluationsOnDomain<F>,

    /// Row-indices of the non-zero entries of B.
    pub b_row_evals_on_K: EvaluationsOnDomain<F>,
    /// Col-indices of the non-zero entries of B.
    pub b_col_evals_on_K: EvaluationsOnDomain<F>,
    /// Values of the non-zero entries of B.
    pub b_val_evals_on_K: EvaluationsOnDomain<F>,

    /// Row-indices of the non-zero entries of C.
    pub c_row_evals_on_K: EvaluationsOnDomain<F>,
    /// Col-indices of the non-zero entries of C.
    pub c_col_evals_on_K: EvaluationsOnDomain<F>,
    /// Values of the non-zero entries of C.
    pub c_val_evals_on_K: EvaluationsOnDomain<F>,

    /// LDE of the row-indices of the non-zero entries of A, on larger domain.
    pub a_row_evals_on_B: EvaluationsOnDomain<F>,
    /// LDE of the col-indices of the non-zero entries of A, on larger domain.
    pub a_col_evals_on_B: EvaluationsOnDomain<F>,
    /// LDE of the values of the non-zero entries of A, on larger domain.
    pub a_val_evals_on_B: EvaluationsOnDomain<F>,

    /// LDE of the row-indices of the non-zero entries of B, on larger domain.
    pub b_row_evals_on_B: EvaluationsOnDomain<F>,
    /// LDE of the col-indices of the non-zero entries of B, on larger domain.
    pub b_col_evals_on_B: EvaluationsOnDomain<F>,
    /// LDE of the values of the non-zero entries of B, on larger domain.
    pub b_val_evals_on_B: EvaluationsOnDomain<F>,

    /// LDE of the row-indices of the non-zero entries of C, on larger domain.
    pub c_row_evals_on_B: EvaluationsOnDomain<F>,
    /// LDE of the col-indices of the non-zero entries of C, on larger domain.
    pub c_col_evals_on_B: EvaluationsOnDomain<F>,
    /// LDE of the values of the non-zero entries of C, on larger domain.
    pub c_val_evals_on_B: EvaluationsOnDomain<F>,
}

impl<'a, F: PrimeField, C: ConstraintSynthesizer<F>> Index<'a, F, C> {
    /// The maximum degree required to represent polynomials of this index.
    pub fn max_degree(&self) -> usize {
        self.index_info.max_degree()
    }

    /// Iterate over the indexed evaluations.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<'a, F>> {
        vec![
            &self.a_row_poly,
            &self.a_col_poly,
            &self.a_val_poly,
            &self.b_row_poly,
            &self.b_col_poly,
            &self.b_val_poly,
            &self.c_row_poly,
            &self.c_col_poly,
            &self.c_val_poly,
        ]
        .into_iter()
    }
}

impl<F: PrimeField> AHPForR1CS<F> {
    /// Generate the index for this constraint system.
    pub fn index<'a, C: ConstraintSynthesizer<F>>(c: C) -> Result<Index<'a, F, C>, Error> {
        let index_time = start_timer!(|| "AHP::Index");

        let constraint_time = start_timer!(|| "Generating constraints");
        let mut ics = IndexerConstraintSystem::new();
        c.generate_constraints(&mut ics)?;
        end_timer!(constraint_time);

        let num_formatted_input_variables = ics.num_input_variables;
        let num_witness_variables = ics.num_witness_variables;
        let num_constraints = ics.num_constraints;
        let num_non_zero = ics.num_non_zero();

        if num_constraints != num_formatted_input_variables + num_witness_variables {
            eprintln!(
                "number of (formatted) input_variables: {}",
                num_formatted_input_variables
            );
            eprintln!("number of witness_variables: {}", num_witness_variables);
            eprintln!("number of num_constraints: {}", num_constraints);
            eprintln!("number of num_non_zero: {}", ics.num_non_zero());
            return Err(Error::NonSquareMatrix);
        }

        if !Self::num_formatted_public_inputs_is_admissible(num_formatted_input_variables) {
            Err(Error::InvalidPublicInputLength)?
        }

        let index_info = IndexInfo {
            num_input_variables: num_formatted_input_variables,
            num_witness_variables,
            num_constraints,
            num_non_zero,

            f: PhantomData,
            cs: PhantomData,
        };

        let domain_h = EvaluationDomain::new(num_constraints).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k = EvaluationDomain::new(num_non_zero).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let x_domain = EvaluationDomain::<F>::new(num_formatted_input_variables)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let b_domain =
            EvaluationDomain::<F>::new(6 * domain_k.size() - 6).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let a_matrix = ics.a_matrix();
        let b_matrix = ics.b_matrix();
        let c_matrix = ics.c_matrix();

        let a_poly_time = start_timer!(|| "Generating A polynomials");
        let (
            (a_row_evals_on_K, a_col_evals_on_K, a_val_evals_on_K),
            (a_row_evals_on_B, a_col_evals_on_B, a_val_evals_on_B),
            (a_row_poly, a_col_poly, a_val_poly),
        ) = matrix_to_polys(a_matrix.clone(), domain_k, domain_h, x_domain, b_domain);
        end_timer!(a_poly_time);

        let b_poly_time = start_timer!(|| "Generating B polynomials");
        let (
            (b_row_evals_on_K, b_col_evals_on_K, b_val_evals_on_K),
            (b_row_evals_on_B, b_col_evals_on_B, b_val_evals_on_B),
            (b_row_poly, b_col_poly, b_val_poly),
        ) = matrix_to_polys(b_matrix.clone(), domain_k, domain_h, x_domain, b_domain);
        end_timer!(b_poly_time);

        let c_poly_time = start_timer!(|| "Generating C polynomials");
        let (
            (c_row_evals_on_K, c_col_evals_on_K, c_val_evals_on_K),
            (c_row_evals_on_B, c_col_evals_on_B, c_val_evals_on_B),
            (c_row_poly, c_col_poly, c_val_poly),
        ) = matrix_to_polys(c_matrix.clone(), domain_k, domain_h, x_domain, b_domain);
        end_timer!(c_poly_time);

        end_timer!(index_time);
        Ok(Index {
            index_info,

            a_matrix,
            b_matrix,
            c_matrix,

            a_row_poly: LabeledPolynomial::new_owned(a_row_poly, None, None),
            a_col_poly: LabeledPolynomial::new_owned(a_col_poly, None, None),
            a_val_poly: LabeledPolynomial::new_owned(a_val_poly, None, None),

            b_row_poly: LabeledPolynomial::new_owned(b_row_poly, None, None),
            b_col_poly: LabeledPolynomial::new_owned(b_col_poly, None, None),
            b_val_poly: LabeledPolynomial::new_owned(b_val_poly, None, None),

            c_row_poly: LabeledPolynomial::new_owned(c_row_poly, None, None),
            c_col_poly: LabeledPolynomial::new_owned(c_col_poly, None, None),
            c_val_poly: LabeledPolynomial::new_owned(c_val_poly, None, None),

            a_row_evals_on_K,
            a_col_evals_on_K,
            a_val_evals_on_K,

            b_row_evals_on_K,
            b_col_evals_on_K,
            b_val_evals_on_K,

            c_row_evals_on_K,
            c_col_evals_on_K,
            c_val_evals_on_K,

            a_row_evals_on_B,
            a_col_evals_on_B,
            a_val_evals_on_B,

            b_row_evals_on_B,
            b_col_evals_on_B,
            b_val_evals_on_B,

            c_row_evals_on_B,
            c_col_evals_on_B,
            c_val_evals_on_B,
        })
    }
}
