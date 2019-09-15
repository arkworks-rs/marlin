use std::marker::PhantomData;
use algebra::PrimeField;
use crate::ahp::indexer::*;
use crate::ahp::prover::ProverMsg;
use r1cs_core::ConstraintSynthesizer;
use poly_commit::MultiPolynomialCommitment as MultiPC;

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// The universal prover key for the argument system.
pub type UniversalProverKey<F, PC> = <PC as MultiPC<F>>::CommitterKey;
/// The universal verifier key for the argument system.
pub type UniversalVerifierKey<F, PC> = <PC as MultiPC<F>>::VerifierKey;


/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// Verification key for a specific index (i.e., R1CS matrices).
pub struct IndexVerifierKey<F: PrimeField, PC: MultiPC<F>, C: ConstraintSynthesizer<F>> {
    /// Stores information about the size of the index, as well as its field of
    /// definition.
    pub index_info: IndexInfo<F, C>,
    /// Commitments to the indexed polynomials.
    pub index_comms: Vec<PC::Commitment>,
}

impl<F: PrimeField, PC: MultiPC<F>, C: ConstraintSynthesizer<F>> algebra::ToBytes for IndexVerifierKey<F, PC, C> {
    fn write<W: std::io::Write>(&self, mut w: W) -> std::io::Result<()> {
        self.index_info.write(&mut w)?;
        self.index_comms.write(&mut w)
    }
}

impl<F: PrimeField, PC: MultiPC<F>, C: ConstraintSynthesizer<F>> Clone for IndexVerifierKey<F, PC, C> {
    fn clone(&self) -> Self {
        Self {
            index_comms: self.index_comms.clone(),
            index_info: self.index_info.clone(),
        }
    }
}

impl<F: PrimeField, PC: MultiPC<F>, C: ConstraintSynthesizer<F>> IndexVerifierKey<F, PC, C> {
    /// Iterate over the commitments to indexed polynomials in `self`.
    pub fn iter(&self) -> impl Iterator<Item = &PC::Commitment> {
        self.index_comms.iter()
    }
}

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// Proving key for a specific index (i.e., R1CS matrices).
pub struct IndexProverKey<'a, F: PrimeField, PC: MultiPC<F>, C: ConstraintSynthesizer<F>> {
    /// The index verifier key.
    pub index_vk: IndexVerifierKey<F, PC, C>,
    /// The randomness for the index polynomial commitments. 
    pub index_comm_rands: Vec<PC::Randomness>,
    /// The index itself.
    pub index: Index<'a, F, C>,
}

impl<'a, F: PrimeField, PC: MultiPC<F>, C: ConstraintSynthesizer<F>> Clone for IndexProverKey<'a, F, PC, C>
where
    PC::Commitment: Clone,
{
    fn clone(&self) -> Self {
        Self {
            index_vk: self.index_vk.clone(),
            index_comm_rands: self.index_comm_rands.clone(),
            index: self.index.clone(),
        }
    }
}

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// A zkSNARK proof.
pub struct Proof<F: PrimeField, PC: MultiPC<F>, C: ConstraintSynthesizer<F>> {
    /// Commitments to the polynomials produced by the AHP prover.
    pub commitments: Vec<Vec<PC::Commitment>>,
    /// Evaluations of these polynomials.
    pub evaluations: Vec<F>,
    /// The field elements sent by the prover.
    pub prover_messages: Vec<ProverMsg<F>>,
    /// An evaluation proof from the polynomial commitment.
    pub pc_proof: PC::Proof,
    #[doc(hidden)]
    constraint_system: PhantomData<C>,
}

impl<F: PrimeField, PC: MultiPC<F>, C: ConstraintSynthesizer<F>> Proof<F, PC, C>  {
    /// Construct a new proof.
    pub fn new(
        commitments: Vec<Vec<PC::Commitment>>,
        evaluations: Vec<F>,
        prover_messages: Vec<ProverMsg<F>>,
        pc_proof: PC::Proof,
    ) -> Self {
        Self {
            commitments,
            evaluations,
            prover_messages,
            pc_proof,
            constraint_system: PhantomData,
        }
    }

    /// Prints information about the size of the proof.
    pub fn print_size_info(&self) {
        use poly_commit::PCCommitment;

        let size_of_fe_in_bytes = F::zero().into_repr().as_ref().len() * 8;
        let mut num_comms_without_degree_bounds = 0;
        let mut num_comms_with_degree_bounds = 0;
        let mut size_bytes_comms_without_degree_bounds = 0;
        let mut size_bytes_comms_with_degree_bounds = 0;
        for c in self.commitments.iter().flat_map(|c| c) {
            if !c.has_degree_bound() {
                num_comms_without_degree_bounds += 1;
                size_bytes_comms_without_degree_bounds += c.size_in_bytes();
            } else {
                num_comms_with_degree_bounds += 1;
                size_bytes_comms_with_degree_bounds += c.size_in_bytes();
            }
        }

        let num_evals = self.evaluations.len();
        let evals_size_in_bytes = num_evals * size_of_fe_in_bytes;
        let num_prover_messages: usize = self.prover_messages.iter().map(|v| v.field_elements.len()).sum();
        let prover_msg_size_in_bytes = num_prover_messages * size_of_fe_in_bytes;
        let arg_size = 
            size_bytes_comms_with_degree_bounds + 
            size_bytes_comms_without_degree_bounds + 
            prover_msg_size_in_bytes + 
            evals_size_in_bytes;
        let stats = format!(
            "Argument size in bytes: {}\n\n\
            Number of commitments without degree bounds: {}\n\
            Size (in bytes) of commitments without degree bounds: {}\n\
            Number of commitments with degree bounds: {}\n\
            Size (in bytes) of commitments with degree bounds: {}\n\n\
            Number of evaluations: {}\n\
            Size (in bytes) of evaluations: {}\n\n\
            Number of field elements in prover messages: {}\n\
            Size (in bytes) of prover message: {}\n",
            arg_size,

            num_comms_without_degree_bounds,
            size_bytes_comms_without_degree_bounds,
            num_comms_with_degree_bounds,
            size_bytes_comms_with_degree_bounds,

            num_evals,
            evals_size_in_bytes,

            num_prover_messages,
            prover_msg_size_in_bytes,
        );
        add_to_trace!(|| "Statistics about proof", || stats);
    }
}
