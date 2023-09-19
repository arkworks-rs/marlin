use crate::ahp::indexer::*;
use crate::ahp::prover::ProverMsg;
use crate::Vec;
use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_ff::PrimeField;
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::{BatchLCProof, PolynomialCommitment};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::format;

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// The universal public parameters for the argument system.
pub type UniversalSRS<F, PC, S> =
    <PC as PolynomialCommitment<F, DensePolynomial<F>, S>>::UniversalParams;

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// Verification key for a specific index (i.e., R1CS matrices).
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct IndexVerifierKey<
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
    S: CryptographicSponge,
> {
    /// Stores information about the size of the index, as well as its field of
    /// definition.
    pub index_info: IndexInfo<F>,
    /// Commitments to the indexed polynomials.
    pub index_comms: Vec<PC::Commitment>,
    /// The verifier key for this index, trimmed from the universal SRS.
    pub verifier_key: PC::VerifierKey,
}

impl<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>, S>, S: CryptographicSponge>
    Clone for IndexVerifierKey<F, PC, S>
{
    fn clone(&self) -> Self {
        Self {
            index_comms: self.index_comms.clone(),
            index_info: self.index_info.clone(),
            verifier_key: self.verifier_key.clone(),
        }
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>, S>, S: CryptographicSponge>
    IndexVerifierKey<F, PC, S>
{
    /// Iterate over the commitments to indexed polynomials in `self`.
    pub fn iter(&self) -> impl Iterator<Item = &PC::Commitment> {
        self.index_comms.iter()
    }
}

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// Proving key for a specific index (i.e., R1CS matrices).
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct IndexProverKey<
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
    S: CryptographicSponge,
> {
    /// The index verifier key.
    pub index_vk: IndexVerifierKey<F, PC, S>,
    /// The randomness for the index polynomial commitments.
    pub index_comm_rands: Vec<PC::Randomness>,
    /// The index itself.
    pub index: Index<F>,
    /// The committer key for this index, trimmed from the universal SRS.
    pub committer_key: PC::CommitterKey,
}

impl<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>, S>, S: CryptographicSponge>
    Clone for IndexProverKey<F, PC, S>
where
    PC::Commitment: Clone,
{
    fn clone(&self) -> Self {
        Self {
            index_vk: self.index_vk.clone(),
            index_comm_rands: self.index_comm_rands.clone(),
            index: self.index.clone(),
            committer_key: self.committer_key.clone(),
        }
    }
}

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// A zkSNARK proof.
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
    S: CryptographicSponge,
> {
    /// Commitments to the polynomials produced by the AHP prover.
    pub commitments: Vec<Vec<PC::Commitment>>,
    /// Evaluations of these polynomials.
    pub evaluations: Vec<F>,
    /// The field elements sent by the prover.
    pub prover_messages: Vec<ProverMsg<F>>,
    /// An evaluation proof from the polynomial commitment.
    pub pc_proof: BatchLCProof<F, PC::BatchProof>,
}

impl<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>, S>, S: CryptographicSponge>
    Proof<F, PC, S>
{
    /// Construct a new proof.
    pub fn new(
        commitments: Vec<Vec<PC::Commitment>>,
        evaluations: Vec<F>,
        prover_messages: Vec<ProverMsg<F>>,
        pc_proof: BatchLCProof<F, PC::BatchProof>,
    ) -> Self {
        Self {
            commitments,
            evaluations,
            prover_messages,
            pc_proof,
        }
    }

    /// Prints information about the size of the proof.
    pub fn print_size_info(&self) {
        use ark_poly_commit::PCCommitment;

        let mut num_comms_without_degree_bounds = 0;
        let mut num_comms_with_degree_bounds = 0;
        let mut size_bytes_comms_without_degree_bounds = 0;
        let mut size_bytes_comms_with_degree_bounds = 0;
        for c in self.commitments.iter().flat_map(|c| c) {
            if !c.has_degree_bound() {
                num_comms_without_degree_bounds += 1;
                size_bytes_comms_without_degree_bounds += c.compressed_size();
            } else {
                num_comms_with_degree_bounds += 1;
                size_bytes_comms_with_degree_bounds += c.compressed_size();
            }
        }

        let proofs: Vec<PC::Proof> = self.pc_proof.proof.clone().into();
        let num_proofs = proofs.len();
        let size_bytes_proofs = self.pc_proof.proof.compressed_size();

        let num_evals = self.evaluations.len();
        let evals_size_in_bytes = self.evaluations.compressed_size();
        let num_prover_messages: usize = self
            .prover_messages
            .iter()
            .map(|v| match v {
                ProverMsg::EmptyMessage => 0,
                ProverMsg::FieldElements(elems) => elems.len(),
            })
            .sum();
        let prover_msg_size_in_bytes = self.prover_messages.compressed_size();
        let arg_size = self.compressed_size();
        let stats = format!(
            "Argument size in bytes: {}\n\n\
             Number of commitments without degree bounds: {}\n\
             Size (in bytes) of commitments without degree bounds: {}\n\
             Number of commitments with degree bounds: {}\n\
             Size (in bytes) of commitments with degree bounds: {}\n\n\
             Number of evaluation proofs: {}\n\
             Size (in bytes) of evaluation proofs: {}\n\n\
             Number of evaluations: {}\n\
             Size (in bytes) of evaluations: {}\n\n\
             Number of field elements in prover messages: {}\n\
             Size (in bytes) of prover message: {}\n",
            arg_size,
            num_comms_without_degree_bounds,
            size_bytes_comms_without_degree_bounds,
            num_comms_with_degree_bounds,
            size_bytes_comms_with_degree_bounds,
            num_proofs,
            size_bytes_proofs,
            num_evals,
            evals_size_in_bytes,
            num_prover_messages,
            prover_msg_size_in_bytes,
        );
        add_to_trace!(|| "Statistics about proof", || stats);
    }
}
