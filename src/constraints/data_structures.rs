use crate::ahp::prover::ProverMsg;
use crate::ahp::{CryptographicSpongeVarNonNative, CryptographicSpongeWithDefault};
use crate::{
    constraints::verifier::Marlin as MarlinVerifierVar,
    data_structures::{IndexVerifierKey, PreparedIndexVerifierKey, Proof},
    PrimeField, String, SynthesisError, ToString, Vec,
};
use ark_ff::{to_bytes, ToConstraintField};
use ark_nonnative_field::NonNativeFieldVar;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit::{PCCheckVar, PolynomialCommitment, PrepareGadget};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    fields::fp::FpVar,
    uint8::UInt8,
    R1CSVar, ToBytesGadget, ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace};
use ark_sponge::{Absorb, CryptographicSponge};
use ark_std::borrow::Borrow;
use hashbrown::HashMap;

pub type UniversalSRS<F, PC, S> =
    <PC as PolynomialCommitment<F, DensePolynomial<F>, S>>::UniversalParams;

pub struct IndexVerifierKeyVar<
    F: PrimeField,
    CF: PrimeField,
    S: CryptographicSponge,
    PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
    PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF, S>,
> {
    pub cs: ConstraintSystemRef<CF>,
    pub domain_h_size: u64,
    pub domain_k_size: u64,
    pub domain_h_size_gadget: FpVar<CF>,
    pub domain_k_size_gadget: FpVar<CF>,
    pub index_comms: Vec<PCG::CommitmentVar>,
    pub verifier_key: PCG::VerifierKeyVar,
}

impl<
        F: PrimeField,
        CF: PrimeField,
        S: CryptographicSponge,
        PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
        PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF, S>,
    > IndexVerifierKeyVar<F, CF, S, PC, PCG>
{
    fn cs(&self) -> ConstraintSystemRef<CF> {
        self.cs.clone()
    }
}

impl<
        F: PrimeField,
        CF: PrimeField,
        S: CryptographicSponge,
        PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
        PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF, S>,
    > AllocVar<IndexVerifierKey<F, S, PC>, CF> for IndexVerifierKeyVar<F, CF, S, PC, PCG>
{
    #[tracing::instrument(target = "r1cs", skip(cs, f))]
    fn new_variable<T>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError>
    where
        T: Borrow<IndexVerifierKey<F, S, PC>>,
    {
        let t = f()?;
        let ivk = t.borrow();

        let ns = cs.into();
        let cs = ns.cs();

        let mut index_comms = Vec::<PCG::CommitmentVar>::new();
        for index_comm in ivk.index_comms.iter() {
            index_comms.push(PCG::CommitmentVar::new_variable(
                ark_relations::ns!(cs, "index_comm"),
                || Ok(index_comm),
                mode,
            )?);
        }

        let verifier_key = PCG::VerifierKeyVar::new_variable(
            ark_relations::ns!(cs, "verifier_key"),
            || Ok(&ivk.verifier_key),
            mode,
        )?;

        let domain_h = GeneralEvaluationDomain::<F>::new(ivk.index_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k = GeneralEvaluationDomain::<F>::new(ivk.index_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_h_size_gadget = FpVar::<CF>::new_variable(
            ark_relations::ns!(cs, "domain_h_size"),
            || Ok(CF::from(domain_h.size() as u128)),
            mode,
        )?;
        let domain_k_size_gadget = FpVar::<CF>::new_variable(
            ark_relations::ns!(cs, "domain_k_size"),
            || Ok(CF::from(domain_k.size() as u128)),
            mode,
        )?;

        Ok(IndexVerifierKeyVar {
            cs,
            domain_h_size: domain_h.size() as u64,
            domain_k_size: domain_k.size() as u64,
            domain_h_size_gadget,
            domain_k_size_gadget,
            index_comms,
            verifier_key,
        })
    }
}

impl<
        F: PrimeField,
        CF: PrimeField,
        S: CryptographicSponge,
        PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
        PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF, S>,
    > ToBytesGadget<CF> for IndexVerifierKeyVar<F, CF, S, PC, PCG>
{
    #[tracing::instrument(target = "r1cs", skip(self))]
    fn to_bytes(&self) -> Result<Vec<UInt8<CF>>, SynthesisError> {
        let mut res = Vec::<UInt8<CF>>::new();

        res.append(&mut self.domain_h_size_gadget.to_bytes()?);
        res.append(&mut self.domain_k_size_gadget.to_bytes()?);
        res.append(&mut self.verifier_key.to_bytes()?);

        for comm in self.index_comms.iter() {
            res.append(&mut comm.to_bytes()?);
        }

        Ok(res)
    }
}

impl<
        F: PrimeField,
        CF: PrimeField,
        S: CryptographicSpongeWithDefault,
        PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
        PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF, S>,
    > Clone for IndexVerifierKeyVar<F, CF, S, PC, PCG>
{
    fn clone(&self) -> Self {
        Self {
            cs: self.cs.clone(),
            domain_h_size: self.domain_h_size,
            domain_k_size: self.domain_k_size,
            domain_h_size_gadget: self.domain_h_size_gadget.clone(),
            domain_k_size_gadget: self.domain_k_size_gadget.clone(),
            index_comms: self.index_comms.clone(),
            verifier_key: self.verifier_key.clone(),
        }
    }
}

impl<
        F: PrimeField,
        CF: PrimeField,
        S: CryptographicSponge,
        PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
        PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF, S>,
    > IndexVerifierKeyVar<F, CF, S, PC, PCG>
{
    pub fn iter(&self) -> impl Iterator<Item = &PCG::CommitmentVar> {
        self.index_comms.iter()
    }
}

pub struct PreparedIndexVerifierKeyVar<
    F: PrimeField,
    CF: PrimeField,
    S: CryptographicSponge,
    SVN: CryptographicSpongeVarNonNative<F, CF, S>,
    PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
    PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF, S>,
> {
    pub cs: ConstraintSystemRef<CF>,
    pub domain_h_size: u64,
    pub domain_k_size: u64,
    pub domain_h_size_gadget: FpVar<CF>,
    pub domain_k_size_gadget: FpVar<CF>,
    pub prepared_index_comms: Vec<PCG::PreparedCommitmentVar>,
    pub prepared_verifier_key: PCG::PreparedVerifierKeyVar,
    pub sponge_var: SVN,
}

impl<
        F: PrimeField,
        CF: PrimeField,
        S: CryptographicSponge,
        SVN: CryptographicSpongeVarNonNative<F, CF, S>,
        PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
        PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF, S>,
    > Clone for PreparedIndexVerifierKeyVar<F, CF, S, SVN, PC, PCG>
{
    fn clone(&self) -> Self {
        PreparedIndexVerifierKeyVar {
            cs: self.cs.clone(),
            domain_h_size: self.domain_h_size,
            domain_k_size: self.domain_k_size,
            domain_h_size_gadget: self.domain_h_size_gadget.clone(),
            domain_k_size_gadget: self.domain_k_size_gadget.clone(),
            prepared_index_comms: self.prepared_index_comms.clone(),
            prepared_verifier_key: self.prepared_verifier_key.clone(),
            sponge_var: self.sponge_var.clone(),
        }
    }
}

impl<F, CF, S, SVN, PC, PCG> PreparedIndexVerifierKeyVar<F, CF, S, SVN, PC, PCG>
where
    F: PrimeField,
    CF: PrimeField + Absorb,
    S: CryptographicSpongeWithDefault,
    SVN: CryptographicSpongeVarNonNative<F, CF, S>,
    PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
    PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF, S>,
    PCG::VerifierKeyVar: ToConstraintFieldGadget<CF>,
    PCG::CommitmentVar: ToConstraintFieldGadget<CF>,
{
    #[tracing::instrument(target = "r1cs", skip(vk))]
    pub fn prepare(vk: &IndexVerifierKeyVar<F, CF, S, PC, PCG>) -> Result<Self, SynthesisError> {
        let cs = vk.cs();
        let params = S::default_params();

        let index_vk_hash = {
            let mut vk_hash = S::new(&params);

            let mut vk_elems = Vec::<CF>::new();
            vk.index_comms.iter().for_each(|index_comm| {
                vk_elems.append(
                    &mut index_comm
                        .to_constraint_field()
                        .unwrap()
                        .iter()
                        .map(|elem| elem.value().unwrap_or_default())
                        .collect(),
                );
            });

            vk_hash.absorb(&vk_elems);

            FpVar::<CF>::new_witness(ark_relations::ns!(cs, "alloc#vk_hash"), || {
                Ok(vk_hash.squeeze_field_elements::<CF>(1)[0])
            })
            .unwrap()
        };

        let params = S::default_params();
        let mut sponge = S::new(&params);

        sponge.absorb(&to_bytes![&MarlinVerifierVar::<F, CF, S, PC, PCG>::PROTOCOL_NAME].unwrap());

        // FIXME Original call was `R::constant`
        let params_var = SVN::default_params();
        let mut sponge_var = SVN::new(cs, &params_var);

        sponge_var.absorb(&index_vk_hash)?;

        let mut prepared_index_comms = Vec::<PCG::PreparedCommitmentVar>::new();
        for comm in vk.index_comms.iter() {
            prepared_index_comms.push(PCG::PreparedCommitmentVar::prepare(comm)?);
        }

        let prepared_verifier_key = PCG::PreparedVerifierKeyVar::prepare(&vk.verifier_key)?;

        Ok(Self {
            cs: vk.cs.clone(),
            domain_h_size: vk.domain_h_size,
            domain_k_size: vk.domain_k_size,
            domain_h_size_gadget: vk.domain_h_size_gadget.clone(),
            domain_k_size_gadget: vk.domain_k_size_gadget.clone(),
            prepared_index_comms,
            prepared_verifier_key,
            sponge_var,
        })
    }
}

impl<F, CF, S, SVN, PC, PCG> AllocVar<PreparedIndexVerifierKey<F, S, PC>, CF>
    for PreparedIndexVerifierKeyVar<F, CF, S, SVN, PC, PCG>
where
    F: PrimeField,
    CF: PrimeField + Absorb,
    S: CryptographicSpongeWithDefault,
    SVN: CryptographicSpongeVarNonNative<F, CF, S>,
    PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
    PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF, S>,
    PC::VerifierKey: ToConstraintField<CF>,
    PC::Commitment: ToConstraintField<CF>,
    PCG::VerifierKeyVar: ToConstraintFieldGadget<CF>,
    PCG::CommitmentVar: ToConstraintFieldGadget<CF>,
{
    #[tracing::instrument(target = "r1cs", skip(cs, f))]
    fn new_variable<T>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError>
    where
        T: Borrow<PreparedIndexVerifierKey<F, S, PC>>,
    {
        let t = f()?;
        let obj = t.borrow();

        let ns = cs.into();
        let cs = ns.cs();

        let mut prepared_index_comms = Vec::<PCG::PreparedCommitmentVar>::new();
        for index_comm in obj.prepared_index_comms.iter() {
            prepared_index_comms.push(PCG::PreparedCommitmentVar::new_variable(
                ark_relations::ns!(cs, "index_comm"),
                || Ok(index_comm),
                mode,
            )?);
        }

        let prepared_verifier_key = PCG::PreparedVerifierKeyVar::new_variable(
            ark_relations::ns!(cs, "pvk"),
            || Ok(&obj.prepared_verifier_key),
            mode,
        )?;

        let mut vk_elems = Vec::<CF>::new();
        obj.orig_vk.index_comms.iter().for_each(|index_comm| {
            vk_elems.append(&mut index_comm.to_field_elements().unwrap());
        });

        let index_vk_hash = {
            let params = S::default_params();
            let mut vk_hash_rng = S::new(&params);

            vk_hash_rng.absorb(&vk_elems);

            FpVar::<CF>::new_variable(
                ark_relations::ns!(cs, "alloc#vk_hash"),
                || Ok(vk_hash_rng.squeeze_field_elements::<CF>(1)[0]),
                mode,
            )
            .unwrap()
        };

        let params = S::default_params();
        let mut sponge = S::new(&params);

        sponge.absorb(&to_bytes![&MarlinVerifierVar::<F, CF, S, PC, PCG>::PROTOCOL_NAME].unwrap());

        // FIXME Original call was `R::constant`
        let params_var = SVN::default_params();
        let mut sponge_var = SVN::new(cs.clone(), &params_var);

        sponge_var.absorb(&index_vk_hash)?;

        let domain_h_size_gadget = FpVar::<CF>::new_variable(
            ark_relations::ns!(cs, "domain_h_size"),
            || Ok(CF::from(obj.domain_h_size as u128)),
            mode,
        )?;

        let domain_k_size_gadget = FpVar::<CF>::new_variable(
            ark_relations::ns!(cs, "domain_k_size"),
            || Ok(CF::from(obj.domain_k_size as u128)),
            mode,
        )?;

        Ok(Self {
            cs,
            domain_h_size: obj.domain_h_size,
            domain_k_size: obj.domain_k_size,
            domain_h_size_gadget,
            domain_k_size_gadget,
            prepared_index_comms,
            prepared_verifier_key,
            sponge_var,
        })
    }
}

pub struct ProofVar<
    F: PrimeField,
    CF: PrimeField,
    S: CryptographicSponge,
    PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
    PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF, S>,
> {
    pub cs: ConstraintSystemRef<CF>,
    pub commitments: Vec<Vec<PCG::CommitmentVar>>,
    pub evaluations: HashMap<String, NonNativeFieldVar<F, CF>>,
    pub prover_messages: Vec<ProverMsgVar<F, CF>>,
    pub pc_batch_proof: PCG::BatchLCProofVar,
}

impl<
        F: PrimeField,
        CF: PrimeField,
        S: CryptographicSponge,
        PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
        PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF, S>,
    > ProofVar<F, CF, S, PC, PCG>
{
    pub fn new(
        cs: ConstraintSystemRef<CF>,
        commitments: Vec<Vec<PCG::CommitmentVar>>,
        evaluations: HashMap<String, NonNativeFieldVar<F, CF>>,
        prover_messages: Vec<ProverMsgVar<F, CF>>,
        pc_batch_proof: PCG::BatchLCProofVar,
    ) -> Self {
        Self {
            cs,
            commitments,
            evaluations,
            prover_messages,
            pc_batch_proof,
        }
    }
}

impl<F, CF, S, PC, PCG> AllocVar<Proof<F, S, PC>, CF> for ProofVar<F, CF, S, PC, PCG>
where
    F: PrimeField,
    CF: PrimeField,
    S: CryptographicSponge,
    PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
    PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF, S>,
    PC::VerifierKey: ToConstraintField<CF>,
    PC::Commitment: ToConstraintField<CF>,
    PCG::VerifierKeyVar: ToConstraintFieldGadget<CF>,
    PCG::CommitmentVar: ToConstraintFieldGadget<CF>,
{
    #[tracing::instrument(target = "r1cs", skip(cs, f))]
    fn new_variable<T>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError>
    where
        T: Borrow<Proof<F, S, PC>>,
    {
        let ns = cs.into();
        let cs = ns.cs();

        let t = f()?;
        let Proof {
            commitments,
            evaluations,
            prover_messages,
            pc_proof,
            ..
        } = t.borrow();

        let commitment_gadgets: Vec<Vec<PCG::CommitmentVar>> = commitments
            .iter()
            .map(|lst| {
                lst.iter()
                    .map(|comm| {
                        PCG::CommitmentVar::new_variable(
                            ark_relations::ns!(cs, "alloc#commitment"),
                            || Ok(comm),
                            mode,
                        )
                        .unwrap()
                    })
                    .collect()
            })
            .collect();

        let evaluation_gadgets_vec: Vec<NonNativeFieldVar<F, CF>> = evaluations
            .iter()
            .map(|eval| {
                NonNativeFieldVar::new_variable(
                    ark_relations::ns!(cs, "alloc#evaluation"),
                    || Ok(eval),
                    mode,
                )
                .unwrap()
            })
            .collect();

        let prover_message_gadgets: Vec<ProverMsgVar<F, CF>> = prover_messages
            .iter()
            .map(|msg| {
                let field_elements: Vec<NonNativeFieldVar<F, CF>> = match msg {
                    ProverMsg::EmptyMessage => Vec::new(),
                    ProverMsg::FieldElements(f) => f
                        .iter()
                        .map(|elem| {
                            NonNativeFieldVar::new_variable(
                                ark_relations::ns!(cs, "alloc#prover message"),
                                || Ok(elem),
                                mode,
                            )
                            .unwrap()
                        })
                        .collect(),
                };

                ProverMsgVar { field_elements }
            })
            .collect();

        let pc_batch_proof = PCG::BatchLCProofVar::new_variable(
            ark_relations::ns!(cs, "alloc#proof"),
            || Ok(pc_proof),
            mode,
        )
        .unwrap();

        let mut evaluation_gadgets = HashMap::<String, NonNativeFieldVar<F, CF>>::new();

        const ALL_POLYNOMIALS: [&str; 10] = [
            "a_denom",
            "b_denom",
            "c_denom",
            "g_1",
            "g_2",
            "t",
            "vanishing_poly_h_alpha",
            "vanishing_poly_h_beta",
            "vanishing_poly_k_gamma",
            "z_b",
        ];

        for (s, eval) in ALL_POLYNOMIALS.iter().zip(evaluation_gadgets_vec.iter()) {
            evaluation_gadgets.insert(s.to_string(), (*eval).clone());
        }

        Ok(ProofVar {
            cs,
            commitments: commitment_gadgets,
            evaluations: evaluation_gadgets,
            prover_messages: prover_message_gadgets,
            pc_batch_proof,
        })
    }
}

impl<
        F: PrimeField,
        CF: PrimeField,
        S: CryptographicSponge,
        PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
        PCG: PCCheckVar<F, DensePolynomial<F>, PC, CF, S>,
    > Clone for ProofVar<F, CF, S, PC, PCG>
{
    fn clone(&self) -> Self {
        ProofVar {
            cs: self.cs.clone(),
            commitments: self.commitments.clone(),
            evaluations: self.evaluations.clone(),
            prover_messages: self.prover_messages.clone(),
            pc_batch_proof: self.pc_batch_proof.clone(),
        }
    }
}

#[repr(transparent)]
pub struct ProverMsgVar<TargetField: PrimeField, BaseField: PrimeField> {
    pub field_elements: Vec<NonNativeFieldVar<TargetField, BaseField>>,
}

impl<TargetField: PrimeField, BaseField: PrimeField> Clone
    for ProverMsgVar<TargetField, BaseField>
{
    fn clone(&self) -> Self {
        ProverMsgVar {
            field_elements: self.field_elements.clone(),
        }
    }
}
