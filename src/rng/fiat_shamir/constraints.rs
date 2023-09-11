use crate::rng::CryptographicSpongeVarNonNative;
use crate::rng::CryptographicSpongeParameters;
use crate::{overhead,Vec};
use ark_ff::PrimeField;
use ark_r1cs_std::fields::nonnative::params::{get_params, OptimizationType};
use ark_r1cs_std::fields::nonnative::{AllocatedNonNativeFieldVar, NonNativeFieldVar};
use ark_r1cs_std::{
    alloc::AllocVar,
    bits::{uint8::UInt8, ToBitsGadget},
    boolean::Boolean,
    fields::fp::AllocatedFp,
    fields::fp::FpVar,
    R1CSVar,
};
use ark_relations::lc;
use ark_relations::r1cs::{
    ConstraintSystemRef, LinearCombination, OptimizationGoal, SynthesisError,
};
use ark_crypto_primitives::sponge::constraints::{AbsorbGadget, CryptographicSpongeVar};
use ark_crypto_primitives::sponge::CryptographicSponge;
use core::marker::PhantomData;

/// Vars for a RNG for use in a Fiat-Shamir transform.
pub trait FiatShamirRngVar<F: PrimeField, CF: PrimeField, S: CryptographicSponge>:
    From<ConstraintSystemRef<CF>> + CryptographicSpongeVar<CF, S>
{
    // Instantiate from a plaintext fs_rng.
    fn constant(cs: ConstraintSystemRef<CF>, pfs: &S) -> Self;

    /// Take in field elements.
    fn absorb_nonnative(
        &mut self,
        elems: &[NonNativeFieldVar<F, CF>],
        ty: OptimizationType,
    ) -> Result<(), SynthesisError>;

    /// Take in field elements.
    fn absorb_native(&mut self, elems: &[FpVar<CF>]) -> Result<(), SynthesisError>;

    /// Take in bytes.
    fn absorb_bytes(&mut self, elems: &[UInt8<CF>]) -> Result<(), SynthesisError>;

    /// Output field elements.
    fn squeeze_native(&mut self, num: usize) -> Result<Vec<FpVar<CF>>, SynthesisError>;

    /// Output field elements.
    fn squeeze_nonnative(
        &mut self,
        num: usize,
    ) -> Result<Vec<NonNativeFieldVar<F, CF>>, SynthesisError>;

    /// Output field elements with only 128 bits.
    fn squeeze_128_bits_nonnative(
        &mut self,
        num: usize,
    ) -> Result<Vec<NonNativeFieldVar<F, CF>>, SynthesisError>;

    /// Output field elements with only 128 bits, and the corresponding bits (this can reduce
    /// repeated computation).
    #[allow(clippy::type_complexity)]
    fn squeeze_128_bits_nonnative_and_bits(
        &mut self,
        num: usize,
    ) -> Result<(Vec<NonNativeFieldVar<F, CF>>, Vec<Vec<Boolean<CF>>>), SynthesisError>;
}

/// Building the Fiat-Shamir sponge's gadget from any algebraic sponge's gadget.
#[derive(Clone)]
pub struct FiatShamirSpongeRngVar<
    F: PrimeField,
    CF: PrimeField,
    PS: CryptographicSponge,
    S: CryptographicSpongeVar<CF, PS>,
> {
    pub cs: ConstraintSystemRef<CF>,
    pub s: S,
    #[doc(hidden)]
    f_phantom: PhantomData<F>,
    cf_phantom: PhantomData<CF>,
    ps_phantom: PhantomData<PS>,
}

impl<F: PrimeField, CF: PrimeField, PS: CryptographicSponge, S: CryptographicSpongeVar<CF, PS>>
    FiatShamirSpongeRngVar<F, CF, PS, S>
{
    /// Compress every two elements if possible. Provides a vector of (limb, num_of_additions),
    /// both of which are CF.
    #[tracing::instrument(target = "r1cs")]
    pub fn compress_gadgets(
        src_limbs: &[(FpVar<CF>, CF)],
        ty: OptimizationType,
    ) -> Result<Vec<FpVar<CF>>, SynthesisError> {
        let capacity = CF::size_in_bits() - 1;
        let mut dest_limbs = Vec::<FpVar<CF>>::new();

        if src_limbs.is_empty() {
            return Ok(vec![]);
        }

        let params = get_params(F::size_in_bits(), CF::size_in_bits(), ty);

        let adjustment_factor_lookup_table = {
            let mut table = Vec::<CF>::new();

            let mut cur = CF::one();
            for _ in 1..=capacity {
                table.push(cur);
                cur.double_in_place();
            }

            table
        };

        let mut i: usize = 0;
        let src_len = src_limbs.len();
        while i < src_len {
            let first = &src_limbs[i];
            let second = if i + 1 < src_len {
                Some(&src_limbs[i + 1])
            } else {
                None
            };

            let first_max_bits_per_limb = params.bits_per_limb + overhead!(first.1 + &CF::one());
            let second_max_bits_per_limb = if second.is_some() {
                params.bits_per_limb + overhead!(second.unwrap().1 + &CF::one())
            } else {
                0
            };

            if second.is_some() && first_max_bits_per_limb + second_max_bits_per_limb <= capacity {
                let adjustment_factor = &adjustment_factor_lookup_table[second_max_bits_per_limb];

                dest_limbs.push(&first.0 * *adjustment_factor + &second.unwrap().0);
                i += 2;
            } else {
                dest_limbs.push(first.0.clone());
                i += 1;
            }
        }

        Ok(dest_limbs)
    }

    /// Push gadgets to sponge.
    #[tracing::instrument(target = "r1cs", skip(sponge))]
    pub fn push_gadgets_to_sponge(
        sponge: &mut S,
        src: &[NonNativeFieldVar<F, CF>],
        ty: OptimizationType,
    ) -> Result<(), SynthesisError> {
        let mut src_limbs: Vec<(FpVar<CF>, CF)> = Vec::new();

        for elem in src.iter() {
            match elem {
                NonNativeFieldVar::Constant(c) => {
                    let v = AllocatedNonNativeFieldVar::<F, CF>::new_constant(sponge.cs(), c)?;

                    for limb in v.limbs.iter() {
                        let num_of_additions_over_normal_form =
                            if v.num_of_additions_over_normal_form == CF::zero() {
                                CF::one()
                            } else {
                                v.num_of_additions_over_normal_form
                            };
                        src_limbs.push((limb.clone(), num_of_additions_over_normal_form));
                    }
                }
                NonNativeFieldVar::Var(v) => {
                    for limb in v.limbs.iter() {
                        let num_of_additions_over_normal_form =
                            if v.num_of_additions_over_normal_form == CF::zero() {
                                CF::one()
                            } else {
                                v.num_of_additions_over_normal_form
                            };
                        src_limbs.push((limb.clone(), num_of_additions_over_normal_form));
                    }
                }
            }
        }

        let dest_limbs = Self::compress_gadgets(&src_limbs, ty)?;
        sponge.absorb(&dest_limbs)?;
        Ok(())
    }

    /// Obtain random bits from hashchain gadget. (Not guaranteed to be uniformly distributed,
    /// should only be used in certain situations.)
    #[tracing::instrument(target = "r1cs", skip(sponge))]
    pub fn get_booleans_from_sponge(
        sponge: &mut S,
        num_bits: usize,
    ) -> Result<Vec<Boolean<CF>>, SynthesisError> {
        let bits_per_element = CF::size_in_bits() - 1;
        let num_elements = (num_bits + bits_per_element - 1) / bits_per_element;

        let src_elements = sponge.squeeze_field_elements(num_elements)?;
        let mut dest_bits = Vec::<Boolean<CF>>::new();

        for elem in src_elements.iter() {
            let elem_bits = elem.to_bits_be()?;
            dest_bits.extend_from_slice(&elem_bits[1..]); // discard the highest bit
        }

        Ok(dest_bits)
    }

    /// Obtain random elements from hashchain gadget. (Not guaranteed to be uniformly distributed,
    /// should only be used in certain situations.)
    #[tracing::instrument(target = "r1cs", skip(sponge))]
    pub fn get_gadgets_from_sponge(
        sponge: &mut S,
        num_elements: usize,
        outputs_short_elements: bool,
    ) -> Result<Vec<NonNativeFieldVar<F, CF>>, SynthesisError> {
        let (dest_gadgets, _) =
            Self::get_gadgets_and_bits_from_sponge(sponge, num_elements, outputs_short_elements)?;

        Ok(dest_gadgets)
    }

    /// Obtain random elements, and the corresponding bits, from hashchain gadget. (Not guaranteed
    /// to be uniformly distributed, should only be used in certain situations.)
    #[tracing::instrument(target = "r1cs", skip(sponge))]
    #[allow(clippy::type_complexity)]
    pub fn get_gadgets_and_bits_from_sponge(
        sponge: &mut S,
        num_elements: usize,
        outputs_short_elements: bool,
    ) -> Result<(Vec<NonNativeFieldVar<F, CF>>, Vec<Vec<Boolean<CF>>>), SynthesisError> {
        let cs = sponge.cs();

        let optimization_type = match cs.optimization_goal() {
            OptimizationGoal::None => OptimizationType::Constraints,
            OptimizationGoal::Constraints => OptimizationType::Constraints,
            OptimizationGoal::Weight => OptimizationType::Weight,
        };

        let params = get_params(F::size_in_bits(), CF::size_in_bits(), optimization_type);

        let num_bits_per_nonnative = if outputs_short_elements {
            128
        } else {
            F::size_in_bits() - 1 // also omit the highest bit
        };
        let bits = Self::get_booleans_from_sponge(sponge, num_bits_per_nonnative * num_elements)?;

        let mut lookup_table = Vec::<Vec<CF>>::new();
        let mut cur = F::one();
        for _ in 0..num_bits_per_nonnative {
            let repr = AllocatedNonNativeFieldVar::<F, CF>::get_limbs_representations(
                &cur,
                optimization_type,
            )?;
            lookup_table.push(repr);
            cur.double_in_place();
        }

        let mut dest_gadgets = Vec::<NonNativeFieldVar<F, CF>>::new();
        let mut dest_bits = Vec::<Vec<Boolean<CF>>>::new();
        bits.chunks_exact(num_bits_per_nonnative)
            .for_each(|per_nonnative_bits| {
                let mut val = vec![CF::zero(); params.num_limbs];
                let mut lc = vec![LinearCombination::<CF>::zero(); params.num_limbs];

                let mut per_nonnative_bits_le = per_nonnative_bits.to_vec();
                per_nonnative_bits_le.reverse();

                dest_bits.push(per_nonnative_bits_le.clone());

                for (j, bit) in per_nonnative_bits_le.iter().enumerate() {
                    if bit.value().unwrap_or_default() {
                        for (k, val) in val.iter_mut().enumerate().take(params.num_limbs) {
                            *val += &lookup_table[j][k];
                        }
                    }

                    #[allow(clippy::needless_range_loop)]
                    for k in 0..params.num_limbs {
                        lc[k] = &lc[k] + bit.lc() * lookup_table[j][k];
                    }
                }

                let mut limbs = Vec::new();
                for k in 0..params.num_limbs {
                    let gadget =
                        AllocatedFp::new_witness(ark_relations::ns!(cs, "alloc"), || Ok(val[k]))
                            .unwrap();
                    lc[k] = lc[k].clone() - (CF::one(), gadget.variable);
                    cs.enforce_constraint(lc!(), lc!(), lc[k].clone()).unwrap();
                    limbs.push(FpVar::<CF>::from(gadget));
                }

                dest_gadgets.push(NonNativeFieldVar::<F, CF>::Var(
                    AllocatedNonNativeFieldVar::<F, CF> {
                        cs: cs.clone(),
                        limbs,
                        num_of_additions_over_normal_form: CF::zero(),
                        is_in_the_normal_form: true,
                        target_phantom: Default::default(),
                    },
                ));
            });

        Ok((dest_gadgets, dest_bits))
    }
}

impl<
        F: PrimeField,
        CF: PrimeField,
        PS: CryptographicSponge,
        S: CryptographicSpongeVarNonNative<F, CF, PS>,
    > From<ConstraintSystemRef<CF>> for FiatShamirSpongeRngVar<F, CF, PS, S>
where
    <S as CryptographicSpongeVar<CF, PS>>::Parameters: CryptographicSpongeParameters,
{
    fn from(cs: ConstraintSystemRef<CF>) -> Self {
        Self {
            cs: cs.clone(),
            s: S::with_default_rate(cs),
            f_phantom: PhantomData,
            cf_phantom: PhantomData,
            ps_phantom: PhantomData,
        }
    }
}

impl<F: PrimeField, CF: PrimeField, PS: CryptographicSponge, S: CryptographicSpongeVar<CF, PS>>
    CryptographicSpongeVar<CF, PS> for FiatShamirSpongeRngVar<F, CF, PS, S>
{
    type Parameters = S::Parameters;

    fn new(cs: ConstraintSystemRef<CF>, params: &Self::Parameters) -> Self {
        Self {
            cs: cs.clone(),
            s: S::new(cs, params),
            f_phantom: PhantomData,
            cf_phantom: PhantomData,
            ps_phantom: PhantomData,
        }
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    fn cs(&self) -> ConstraintSystemRef<CF> {
        self.cs.clone()
    }

    fn absorb(&mut self, input: &impl AbsorbGadget<CF>) -> Result<(), SynthesisError> {
        self.s.absorb(input)
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    fn squeeze_bytes(&mut self, num_bytes: usize) -> Result<Vec<UInt8<CF>>, SynthesisError> {
        self.s.squeeze_bytes(num_bytes)
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    fn squeeze_bits(&mut self, num_bits: usize) -> Result<Vec<Boolean<CF>>, SynthesisError> {
        self.s.squeeze_bits(num_bits)
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    fn squeeze_field_elements(
        &mut self,
        num_elements: usize,
    ) -> Result<Vec<FpVar<CF>>, SynthesisError> {
        self.s.squeeze_field_elements(num_elements)
    }
}

impl<
        F: PrimeField,
        CF: PrimeField,
        PS: CryptographicSponge,
        S: CryptographicSpongeVarNonNative<F, CF, PS>,
    > FiatShamirRngVar<F, CF, PS> for FiatShamirSpongeRngVar<F, CF, PS, S>
where
    <S as CryptographicSpongeVar<CF, PS>>::Parameters: CryptographicSpongeParameters,
{
    fn constant(cs: ConstraintSystemRef<CF>, _pfs: &PS) -> Self {
        Self::from(cs)
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    fn absorb_nonnative(
        &mut self,
        elems: &[NonNativeFieldVar<F, CF>],
        ty: OptimizationType,
    ) -> Result<(), SynthesisError> {
        Self::push_gadgets_to_sponge(&mut self.s, &elems.to_vec(), ty)
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    fn absorb_native(&mut self, elems: &[FpVar<CF>]) -> Result<(), SynthesisError> {
        self.absorb(&elems)
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    fn absorb_bytes(&mut self, elems: &[UInt8<CF>]) -> Result<(), SynthesisError> {
        self.absorb(&elems)
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    fn squeeze_native(&mut self, num: usize) -> Result<Vec<FpVar<CF>>, SynthesisError> {
        self.s.squeeze_field_elements(num)
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    fn squeeze_nonnative(
        &mut self,
        num: usize,
    ) -> Result<Vec<NonNativeFieldVar<F, CF>>, SynthesisError> {
        Self::get_gadgets_from_sponge(&mut self.s, num, false)
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    fn squeeze_128_bits_nonnative(
        &mut self,
        num: usize,
    ) -> Result<Vec<NonNativeFieldVar<F, CF>>, SynthesisError> {
        Self::get_gadgets_from_sponge(&mut self.s, num, true)
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    fn squeeze_128_bits_nonnative_and_bits(
        &mut self,
        num: usize,
    ) -> Result<(Vec<NonNativeFieldVar<F, CF>>, Vec<Vec<Boolean<CF>>>), SynthesisError> {
        Self::get_gadgets_and_bits_from_sponge(&mut self.s, num, true)
    }
}
