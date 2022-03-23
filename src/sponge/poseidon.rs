use core::marker::PhantomData;

use ark_ff::{FpParameters, PrimeField};
use ark_nonnative_field::{
    params::OptimizationType, AllocatedNonNativeFieldVar, NonNativeFieldVar,
};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::UInt8;
use ark_r1cs_std::{alloc::AllocVar, boolean::Boolean};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::AbsorbGadget;
use ark_sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonParameters, PoseidonSponge},
    CryptographicSponge,
};

use super::{CryptographicSpongeParameters, CryptographicSpongeVarNonNative};
use crate::{overhead, CryptographicSpongeWithRate};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PoseidonArguments<F: PrimeField> {
    pub prime_bits: u64,
    pub full_rounds: u32,
    pub partial_rounds: u32,
    pub skip_matrices: u64,

    _field: PhantomData<F>,
}

impl<F: PrimeField> PoseidonArguments<F> {
    pub const DEFAULT: Self = Self {
        prime_bits: F::Params::MODULUS_BITS as u64,
        full_rounds: 8,
        partial_rounds: 60,
        skip_matrices: 0,
        _field: PhantomData,
    };
}

impl<F: PrimeField> CryptographicSpongeWithRate for PoseidonSponge<F> {
    fn default_rate() -> usize {
        PoseidonParametersWithDefaultRate::<F>::DEFAULT_RATE
    }
}

impl<F: PrimeField> CryptographicSpongeParameters for PoseidonParameters<F> {
    fn from_rate(rate: usize) -> Self {
        PoseidonParametersWithDefaultRate::from_rate(rate).params
    }
}

impl<F: PrimeField, CF: PrimeField, S: CryptographicSponge>
    CryptographicSpongeVarNonNative<F, CF, S> for PoseidonSpongeVar<CF>
where
    PoseidonSpongeVar<CF>: CryptographicSpongeVar<CF, S>,
    <Self as CryptographicSpongeVar<CF, S>>::Parameters: CryptographicSpongeParameters,
{
    fn default_rate() -> usize {
        PoseidonParametersWithDefaultRate::<CF>::DEFAULT_RATE
    }

    fn absorb_nonnative(
        &mut self,
        input: &[NonNativeFieldVar<F, CF>],
        ty: OptimizationType,
    ) -> Result<(), SynthesisError> {
        let mut src_limbs: Vec<(FpVar<CF>, CF)> = Vec::new();

        for elem in input.iter() {
            match elem {
                NonNativeFieldVar::Constant(c) => {
                    let v = AllocatedNonNativeFieldVar::<F, CF>::new_constant(self.cs(), c)?;

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

        let capacity = CF::size_in_bits() - 1;
        let mut dest_limbs = Vec::<FpVar<CF>>::new();

        if !src_limbs.is_empty() {
            let params =
                ark_nonnative_field::params::get_params(F::size_in_bits(), CF::size_in_bits(), ty);

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

                let first_max_bits_per_limb =
                    params.bits_per_limb + overhead!(first.1 + &CF::one());
                let second_max_bits_per_limb = if second.is_some() {
                    params.bits_per_limb + overhead!(second.unwrap().1 + &CF::one())
                } else {
                    0
                };

                if second.is_some()
                    && first_max_bits_per_limb + second_max_bits_per_limb <= capacity
                {
                    let adjustment_factor =
                        &adjustment_factor_lookup_table[second_max_bits_per_limb];

                    dest_limbs.push(&first.0 * *adjustment_factor + &second.unwrap().0);
                    i += 2;
                } else {
                    dest_limbs.push(first.0.clone());
                    i += 1;
                }
            }
        }

        self.absorb(&dest_limbs)?;

        Ok(())
    }
}

/// Parameters and RNG used
#[derive(Clone, Debug)]
pub struct PoseidonParametersWithDefaultRate<F: PrimeField> {
    pub params: PoseidonParameters<F>,
}

impl<F: PrimeField> PoseidonParametersWithDefaultRate<F> {
    /// Default rate for poseidon
    pub const DEFAULT_RATE: usize = 4;
}

impl<F: PrimeField> From<PoseidonParameters<F>> for PoseidonParametersWithDefaultRate<F> {
    fn from(params: PoseidonParameters<F>) -> Self {
        Self { params }
    }
}

impl<F: PrimeField> CryptographicSpongeParameters for PoseidonParametersWithDefaultRate<F> {
    fn from_rate(rate: usize) -> Self {
        let PoseidonArguments {
            prime_bits,
            full_rounds,
            partial_rounds,
            skip_matrices,
            ..
        } = PoseidonArguments::<F>::DEFAULT;

        // TODO consume the arguments
        let capacity = 1;
        let alpha = 5;
        let _ = (rate, prime_bits, skip_matrices);

        // TODO generate secure constants
        let ark = F::one();
        let ark = vec![ark; 3];
        let ark = vec![ark; (full_rounds + partial_rounds) as usize];

        // TODO generate secure matrix
        let mds = F::one();
        let mds = vec![mds; rate + capacity];
        let mds = vec![mds; rate + capacity];

        PoseidonParameters::new(full_rounds, partial_rounds, alpha, mds, ark).into()
    }
}

#[derive(Clone)]
/// Wrapper for [`PoseidonSponge`]
pub struct PoseidonSpongeWithDefaultRate<F: PrimeField> {
    pub s: PoseidonSponge<F>,
}

impl<F: PrimeField> From<PoseidonSponge<F>> for PoseidonSpongeWithDefaultRate<F> {
    fn from(s: PoseidonSponge<F>) -> Self {
        Self { s }
    }
}

impl<F: PrimeField> CryptographicSponge for PoseidonSpongeWithDefaultRate<F> {
    type Parameters = PoseidonParametersWithDefaultRate<F>;

    fn new(p: &Self::Parameters) -> Self {
        PoseidonSponge::new(&p.params).into()
    }

    fn absorb(&mut self, input: &impl ark_sponge::Absorb) {
        self.s.absorb(input)
    }

    fn squeeze_bytes(&mut self, num_bytes: usize) -> Vec<u8> {
        self.s.squeeze_bytes(num_bytes)
    }

    fn squeeze_bits(&mut self, num_bits: usize) -> Vec<bool> {
        self.s.squeeze_bits(num_bits)
    }
}

impl<F: PrimeField> CryptographicSpongeWithRate for PoseidonSpongeWithDefaultRate<F> {
    fn default_rate() -> usize {
        PoseidonParametersWithDefaultRate::<F>::DEFAULT_RATE
    }
}

#[derive(Clone)]
/// Wrapper for [`PoseidonSpongeVar`]
pub struct PoseidonSpongeVarWithDefaultRate<CF: PrimeField> {
    pub s: PoseidonSpongeVar<CF>,
}

impl<CF: PrimeField> From<PoseidonSpongeVar<CF>> for PoseidonSpongeVarWithDefaultRate<CF> {
    fn from(s: PoseidonSpongeVar<CF>) -> Self {
        Self { s }
    }
}

impl<CF: PrimeField, S: CryptographicSponge> CryptographicSpongeVar<CF, S>
    for PoseidonSpongeVarWithDefaultRate<CF>
{
    type Parameters = PoseidonParametersWithDefaultRate<CF>;

    fn new(cs: ConstraintSystemRef<CF>, p: &Self::Parameters) -> Self {
        PoseidonSpongeVar::new(cs, &p.params).into()
    }

    fn cs(&self) -> ConstraintSystemRef<CF> {
        self.s.cs()
    }

    fn absorb(&mut self, input: &impl AbsorbGadget<CF>) -> Result<(), SynthesisError> {
        self.s.absorb(input)
    }

    fn squeeze_bytes(&mut self, num_bytes: usize) -> Result<Vec<UInt8<CF>>, SynthesisError> {
        self.s.squeeze_bytes(num_bytes)
    }

    fn squeeze_bits(&mut self, num_bits: usize) -> Result<Vec<Boolean<CF>>, SynthesisError> {
        self.s.squeeze_bits(num_bits)
    }

    fn squeeze_field_elements(
        &mut self,
        num_elements: usize,
    ) -> Result<Vec<FpVar<CF>>, SynthesisError> {
        self.s.squeeze_field_elements(num_elements)
    }
}

impl<F: PrimeField, CF: PrimeField, S: CryptographicSponge>
    CryptographicSpongeVarNonNative<F, CF, S> for PoseidonSpongeVarWithDefaultRate<CF>
{
    fn default_rate() -> usize {
        PoseidonParametersWithDefaultRate::<CF>::DEFAULT_RATE
    }

    fn absorb_nonnative(
        &mut self,
        input: &[NonNativeFieldVar<F, CF>],
        ty: OptimizationType,
    ) -> Result<(), SynthesisError> {
        self.s.absorb_nonnative(input, ty)
    }
}
