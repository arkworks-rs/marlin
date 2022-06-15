use ark_ff::PrimeField;
use ark_nonnative_field::{params::OptimizationType, NonNativeFieldVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::{constraints::CryptographicSpongeVar, CryptographicSponge};

pub mod poseidon;

pub trait CryptographicSpongeParameters {
    fn from_rate(rate: usize) -> Self;
}

pub trait CryptographicSpongeWithRate: CryptographicSponge
where
    <Self as CryptographicSponge>::Parameters: CryptographicSpongeParameters,
{
    fn default_rate() -> usize;

    fn with_default_rate() -> Self {
        let rate = Self::default_rate();

        Self::from_rate(rate)
    }

    fn from_rate(rate: usize) -> Self {
        let params =
            <<Self as CryptographicSponge>::Parameters as CryptographicSpongeParameters>::from_rate(
                rate,
            );

        <Self as CryptographicSponge>::new(&params)
    }
}

pub trait CryptographicSpongeVarNonNative<F: PrimeField, CF: PrimeField, S: CryptographicSponge>:
    CryptographicSpongeVar<CF, S>
where
    <Self as CryptographicSpongeVar<CF, S>>::Parameters: CryptographicSpongeParameters,
{
    fn default_rate() -> usize;

    fn with_default_rate(cs: ConstraintSystemRef<CF>) -> Self {
        let rate = Self::default_rate();

        Self::from_rate(cs, rate)
    }

    fn from_rate(cs: ConstraintSystemRef<CF>, rate: usize) -> Self {
        let params =
            <<Self as CryptographicSpongeVar<CF, S>>::Parameters as CryptographicSpongeParameters>::from_rate(
                rate,
            );

        <Self as CryptographicSpongeVar<CF, S>>::new(cs, &params)
    }

    /// Absorb non native elements
    fn absorb_nonnative(
        &mut self,
        input: &[NonNativeFieldVar<F, CF>],
        ty: OptimizationType,
    ) -> Result<(), SynthesisError>;
}
