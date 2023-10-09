use crate::Vec;
use ark_crypto_primitives::sponge::poseidon::{
    find_poseidon_ark_and_mds, PoseidonConfig, PoseidonSponge,
};
use ark_crypto_primitives::sponge::{Absorb, CryptographicSponge};
use ark_ff::PrimeField;

use ark_std::rand::RngCore;

/// A simple `FiatShamirRng` that refreshes its seed by hashing together the previous seed
/// and the new seed material.
/// Exposes a particular instantiation of the Poseidon sponge

#[derive(Clone)]
pub struct SimplePoseidonRng<F: PrimeField>(PoseidonSponge<F>);

impl<F: PrimeField> RngCore for SimplePoseidonRng<F> {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        self.0
            .squeeze_bits(32)
            .iter()
            .rev()
            .fold(0, |acc, &bit| (acc << 1) | (bit as u32))
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        self.0
            .squeeze_bits(64)
            .iter()
            .rev()
            .fold(0, |acc, &bit| (acc << 1) | (bit as u64))
    }

    #[inline]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        dest.copy_from_slice(self.0.squeeze_bytes(dest.len()).as_slice());
    }

    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), ark_std::rand::Error> {
        Ok(self.fill_bytes(dest))
    }
}

impl<F: PrimeField> CryptographicSponge for SimplePoseidonRng<F> {
    type Config = PoseidonConfig<F>;

    fn new(params: &Self::Config) -> Self {
        Self(PoseidonSponge::new(params))
    }

    fn absorb(&mut self, input: &impl Absorb) {
        self.0.absorb(input);
    }

    fn squeeze_bytes(&mut self, num_bytes: usize) -> Vec<u8> {
        self.0.squeeze_bytes(num_bytes)
    }

    fn squeeze_bits(&mut self, num_bits: usize) -> Vec<bool> {
        self.0.squeeze_bits(num_bits)
    }
}

/// Instantiate Poseidon sponge with default parameters
impl<F: PrimeField> Default for SimplePoseidonRng<F> {
    fn default() -> Self {
        // let default =
        // Self(PoseidonSponge::new(&poseidon_parameters_for_test()))
        let (alpha, rate, full_rounds, partial_rounds) = (17, 2, 8, 29);
        let (ark, mds) = find_poseidon_ark_and_mds(
            F::MODULUS_BIT_SIZE as u64,
            rate,
            full_rounds,
            partial_rounds,
            0,
        );
        let config = PoseidonConfig {
            full_rounds: full_rounds as usize,
            partial_rounds: partial_rounds as usize,
            alpha: alpha as u64,
            ark,
            mds,
            rate,
            capacity: 1,
        };
        SimplePoseidonRng(PoseidonSponge::new(&config))
    }
}
