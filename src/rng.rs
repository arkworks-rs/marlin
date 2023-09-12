use crate::Vec;
use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_crypto_primitives::sponge::poseidon::{PoseidonSponge, PoseidonConfig};
use ark_ff::{Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::convert::From;
use ark_std::marker::PhantomData;
use ark_std::rand::{RngCore, SeedableRng};
use digest::Digest;

/// A simple `FiatShamirRng` that refreshes its seed by hashing together the previous seed
/// and the new seed material.
/// Exposes a particular instantiation of the Poseidon sponge 

pub struct SimplePoseidonRng<F:PrimeField>(PoseidonSponge<F>);

impl<F:PrimeField> RngCore for SimplePoseidonRng<F> {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        self.0.squeeze_bits(32).iter().rev().fold(0, |acc, &bit| (acc << 1) | (bit as u32))
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        self.0.squeeze_bits(64).iter().rev().fold(0, |acc, &bit| (acc << 1) | (bit as u64))
    }

    #[inline]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0.squeeze_bytes(dest.len()).iter().enumerate().map(|(i, x)| dest[i] = *x );
    }

    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), ark_std::rand::Error> {
        Ok(self.fill_bytes(dest))
    }
}
