use crate::Vec;
use ark_ff::{FromBytes, ToBytes};
use ark_std::convert::From;
use ark_std::marker::PhantomData;
use ark_std::rand::{RngCore, SeedableRng};
use digest::Digest;

/// An RNG suitable for Fiat-Shamir transforms
pub trait FiatShamirRng: RngCore {
    /// Create a new `Self` with an initial input
    fn initialize<'a, T: 'a + ToBytes>(initial_input: &'a T) -> Self;
    /// Absorb new inputs into state
    fn absorb<'a, T: 'a + ToBytes>(&mut self, new_input: &'a T);
}

/// A simple `FiatShamirRng` that refreshes its seed by hashing together the previous seed
/// and the new seed material.
pub struct SimpleHashFiatShamirRng<D: Digest, R: RngCore + SeedableRng> {
    r: R,
    seed: [u8; 32],
    #[doc(hidden)]
    digest: PhantomData<D>,
}

impl<D: Digest, R: RngCore + SeedableRng> RngCore for SimpleHashFiatShamirRng<D, R> {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        self.r.next_u32()
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        self.r.next_u64()
    }

    #[inline]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.r.fill_bytes(dest);
    }

    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), ark_std::rand::Error> {
        Ok(self.r.fill_bytes(dest))
    }
}

impl<D: Digest, R: RngCore + SeedableRng> FiatShamirRng for SimpleHashFiatShamirRng<D, R>
where
    R::Seed: From<[u8; 32]>,
{
    /// Create a new `Self` by initializing with a fresh seed.
    /// `self.seed = H(initial_input)`.
    #[inline]
    fn initialize<'a, T: 'a + ToBytes>(initial_input: &'a T) -> Self {
        let mut bytes = Vec::new();
        initial_input
            .write(&mut bytes)
            .expect("failed to convert to bytes");
        let seed = FromBytes::read(D::digest(&bytes).as_ref()).expect("failed to get [u8; 32]");
        let r = R::from_seed(<R::Seed>::from(seed));
        Self {
            r,
            seed: seed,
            digest: PhantomData,
        }
    }

    /// Refresh `self.seed` with new material. Achieved by setting
    /// `self.seed = H(new_input || self.seed)`.
    #[inline]
    fn absorb<'a, T: 'a + ToBytes>(&mut self, new_input: &'a T) {
        let mut bytes = Vec::new();
        new_input
            .write(&mut bytes)
            .expect("failed to convert to bytes");
        bytes.extend_from_slice(&self.seed);
        self.seed = FromBytes::read(D::digest(&bytes).as_ref()).expect("failed to get [u8; 32]");
        self.r = R::from_seed(<R::Seed>::from(self.seed));
    }
}
