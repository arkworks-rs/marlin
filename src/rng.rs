use algebra::{ToBytes, FromBytes};
use generic_array::GenericArray;
use digest::Digest;
use rand::{SeedableRng, Rng, ChaChaRng, Rand};
use std::marker::PhantomData;



/// A `SeedableRng` that refreshes its seed by hashing together the previous seed
/// and the new seed material.
// TODO: later: re-evaluate decision about ChaChaRng
pub struct FiatShamirRng<D: Digest> {
    r: ChaChaRng,
    seed:  GenericArray<u8, D::OutputSize>,
    #[doc(hidden)]
    digest: PhantomData<D>,
}

impl<D: Digest> Rng for FiatShamirRng<D> {
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
    fn gen<T: Rand>(&mut self) -> T
    where
        Self: Sized,
    {
        self.r.gen()
    }
}
impl<D: Digest> FiatShamirRng<D> {
    /// Refresh `self.seed` with new material. Achieved by setting 
    /// `self.seed = H(self.seed || new_seed)`.
    #[inline]
    pub fn absorb<'a, T: 'a + ToBytes>(&mut self, seed: &'a T) {
        let mut bytes = Vec::new();
        seed.write(&mut bytes).expect("failed to convert to bytes");
        bytes.extend_from_slice(&self.seed);
        self.seed = D::digest(&bytes);
        let seed: [u32; 4] = FromBytes::read(self.seed.as_ref()).expect("failed to get [u32; 8]");
        self.r.reseed(&seed);
    }
}

impl<'a, D: Digest, T: 'a + ToBytes> SeedableRng<&'a T> for FiatShamirRng<D> {
    #[inline]
    fn reseed(&mut self, seed: &'a T) {
        let mut bytes = Vec::new();
        seed.write(&mut bytes).expect("failed to convert to bytes");
        bytes.extend_from_slice(&self.seed);
        self.seed = D::digest(&bytes);
        let seed: [u32; 4] = FromBytes::read(self.seed.as_ref()).expect("failed to get [u32; 8]");
        self.r.reseed(&seed);
    }

    #[inline]
    fn from_seed(seed: &'a T) -> Self {
        let mut bytes = Vec::new();
        seed.write(&mut bytes).expect("failed to convert to bytes");
        let seed = D::digest(&bytes);
        let r_seed: [u32; 4] = FromBytes::read(seed.as_ref()).expect("failed to get [u32; 8]");
        let r = ChaChaRng::from_seed(&r_seed);
        Self {
            r,
            seed,
            digest: PhantomData,
        }
    }
}
