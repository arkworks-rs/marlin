// For benchmark, run:
//     RAYON_NUM_THREADS=N cargo bench --no-default-features --features "std parallel" -- --nocapture
// where N is the number of threads you want to use (N = 1 for single-thread).

use ark_bls12_381::{Bls12_381, Fr as BlsFr};

use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_ff::PrimeField;
use ark_marlin::{Marlin, SimplePoseidonRng};
use ark_mnt4_298::{Fr as MNT4Fr, MNT4_298};
use ark_mnt4_753::{Fr as MNT4BigFr, MNT4_753};
use ark_mnt6_298::{Fr as MNT6Fr, MNT6_298};
use ark_mnt6_753::{Fr as MNT6BigFr, MNT6_753};
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::sonic_pc::SonicKZG10;
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
};
use ark_std::{ops::Mul, rand::RngCore};
use itertools::Itertools;

const NUM_PROVE_REPEATITIONS: usize = 10;
const NUM_VERIFY_REPEATITIONS: usize = 50;

#[derive(Copy)]
struct DummyCircuit<F: PrimeField> {
    pub a: Option<F>,
    pub b: Option<F>,
    pub num_variables: usize,
    pub num_constraints: usize,
}

impl<F: PrimeField> Clone for DummyCircuit<F> {
    fn clone(&self) -> Self {
        DummyCircuit {
            a: self.a.clone(),
            b: self.b.clone(),
            num_variables: self.num_variables.clone(),
            num_constraints: self.num_constraints.clone(),
        }
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for DummyCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

            Ok(a * b)
        })?;

        for _ in 0..(self.num_variables - 3) {
            let _ = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        }

        for _ in 0..self.num_constraints - 1 {
            cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        }

        cs.enforce_constraint(lc!(), lc!(), lc!())?;

        Ok(())
    }
}

macro_rules! marlin_prove_bench {
    ($bench_name:ident, $bench_field:ty, $bench_pairing_engine:ty) => {
        let mut rng_seed = ark_std::test_rng();
        let mut rng: SimplePoseidonRng<$bench_field> = SimplePoseidonRng::default();
        rng.absorb(&rng_seed.next_u64());
        let (a, b) = rng
            .squeeze_field_elements(2)
            .iter()
            .map(|x: &$bench_field| x.to_owned())
            .collect_tuple()
            .unwrap();
        let c = DummyCircuit::<$bench_field> {
            a: Some(a),
            b: Some(b),
            num_variables: 10,
            num_constraints: 65536,
        };

        let srs = Marlin::<
            $bench_field,
            SonicKZG10<
                $bench_pairing_engine,
                DensePolynomial<$bench_field>,
                SimplePoseidonRng<$bench_field>,
            >,
            SimplePoseidonRng<$bench_field>,
        >::universal_setup(65536, 65536, 3 * 65536, &mut rng)
        .unwrap();
        let (pk, _) = Marlin::<
            $bench_field,
            SonicKZG10<
                $bench_pairing_engine,
                DensePolynomial<$bench_field>,
                SimplePoseidonRng<$bench_field>,
            >,
            SimplePoseidonRng<$bench_field>,
        >::index(&srs, c)
        .unwrap();

        let start = ark_std::time::Instant::now();

        for _ in 0..NUM_PROVE_REPEATITIONS {
            let _ = Marlin::<
                $bench_field,
                SonicKZG10<
                    $bench_pairing_engine,
                    DensePolynomial<$bench_field>,
                    SimplePoseidonRng<$bench_field>,
                >,
                SimplePoseidonRng<$bench_field>,
            >::prove(&pk, c.clone(), &mut rng)
            .unwrap();
        }

        println!(
            "per-constraint proving time for {}: {} ns/constraint",
            stringify!($bench_pairing_engine),
            start.elapsed().as_nanos() / NUM_PROVE_REPEATITIONS as u128 / 65536u128
        );
    };
}

macro_rules! marlin_verify_bench {
    ($bench_name:ident, $bench_field:ty, $bench_pairing_engine:ty) => {
        let mut rng_seed = ark_std::test_rng();
        let mut rng: SimplePoseidonRng<$bench_field> = SimplePoseidonRng::default();
        rng.absorb(&rng_seed.next_u64());
        let (a, b) = rng
            .squeeze_field_elements(2)
            .iter()
            .map(|x: &$bench_field| x.to_owned())
            .collect_tuple()
            .unwrap();
        let c = DummyCircuit::<$bench_field> {
            a: Some(a),
            b: Some(b),
            num_variables: 10,
            num_constraints: 65536,
        };

        let srs = Marlin::<
            $bench_field,
            SonicKZG10<
                $bench_pairing_engine,
                DensePolynomial<$bench_field>,
                SimplePoseidonRng<$bench_field>,
            >,
            SimplePoseidonRng<$bench_field>,
        >::universal_setup(65536, 65536, 3 * 65536, &mut rng)
        .unwrap();
        let (pk, vk) = Marlin::<
            $bench_field,
            SonicKZG10<
                $bench_pairing_engine,
                DensePolynomial<$bench_field>,
                SimplePoseidonRng<$bench_field>,
            >,
            SimplePoseidonRng<$bench_field>,
        >::index(&srs, c)
        .unwrap();
        let proof = Marlin::<
            $bench_field,
            SonicKZG10<
                $bench_pairing_engine,
                DensePolynomial<$bench_field>,
                SimplePoseidonRng<$bench_field>,
            >,
            SimplePoseidonRng<$bench_field>,
        >::prove(&pk, c.clone(), &mut rng)
        .unwrap();

        let v = c.a.unwrap().mul(c.b.unwrap());

        let start = ark_std::time::Instant::now();

        for _ in 0..NUM_VERIFY_REPEATITIONS {
            let _ = Marlin::<
                $bench_field,
                SonicKZG10<
                    $bench_pairing_engine,
                    DensePolynomial<$bench_field>,
                    SimplePoseidonRng<$bench_field>,
                >,
                SimplePoseidonRng<$bench_field>,
            >::verify(&vk, &vec![v], &proof, &mut rng)
            .unwrap();
        }

        println!(
            "verifying time for {}: {} ns",
            stringify!($bench_pairing_engine),
            start.elapsed().as_nanos() / NUM_VERIFY_REPEATITIONS as u128
        );
    };
}

fn bench_prove() {
    marlin_prove_bench!(bls, BlsFr, Bls12_381);
    marlin_prove_bench!(mnt4, MNT4Fr, MNT4_298);
    marlin_prove_bench!(mnt6, MNT6Fr, MNT6_298);
    marlin_prove_bench!(mnt4big, MNT4BigFr, MNT4_753);
    marlin_prove_bench!(mnt6big, MNT6BigFr, MNT6_753);
}

fn bench_verify() {
    marlin_verify_bench!(bls, BlsFr, Bls12_381);
    marlin_verify_bench!(mnt4, MNT4Fr, MNT4_298);
    marlin_verify_bench!(mnt6, MNT6Fr, MNT6_298);
    marlin_verify_bench!(mnt4big, MNT4BigFr, MNT4_753);
    marlin_verify_bench!(mnt6big, MNT6BigFr, MNT6_753);
}

fn main() {
    bench_prove();
    bench_verify();
}
