use ark_ff::Field;
use ark_relations::lc;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};

#[derive(Copy, Clone)]
struct Circuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
    num_constraints: usize,
    num_variables: usize,
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for Circuit<ConstraintF> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

            a.mul_assign(&b);
            Ok(a)
        })?;

        for _ in 0..(self.num_variables - 3) {
            let _ = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        }

        for _ in 0..self.num_constraints {
            cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        }
        Ok(())
    }
}

mod marlin {
    use super::*;
    use crate::{fiat_shamir::FiatShamirChaChaRng, Marlin, MarlinDefaultConfig};

    use ark_bls12_381::{Bls12_381, Fq, Fr};
    use ark_ff::UniformRand;
    use ark_poly_commit::marlin_pc::MarlinKZG10;
    use blake2::Blake2s;
    use core::ops::MulAssign;

    type MultiPC = MarlinKZG10<Bls12_381>;
    type MarlinInst =
        Marlin<Fr, Fq, MultiPC, FiatShamirChaChaRng<Fr, Fq, Blake2s>, MarlinDefaultConfig>;

    fn test_circuit(num_constraints: usize, num_variables: usize) {
        let rng = &mut ark_ff::test_rng();

        let universal_srs = MarlinInst::universal_setup(100, 25, 100, rng).unwrap();

        for _ in 0..100 {
            let a = Fr::rand(rng);
            let b = Fr::rand(rng);
            let mut c = a;
            c.mul_assign(&b);

            let circ = Circuit {
                a: Some(a),
                b: Some(b),
                num_constraints,
                num_variables,
            };

            let (index_pk, index_vk) = MarlinInst::index(&universal_srs, circ).unwrap();
            println!("Called index");

            let proof = MarlinInst::prove(&index_pk, circ, rng).unwrap();
            println!("Called prover");

            assert!(MarlinInst::verify(&index_vk, &[c], &proof).unwrap());
            println!("Called verifier");
            println!("\nShould not verify (i.e. verifier messages should print below):");
            assert!(!MarlinInst::verify(&index_vk, &[a], &proof).unwrap());
        }
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_big() {
        let num_constraints = 100;
        let num_variables = 25;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_small() {
        let num_constraints = 26;
        let num_variables = 25;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_big() {
        let num_constraints = 25;
        let num_variables = 100;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_small() {
        let num_constraints = 25;
        let num_variables = 26;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_square_matrix() {
        let num_constraints = 25;
        let num_variables = 25;

        test_circuit(num_constraints, num_variables);
    }
}

mod marlin_recursion {
    use super::*;
    use crate::{
        fiat_shamir::{poseidon::PoseidonSponge, FiatShamirAlgebraicSpongeRng},
        Marlin, MarlinRecursiveConfig,
    };

    use ark_ec::CycleEngine;
    use ark_ff::UniformRand;
    use ark_mnt4_298::{Fq, Fr, MNT4_298};
    use ark_mnt6_298::MNT6_298;
    use ark_poly_commit::marlin_pc::MarlinKZG10;
    use core::ops::MulAssign;

    type MultiPC = MarlinKZG10<MNT4_298>;
    type MarlinInst = Marlin<
        Fr,
        Fq,
        MultiPC,
        FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq>>,
        MarlinRecursiveConfig,
    >;

    #[derive(Copy, Clone, Debug)]
    struct MNT298Cycle;
    impl CycleEngine for MNT298Cycle {
        type E1 = MNT6_298;
        type E2 = MNT4_298;
    }

    fn test_circuit(num_constraints: usize, num_variables: usize) {
        let rng = &mut ark_ff::test_rng();

        let universal_srs = MarlinInst::universal_setup(100, 25, 100, rng).unwrap();

        for _ in 0..100 {
            let a = Fr::rand(rng);
            let b = Fr::rand(rng);
            let mut c = a;
            c.mul_assign(&b);

            let circ = Circuit {
                a: Some(a),
                b: Some(b),
                num_constraints,
                num_variables,
            };

            let (index_pk, index_vk) = MarlinInst::index(&universal_srs, circ).unwrap();
            println!("Called index");

            let proof = MarlinInst::prove(&index_pk, circ, rng).unwrap();
            println!("Called prover");

            assert!(MarlinInst::verify(&index_vk, &[c], &proof).unwrap());
            println!("Called verifier");
            println!("\nShould not verify (i.e. verifier messages should print below):");
            assert!(!MarlinInst::verify(&index_vk, &[a], &proof).unwrap());
        }
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_big() {
        let num_constraints = 100;
        let num_variables = 25;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_small() {
        let num_constraints = 26;
        let num_variables = 25;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_big() {
        let num_constraints = 25;
        let num_variables = 100;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_small() {
        let num_constraints = 25;
        let num_variables = 26;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_square_matrix() {
        let num_constraints = 25;
        let num_variables = 25;

        test_circuit(num_constraints, num_variables);
    }
}

mod fiat_shamir {
    use crate::fiat_shamir::constraints::FiatShamirRngVar;
    use crate::fiat_shamir::{
        constraints::FiatShamirAlgebraicSpongeRngVar,
        poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge},
        FiatShamirAlgebraicSpongeRng, FiatShamirChaChaRng, FiatShamirRng,
    };
    use ark_ff::{PrimeField, UniformRand};
    use ark_mnt4_298::{Fq, Fr};
    use ark_nonnative_field::NonNativeFieldVar;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::bits::uint8::UInt8;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSystemRef};
    use blake2::Blake2s;

    const NUM_ABSORBED_RAND_FIELD_ELEMS: usize = 10;
    const NUM_ABSORBED_RAND_BYTE_ELEMS: usize = 10;
    const SIZE_ABSORBED_BYTE_ELEM: usize = 64;

    const NUM_SQUEEZED_FIELD_ELEMS: usize = 10;
    const NUM_SQUEEZED_SHORT_FIELD_ELEMS: usize = 10;

    #[test]
    fn test_chacharng() {
        let rng = &mut ark_ff::test_rng();

        let mut absorbed_rand_field_elems = Vec::new();
        for _ in 0..NUM_ABSORBED_RAND_FIELD_ELEMS {
            absorbed_rand_field_elems.push(Fr::rand(rng));
        }

        let mut absorbed_rand_byte_elems = Vec::<Vec<u8>>::new();
        for _ in 0..NUM_ABSORBED_RAND_BYTE_ELEMS {
            absorbed_rand_byte_elems.push(
                (0..SIZE_ABSORBED_BYTE_ELEM)
                    .map(|_| u8::rand(rng))
                    .collect(),
            );
        }

        let mut fs_rng = FiatShamirChaChaRng::<Fr, Fq, Blake2s>::new();
        fs_rng.absorb_nonnative_field_elements(&absorbed_rand_field_elems);
        for absorbed_rand_byte_elem in absorbed_rand_byte_elems {
            fs_rng.absorb_bytes(&absorbed_rand_byte_elem);
        }

        let _squeezed_fields_elems =
            fs_rng.squeeze_nonnative_field_elements(NUM_SQUEEZED_FIELD_ELEMS);
        let _squeezed_short_fields_elems =
            fs_rng.squeeze_128_bits_nonnative_field_elements(NUM_SQUEEZED_SHORT_FIELD_ELEMS);
    }

    #[test]
    fn test_poseidon() {
        let rng = &mut ark_ff::test_rng();

        let mut absorbed_rand_field_elems = Vec::new();
        for _ in 0..NUM_ABSORBED_RAND_FIELD_ELEMS {
            absorbed_rand_field_elems.push(Fr::rand(rng));
        }

        let mut absorbed_rand_byte_elems = Vec::<Vec<u8>>::new();
        for _ in 0..NUM_ABSORBED_RAND_BYTE_ELEMS {
            absorbed_rand_byte_elems.push(
                (0..SIZE_ABSORBED_BYTE_ELEM)
                    .map(|_| u8::rand(rng))
                    .collect(),
            );
        }

        // fs_rng in the plaintext world
        let mut fs_rng = FiatShamirAlgebraicSpongeRng::<Fr, Fq, PoseidonSponge<Fq>>::new();

        fs_rng.absorb_nonnative_field_elements(&absorbed_rand_field_elems);

        for absorbed_rand_byte_elem in &absorbed_rand_byte_elems {
            fs_rng.absorb_bytes(absorbed_rand_byte_elem);
        }

        let squeezed_fields_elems =
            fs_rng.squeeze_nonnative_field_elements(NUM_SQUEEZED_FIELD_ELEMS);
        let squeezed_short_fields_elems =
            fs_rng.squeeze_128_bits_nonnative_field_elements(NUM_SQUEEZED_SHORT_FIELD_ELEMS);

        // fs_rng in the constraint world
        let cs_sys = ConstraintSystem::<Fq>::new();
        let cs = ConstraintSystemRef::new(cs_sys);
        let mut fs_rng_gadget = FiatShamirAlgebraicSpongeRngVar::<
            Fr,
            Fq,
            PoseidonSponge<Fq>,
            PoseidonSpongeVar<Fq>,
        >::new(ark_relations::ns!(cs, "new").cs());

        let mut absorbed_rand_field_elems_gadgets = Vec::new();
        for absorbed_rand_field_elem in absorbed_rand_field_elems.iter() {
            absorbed_rand_field_elems_gadgets.push(
                NonNativeFieldVar::<Fr, Fq>::new_constant(
                    ark_relations::ns!(cs, "alloc elem"),
                    absorbed_rand_field_elem,
                )
                .unwrap(),
            );
        }
        fs_rng_gadget
            .absorb_nonnative_field_elements(&absorbed_rand_field_elems_gadgets)
            .unwrap();

        let mut absorbed_rand_byte_elems_gadgets = Vec::<Vec<UInt8<Fq>>>::new();
        for absorbed_rand_byte_elem in absorbed_rand_byte_elems.iter() {
            let mut byte_gadget = Vec::<UInt8<Fq>>::new();
            for byte in absorbed_rand_byte_elem.iter() {
                byte_gadget
                    .push(UInt8::new_constant(ark_relations::ns!(cs, "alloc byte"), byte).unwrap());
            }
            absorbed_rand_byte_elems_gadgets.push(byte_gadget);
        }
        for absorbed_rand_byte_elems_gadget in absorbed_rand_byte_elems_gadgets.iter() {
            fs_rng_gadget
                .absorb_bytes(absorbed_rand_byte_elems_gadget)
                .unwrap();
        }

        let squeezed_fields_elems_gadgets = fs_rng_gadget
            .squeeze_field_elements(NUM_SQUEEZED_FIELD_ELEMS)
            .unwrap();

        let squeezed_short_fields_elems_gadgets = fs_rng_gadget
            .squeeze_128_bits_field_elements(NUM_SQUEEZED_SHORT_FIELD_ELEMS)
            .unwrap();

        // compare elems
        for (i, (left, right)) in squeezed_fields_elems
            .iter()
            .zip(squeezed_fields_elems_gadgets.iter())
            .enumerate()
        {
            assert_eq!(
                left.into_repr(),
                right.value().unwrap().into_repr(),
                "{}: left = {:?}, right = {:?}",
                i,
                left.into_repr(),
                right.value().unwrap().into_repr()
            );
        }

        // compare short elems
        for (i, (left, right)) in squeezed_short_fields_elems
            .iter()
            .zip(squeezed_short_fields_elems_gadgets.iter())
            .enumerate()
        {
            assert_eq!(
                left.into_repr(),
                right.value().unwrap().into_repr(),
                "{}: left = {:?}, right = {:?}",
                i,
                left.into_repr(),
                right.value().unwrap().into_repr()
            );
        }

        if !cs.is_satisfied().unwrap() {
            println!("\n=========================================================");
            println!("\nUnsatisfied constraints:");
            println!("\n{:?}", cs.which_is_unsatisfied().unwrap());
            println!("\n=========================================================");
        }
        assert!(cs.is_satisfied().unwrap());
    }
}
