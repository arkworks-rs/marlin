use ark_ff::Field;
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
};
use ark_std::marker::PhantomData;

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
        let d = cs.new_input_variable(|| {
            let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

            a.mul_assign(&b);
            a.mul_assign(&b);
            Ok(a)
        })?;

        for _ in 0..(self.num_variables - 3) {
            let _ = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        }

        for _ in 0..(self.num_constraints - 1) {
            cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        }
        cs.enforce_constraint(lc!() + c, lc!() + b, lc!() + d)?;

        Ok(())
    }
}

#[derive(Clone)]
/// Define a constraint system that would trigger outlining.
struct OutlineTestCircuit<F: Field> {
    field_phantom: PhantomData<F>,
}

impl<F: Field> ConstraintSynthesizer<F> for OutlineTestCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        // This program checks if the input elements are between 0 and 9.
        //
        // Note that this constraint system is neither the most intuitive way nor
        // the most efficient way for such a task. It is for testing purposes,
        // as we want to trigger the outlining.
        //
        let mut inputs = Vec::new();
        for i in 0..5 {
            inputs.push(cs.new_input_variable(|| Ok(F::from(i as u128)))?);
        }

        for i in 0..5 {
            let mut total_count_for_this_input = cs.new_lc(lc!()).unwrap();

            for bucket in 0..10 {
                let count_increment_for_this_bucket =
                    cs.new_witness_variable(|| Ok(F::from(i == bucket)))?;

                total_count_for_this_input = cs
                    .new_lc(
                        lc!()
                            + (F::one(), total_count_for_this_input)
                            + (F::one(), count_increment_for_this_bucket.clone()),
                    )
                    .unwrap();

                // Only when `input[i]` equals `bucket` can `count_increment_for_this_bucket` be nonzero.
                //
                // A malicious prover can make `count_increment_for_this_bucket` neither 0 nor 1.
                // But the constraint on `total_count_for_this_input` will reject such case.
                //
                // At a high level, only one of the `count_increment_for_this_bucket` among all the buckets
                // could be nonzero, which equals `total_count_for_this_input`. Thus, by checking whether
                // `total_count_for_this_input` is 1, we know this input number is in the range.
                //
                cs.enforce_constraint(
                    lc!() + (F::one(), inputs[i].clone())
                        - (F::from(bucket as u128), ark_relations::r1cs::Variable::One),
                    lc!() + (F::one(), count_increment_for_this_bucket),
                    lc!(),
                )?;
            }

            // Enforce `total_count_for_this_input` to be one.
            cs.enforce_constraint(
                lc!(),
                lc!(),
                lc!() + (F::one(), total_count_for_this_input.clone())
                    - (F::one(), ark_relations::r1cs::Variable::One),
            )?;
        }

        Ok(())
    }
}

mod marlin {
    use super::*;
    use crate::{Marlin, MarlinDefaultConfig};

    use ark_bls12_381::{Bls12_381, Fq, Fr};
    use ark_ff::UniformRand;
    use ark_poly::univariate::DensePolynomial;
    use ark_poly_commit::marlin_pc::MarlinKZG10;
    use ark_std::ops::MulAssign;
    use blake2::Blake2s;

    type MultiPC = MarlinKZG10<Bls12_381, DensePolynomial<Fr>, PoseidonSponge<Fr>>;
    type MarlinInst = Marlin<
        Fr,
        Fq,
        PoseidonSponge<Fr>,
        MultiPC,
        FiatShamirChaChaRng<Fr, Fq, Blake2s>,
        MarlinDefaultConfig,
    >;

    fn test_circuit(num_constraints: usize, num_variables: usize) {
        let rng = &mut ark_std::test_rng();

        let universal_srs = MarlinInst::universal_setup(100, 25, 100, rng).unwrap();

        for _ in 0..100 {
            let a = Fr::rand(rng);
            let b = Fr::rand(rng);
            let mut c = a;
            c.mul_assign(&b);
            let mut d = c;
            d.mul_assign(&b);

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

            assert!(MarlinInst::verify(&index_vk, &[c, d], &proof).unwrap());
            println!("Called verifier");
            println!("\nShould not verify (i.e. verifier messages should print below):");
            assert!(!MarlinInst::verify(&index_vk, &[a, a], &proof).unwrap());
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
    use crate::{Marlin, MarlinRecursiveConfig};

    use ark_ec::{CurveCycle, PairingEngine, PairingFriendlyCycle};
    use ark_ff::UniformRand;
    use ark_mnt4_298::{Fq, Fr, MNT4_298};
    use ark_mnt6_298::MNT6_298;
    use ark_poly::polynomial::univariate::DensePolynomial;
    use ark_poly_commit::marlin_pc::MarlinKZG10;
    use core::ops::MulAssign;

    type MultiPC = MarlinKZG10<MNT4_298, DensePolynomial<Fr>, PoseidonSponge<Fr>>;
    type MarlinInst = Marlin<
        Fr,
        Fq,
        PoseidonSponge<Fr>,
        MultiPC,
        FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq>>,
        MarlinRecursiveConfig,
    >;

    #[derive(Copy, Clone, Debug)]
    struct MNT298Cycle;
    impl CurveCycle for MNT298Cycle {
        type E1 = <MNT6_298 as PairingEngine>::G1Affine;
        type E2 = <MNT4_298 as PairingEngine>::G1Affine;
    }
    impl PairingFriendlyCycle for MNT298Cycle {
        type Engine1 = MNT6_298;
        type Engine2 = MNT4_298;
    }

    fn test_circuit(num_constraints: usize, num_variables: usize) {
        let rng = &mut ark_std::test_rng();

        let universal_srs = MarlinInst::universal_setup(100, 25, 100, rng).unwrap();

        for _ in 0..100 {
            let a = Fr::rand(rng);
            let b = Fr::rand(rng);
            let mut c = a;
            c.mul_assign(&b);
            let mut d = c;
            d.mul_assign(&b);

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

            assert!(MarlinInst::verify(&index_vk, &[c, d], &proof).unwrap());
            println!("Called verifier");
            println!("\nShould not verify (i.e. verifier messages should print below):");
            assert!(!MarlinInst::verify(&index_vk, &[a, a], &proof).unwrap());
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

    #[test]
    /// Test on a constraint system that will trigger outlining.
    fn prove_and_test_outlining() {
        let rng = &mut ark_std::test_rng();

        let universal_srs = MarlinInst::universal_setup(150, 150, 150, rng).unwrap();

        let circ = OutlineTestCircuit {
            field_phantom: PhantomData,
        };

        let (index_pk, index_vk) = MarlinInst::index(&universal_srs, circ.clone()).unwrap();
        println!("Called index");

        let proof = MarlinInst::prove(&index_pk, circ, rng).unwrap();
        println!("Called prover");

        let mut inputs = Vec::new();
        for i in 0u128..5u128 {
            inputs.push(Fr::from(i));
        }

        assert!(MarlinInst::verify(&index_vk, &inputs, &proof).unwrap());
        println!("Called verifier");
    }
}

mod fiat_shamir {
    use ark_ff::PrimeField;
    use ark_mnt4_298::{Fq, Fr};
    use ark_nonnative_field::params::OptimizationType;
    use ark_nonnative_field::NonNativeFieldVar;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::bits::uint8::UInt8;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSystemRef, OptimizationGoal};
    use ark_std::UniformRand;
    use blake2::Blake2s;

    const NUM_ABSORBED_RAND_FIELD_ELEMS: usize = 10;
    const NUM_ABSORBED_RAND_BYTE_ELEMS: usize = 10;
    const SIZE_ABSORBED_BYTE_ELEM: usize = 64;

    const NUM_SQUEEZED_FIELD_ELEMS: usize = 10;
    const NUM_SQUEEZED_SHORT_FIELD_ELEMS: usize = 10;

    #[test]
    fn test_chacharng() {
        let rng = &mut ark_std::test_rng();

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
        fs_rng
            .absorb_nonnative_field_elements(&absorbed_rand_field_elems, OptimizationType::Weight);
        for absorbed_rand_byte_elem in absorbed_rand_byte_elems {
            fs_rng.absorb_bytes(&absorbed_rand_byte_elem);
        }

        let _squeezed_fields_elems = fs_rng
            .squeeze_nonnative_field_elements(NUM_SQUEEZED_FIELD_ELEMS, OptimizationType::Weight);
        let _squeezed_short_fields_elems =
            fs_rng.squeeze_128_bits_nonnative_field_elements(NUM_SQUEEZED_SHORT_FIELD_ELEMS);
    }

    #[test]
    fn test_poseidon() {
        let rng = &mut ark_std::test_rng();

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

        fs_rng
            .absorb_nonnative_field_elements(&absorbed_rand_field_elems, OptimizationType::Weight);

        for absorbed_rand_byte_elem in &absorbed_rand_byte_elems {
            fs_rng.absorb_bytes(absorbed_rand_byte_elem);
        }

        let squeezed_fields_elems = fs_rng
            .squeeze_nonnative_field_elements(NUM_SQUEEZED_FIELD_ELEMS, OptimizationType::Weight);
        let squeezed_short_fields_elems =
            fs_rng.squeeze_128_bits_nonnative_field_elements(NUM_SQUEEZED_SHORT_FIELD_ELEMS);

        // fs_rng in the constraint world
        let cs_sys = ConstraintSystem::<Fq>::new();
        let cs = ConstraintSystemRef::new(cs_sys);
        cs.set_optimization_goal(OptimizationGoal::Weight);
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
            .absorb_nonnative_field_elements(
                &absorbed_rand_field_elems_gadgets,
                OptimizationType::Weight,
            )
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
