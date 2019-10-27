use algebra::Field;
use r1cs_core::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};

#[derive(Copy, Clone)]
struct Circuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
    num_constraints: usize,
    num_variables: usize,
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for Circuit<ConstraintF> {
    fn generate_constraints<CS: ConstraintSystem<ConstraintF>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let a = cs.alloc(|| "a", || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.alloc(|| "b", || self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.alloc_input(
            || "c",
            || {
                let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                a.mul_assign(&b);
                Ok(a)
            },
        )?;

        for i in 0..(self.num_variables - 3) {
            let _ = cs.alloc(|| format!("var {}", i), || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        }

        for i in 0..self.num_constraints {
            cs.enforce(|| format!("constraint {}", i), |lc| lc + a, |lc| lc + b, |lc| lc + c);
        }
        Ok(())
    }
}

mod marlin {
    use super::*;
    use crate::Marlin;

    use algebra::UniformRand;
    use algebra::{curves::bls12_377::Bls12_377, fields::bls12_377::Fr};
    use blake2::Blake2s;
    use poly_commit::{multi_pc::mpc_from_spc::*, single_pc::kzg10::KZG10};
    use std::ops::MulAssign;

    type MultiPC = MultiPCFromSinglePC<Fr, KZG10<Bls12_377>>;

    type MarlinInst = Marlin<Fr, MultiPC, Blake2s>;

    fn test_circuit(num_constraints: usize, num_variables: usize) {
        let rng = &mut rand_core::OsRng;

        let (universal_pk, universal_vk) = MarlinInst::universal_setup(100, 25, 100, rng).unwrap();

        for _ in 0..100 {
            let a = Fr::rand(rng);
            let b = Fr::rand(rng);
            let mut c = a;
            c.mul_assign(&b);

            let circ = Circuit { a: Some(a), b: Some(b), num_constraints, num_variables };

            let (index_pk, index_vk) = MarlinInst::index(&universal_pk, circ.clone()).unwrap();

            let proof = MarlinInst::prove(&universal_pk, &index_pk, circ, rng).unwrap();

            assert!(MarlinInst::verify(&universal_vk, &index_vk, &[c], &proof, rng).unwrap());
            println!("\nShould not verify (i.e. verifier messages should print below):");
            assert!(!MarlinInst::verify(&universal_vk, &index_vk, &[a], &proof, rng).unwrap());
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
