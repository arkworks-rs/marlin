use algebra::Field;
use r1cs_core::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};

#[derive(Copy, Clone)]
struct MySillyCircuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for MySillyCircuit<ConstraintF> {
    fn generate_constraints<CS: ConstraintSystem<ConstraintF>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
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

        cs.enforce(|| "one", |lc| lc + CS::one(), |lc| lc + CS::one(), |lc| lc + CS::one());
        cs.enforce(|| "first", |lc| lc + a, |lc| lc + b, |lc| lc + c);
        cs.enforce(|| "second", |lc| lc + a, |lc| lc + b, |lc| lc + c);
        cs.enforce(|| "third", |lc| lc + a, |lc| lc + b, |lc| lc + c);
        
        Ok(())
    }
}

mod marlin {
    use super::*;
    use crate::Marlin;

    use algebra::{curves::bls12_377::Bls12_377, fields::bls12_377::Fr};
    use rand::thread_rng;
    use algebra::UniformRand;
    use std::ops::MulAssign;
    use poly_commit::{multi_pc::mpc_from_spc::*, single_pc::kzg10::KZG10};
    use blake2::Blake2s;

    type MultiPC = MultiPCFromSinglePC<Fr, KZG10<Bls12_377>>;

    type MarlinInst = Marlin<Fr, MultiPC, Blake2s>;

    #[test]
    fn prove_and_verify() {
        let rng = &mut thread_rng();

        let (universal_pk, universal_vk) = MarlinInst::universal_setup(4, 4, 4, rng).unwrap();

        for _ in 0..100 {
            let a = Fr::rand(rng);
            let b = Fr::rand(rng);
            let mut c = a;
            c.mul_assign(&b);
            
            let circ = MySillyCircuit {
                a: Some(a),
                b: Some(b),
            };

            let (index_pk, index_vk) = MarlinInst::index(&universal_pk, circ.clone()).unwrap();

            let proof = MarlinInst::prove(&universal_pk, &index_pk, circ, rng).unwrap();

            assert!(MarlinInst::verify(&universal_vk, &index_vk, &[c], &proof, rng).unwrap());
            assert!(!MarlinInst::verify(&universal_vk, &index_vk, &[a], &proof, rng).unwrap());
        }
    }
}
