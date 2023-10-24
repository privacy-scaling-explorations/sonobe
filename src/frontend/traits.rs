use crate::ccs::{CCS, r1cs::R1CS};
use crate::frontend::circom::CircomWrapper;
use crate::frontend::arkworks::extract_r1cs_and_z;

use num_bigint::BigInt;
use ark_ec::CurveGroup;
use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_relations::r1cs::ConstraintSystem;
use std::{error::Error, vec::Vec};

// Define a Frontend trait
pub trait Frontend<C: CurveGroup, F: PrimeField> {
    fn extract_r1cs_and_z(&self, inputs: &[(String, Vec<BigInt>)]) -> Result<(R1CS<C::ScalarField>, Vec<C::ScalarField>), Box<dyn Error>>;
    
    fn extract_ccs_and_z(&self, inputs:&[(String, Vec<BigInt>)]) -> Result<(CCS<C>, Vec<C::ScalarField>), Box<dyn Error>>;
}

// Implement Frontend trait for Arkworks
impl<C: CurveGroup<ScalarField = F>, F: PrimeField> Frontend<C, F> for ConstraintSystem<F>
where C::ScalarField: PrimeField {
    fn extract_r1cs_and_z(&self, _inputs: &[(String, Vec<BigInt>)]) -> Result<(R1CS<C::ScalarField>, Vec<C::ScalarField>), Box<dyn Error>> {
        Ok(extract_r1cs_and_z(self))
    }

    fn extract_ccs_and_z(&self, _inputs: &[(String, Vec<BigInt>)]) -> Result<(CCS<C>, Vec<C::ScalarField>), Box<dyn Error>> {
        let (r1cs, z) = extract_r1cs_and_z(self);
        let ccs = CCS::from_r1cs(r1cs);
        Ok((ccs, z))
    }
}

// Implement Frontend trait for Circom
impl<E: Pairing, F: PrimeField> Frontend<E::G1, F> for CircomWrapper<E> {
    fn extract_r1cs_and_z(&self, inputs: &[(String, Vec<BigInt>)]) -> Result<(R1CS<E::ScalarField>, Vec<E::ScalarField>), Box<dyn Error>> {
        self.extract_r1cs_and_z(inputs)
    }
    
    fn extract_ccs_and_z(&self, inputs: &[(String, Vec<BigInt>)]) -> Result<(CCS<E::G1>, Vec<E::ScalarField>), Box<dyn Error>> {
        let result = self.extract_r1cs_and_z(inputs)?;
        let (r1cs, z) = result;
        let ccs = CCS::from_r1cs(r1cs);
        Ok((ccs, z))
    }    
}

#[cfg(test)]
mod frontend_tests {
    use super::*;
    use ark_bn254::Bn254;
    use std::env;
    use ark_pallas::{Fr, Projective};
    use crate::frontend::arkworks::tests::TestCircuit;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
    use ark_ff::Field;

    fn test_frontend_trait_logic<C: CurveGroup, F: PrimeField>(frontend: &dyn Frontend<C, F>, expect_success: bool, inputs: Vec<(String, Vec<BigInt>)>){
        // R1CS
        let (r1cs, z_r1cs) = frontend
            .extract_r1cs_and_z(&inputs)
            .expect("Error processing input");

        let r1cs_check_result = r1cs.check_relation(&z_r1cs);

        // CCS
        let (ccs, z_ccs) = frontend
            .extract_ccs_and_z(&inputs)
            .expect("Error processing input");

        let ccs_check_result = ccs.check_relation(&z_ccs);

        match (expect_success, r1cs_check_result, ccs_check_result) {
            (true, Ok(_), Ok(_)) => {}, 
            (false, Err(_), _) | (false, _, Err(_)) => {}, 
            (true, _, Err(_)) | (true, Err(_), _) => panic!("Expected success but got a failure for either R1CS or CCS."),
            (false, Ok(_), Ok(_)) => panic!("Expected a failure but got success for both R1CS and CCS.")        
        }
    }

    fn load_circom_wrapper_as_frontend<F: PrimeField>() -> Box<dyn Frontend<<Bn254 as Pairing>::G1, F>> {
        let current_dir = env::current_dir().unwrap();
        let base_path = current_dir.join("src/frontend/circom/test_folder");
        let r1cs_filepath = base_path.join("test_circuit.r1cs");
        let wasm_filepath = base_path.join("test_circuit_js/test_circuit.wasm");

        assert!(r1cs_filepath.exists());
        assert!(wasm_filepath.exists());

        Box::new(CircomWrapper::<Bn254>::new(r1cs_filepath, wasm_filepath))
    }

    #[test]
    fn test_frontend_trait_for_circom() {
        let frontend: Box<dyn Frontend<<Bn254 as Pairing>::G1, Fr>> = load_circom_wrapper_as_frontend();

        test_frontend_trait_logic(&*frontend, true, vec![("step_in".to_string(), vec![BigInt::from(3)])]);
        test_frontend_trait_logic(&*frontend, false, vec![("step_in".to_string(), vec![BigInt::from(7)])]);
    }

    #[test]
    fn test_frontend_trait_for_arkworks() {
        let cs_ref = ConstraintSystem::<Fr>::new_ref();
        let x = Fr::from(3_u32);
        let y = x * x * x + x + Fr::from(5_u32);
        let test_circuit = TestCircuit::<Fr> { x, y };
        test_circuit.generate_constraints(cs_ref.clone()).unwrap();
        cs_ref.finalize();
        assert!(cs_ref.is_satisfied().unwrap());
    
        let cs = cs_ref.into_inner().unwrap();
    
        let frontend: &dyn Frontend<Projective, Fr> = &cs;
    
        let (r1cs, z_r1cs) = frontend.extract_r1cs_and_z(&[].as_slice()).unwrap();
        r1cs.check_relation(&z_r1cs).unwrap();
    
        let (ccs, z_ccs) = frontend.extract_ccs_and_z(&[].as_slice()).unwrap();
        ccs.check_relation(&z_ccs[..]).unwrap();
    }
}