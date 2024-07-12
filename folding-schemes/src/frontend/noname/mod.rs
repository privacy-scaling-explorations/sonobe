use crate::Error;
use ark_noname::sonobe::NonameSonobeCircuit;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use num_bigint::BigUint;
use std::marker::PhantomData;

use self::utils::NonameInputs;

use super::FCircuit;
use ark_ff::PrimeField;
use ark_noname::utils::compile_source_code;
use noname::backends::{r1cs::R1CS as R1CSNoname, BackendField};
use noname::witness::CompiledCircuit;
pub mod utils;
#[derive(Debug, Clone)]
pub struct NonameFCircuit<F: PrimeField, BF: BackendField> {
    pub state_len: usize,
    pub external_inputs_len: usize,
    pub circuit: CompiledCircuit<R1CSNoname<BF>>,
    _f: PhantomData<F>,
}

impl<F: PrimeField, BF: BackendField> FCircuit<F> for NonameFCircuit<F, BF> {
    type Params = (String, usize, usize);

    fn new(params: Self::Params) -> Result<Self, crate::Error> {
        let (code, state_len, external_inputs_len) = params;
        let compiled_circuit = compile_source_code::<BF>(&code).map_err(|_| {
            Error::Other("Encountered an error while compiling a noname circuit".to_owned())
        })?;
        Ok(NonameFCircuit {
            state_len,
            external_inputs_len,
            circuit: compiled_circuit,
            _f: PhantomData,
        })
    }

    fn state_len(&self) -> usize {
        self.state_len
    }

    fn external_inputs_len(&self) -> usize {
        self.external_inputs_len
    }

    fn step_native(
        &self,
        _i: usize,
        z_i: Vec<F>,
        external_inputs: Vec<F>,
    ) -> Result<Vec<F>, crate::Error> {
        let wtns_external_inputs =
            NonameInputs::from((&external_inputs, "external_inputs".to_string()));
        let wtns_ivc_inputs = NonameInputs::from((&z_i, "ivc_inputs".to_string()));

        let noname_witness = self
            .circuit
            .generate_witness(wtns_ivc_inputs.0, wtns_external_inputs.0)
            .map_err(|e| Error::WitnessCalculationError(e.to_string()))?;

        let z_i1_end_index = z_i.len() + 1;
        let assigned_z_i1 = (1..z_i1_end_index)
            .map(|idx| {
                let value: BigUint = Into::into(noname_witness.witness[idx]);
                F::from(value)
            })
            .collect();

        Ok(assigned_z_i1)
    }

    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
        external_inputs: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let wtns_external_inputs =
            NonameInputs::from_fpvars((&external_inputs, "external_inputs".to_string()))?;
        let wtns_ivc_inputs = NonameInputs::from_fpvars((&z_i, "ivc_inputs".to_string()))?;
        let noname_witness = self
            .circuit
            .generate_witness(wtns_ivc_inputs.0, wtns_external_inputs.0)
            .map_err(|_| SynthesisError::Unsatisfiable)?;
        let z_i1_end_index = z_i.len() + 1;
        let assigned_z_i1: Vec<FpVar<F>> = (1..z_i1_end_index)
            .map(|idx| -> Result<FpVar<F>, SynthesisError> {
                // the assigned zi1 is of the same size than the initial zi and is located in the
                // output of the witness vector
                // we prefer to assign z_i1 here since (1) we have to return it, (2) we cant return
                // anything with the `generate_constraints` method used below
                let value: BigUint = Into::into(noname_witness.witness[idx]);
                let field_element = F::from(value);
                FpVar::<F>::new_witness(cs.clone(), || Ok(field_element))
            })
            .collect::<Result<Vec<FpVar<F>>, SynthesisError>>()?;

        let noname_circuit = NonameSonobeCircuit {
            compiled_circuit: self.circuit.clone(),
            witness: noname_witness,
            assigned_z_i: &z_i,
            assigned_external_inputs: &external_inputs,
            assigned_z_i1: &assigned_z_i1,
        };
        noname_circuit.generate_constraints(cs.clone())?;

        Ok(assigned_z_i1)
    }
}

#[cfg(test)]
mod tests {

    use ark_bn254::Fr;
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
    use noname::backends::r1cs::R1csBn254Field;

    use crate::frontend::FCircuit;

    use super::NonameFCircuit;
    use ark_relations::r1cs::ConstraintSystem;

    const NONAME_CIRCUIT_EXTERNAL_INPUTS: &str =
        "fn main(pub ivc_inputs: [Field; 2], external_inputs: [Field; 2]) -> [Field; 2] {
    let xx = external_inputs[0] + ivc_inputs[0];
    let yy = external_inputs[1] * ivc_inputs[1];
    assert_eq(yy, xx);
    return [xx, yy];
}";

    const NONAME_CIRCUIT_NO_EXTERNAL_INPUTS: &str =
        "fn main(pub ivc_inputs: [Field; 2]) -> [Field; 2] {
    let out = ivc_inputs[0] * ivc_inputs[1];
    return [out, ivc_inputs[1]];
}";

    #[test]
    fn test_step_native() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let params = (NONAME_CIRCUIT_EXTERNAL_INPUTS.to_owned(), 2, 2);
        let circuit = NonameFCircuit::<Fr, R1csBn254Field>::new(params).unwrap();
        let inputs_public = vec![Fr::from(2), Fr::from(5)];
        let inputs_private = vec![Fr::from(8), Fr::from(2)];

        let ivc_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(inputs_public.clone())).unwrap();
        let external_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(inputs_private.clone())).unwrap();

        let z_i1 = circuit
            .generate_step_constraints(cs.clone(), 0, ivc_inputs_var, external_inputs_var)
            .unwrap();
        let z_i1_native = circuit
            .step_native(0, inputs_public, inputs_private)
            .unwrap();

        assert_eq!(z_i1[0].value().unwrap(), z_i1_native[0]);
        assert_eq!(z_i1[1].value().unwrap(), z_i1_native[1]);
    }

    #[test]
    fn test_step_constraints() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let params = (NONAME_CIRCUIT_EXTERNAL_INPUTS.to_owned(), 2, 2);
        let circuit = NonameFCircuit::<Fr, R1csBn254Field>::new(params).unwrap();
        let inputs_public = vec![Fr::from(2), Fr::from(5)];
        let inputs_private = vec![Fr::from(8), Fr::from(2)];

        let ivc_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(inputs_public)).unwrap();
        let external_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(inputs_private)).unwrap();

        let z_i1 = circuit
            .generate_step_constraints(cs.clone(), 0, ivc_inputs_var, external_inputs_var)
            .unwrap();
        assert!(cs.is_satisfied().unwrap());
        assert_eq!(z_i1[0].value().unwrap(), Fr::from(10_u8));
        assert_eq!(z_i1[1].value().unwrap(), Fr::from(10_u8));
    }

    #[test]
    fn test_generate_constraints_no_external_inputs() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let params = (NONAME_CIRCUIT_NO_EXTERNAL_INPUTS.to_owned(), 2, 0);
        let inputs_public = vec![Fr::from(2), Fr::from(5)];

        let ivc_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(inputs_public)).unwrap();

        let f_circuit = NonameFCircuit::<Fr, R1csBn254Field>::new(params).unwrap();
        f_circuit
            .generate_step_constraints(cs.clone(), 0, ivc_inputs_var, vec![])
            .unwrap();
        assert!(cs.is_satisfied().unwrap());
    }
}
