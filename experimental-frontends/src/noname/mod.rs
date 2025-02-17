use ark_ff::PrimeField;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use noname::backends::{r1cs::R1CS as R1CSNoname, BackendField};
use noname::witness::CompiledCircuit;
use num_bigint::BigUint;
use std::marker::PhantomData;

use folding_schemes::{frontend::FCircuit, Error};

pub mod bridge;
pub mod utils;
use crate::utils::{VecF, VecFpVar};

use self::bridge::NonameSonobeCircuit;
use self::utils::{compile_source_code, NonameInputs};

// `L` indicates the length of the ExternalInputs vector of field elements.
#[derive(Debug, Clone)]
pub struct NonameFCircuit<F: PrimeField, BF: BackendField, const L: usize> {
    pub state_len: usize,
    pub circuit: CompiledCircuit<R1CSNoname<BF>>,
    _f: PhantomData<F>,
}

impl<F: PrimeField, BF: BackendField, const L: usize> FCircuit<F> for NonameFCircuit<F, BF, L> {
    type Params = (String, usize);
    type ExternalInputs = VecF<F, L>;
    type ExternalInputsVar = VecFpVar<F, L>;

    fn new(params: Self::Params) -> Result<Self, Error> {
        let (code, state_len) = params;
        let compiled_circuit = compile_source_code::<BF>(&code).map_err(|_| {
            Error::Other("Encountered an error while compiling a noname circuit".to_owned())
        })?;
        Ok(NonameFCircuit {
            state_len,
            circuit: compiled_circuit,
            _f: PhantomData,
        })
    }

    fn state_len(&self) -> usize {
        self.state_len
    }

    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
        external_inputs: Self::ExternalInputsVar,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let wtns_external_inputs =
            NonameInputs::from_fpvars((&external_inputs.0, "external_inputs".to_string()))?;
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
                // we prefer to assign z_i1 here since (1) we have to return it, (2) we can't return
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
            assigned_external_inputs: &external_inputs.0,
            assigned_z_i1: &assigned_z_i1,
        };
        noname_circuit.generate_constraints(cs.clone())?;

        Ok(assigned_z_i1)
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::Fr;
    use ark_ff::PrimeField;
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use noname::backends::r1cs::R1csBn254Field;

    use folding_schemes::{frontend::FCircuit, Error};

    use super::NonameFCircuit;
    use crate::utils::VecFpVar;

    /// Native implementation of `NONAME_CIRCUIT_EXTERNAL_INPUTS`
    fn external_inputs_step_native<F: PrimeField>(z_i: Vec<F>, external_inputs: Vec<F>) -> Vec<F> {
        let xx = external_inputs[0] + z_i[0];
        let yy = external_inputs[1] * z_i[1];
        assert_eq!(yy, xx);
        vec![xx, yy]
    }

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
    fn test_step_native() -> Result<(), Error> {
        let cs = ConstraintSystem::<Fr>::new_ref();
        // state length = 2, external inputs length= 2
        let params = (NONAME_CIRCUIT_EXTERNAL_INPUTS.to_owned(), 2);
        let circuit = NonameFCircuit::<Fr, R1csBn254Field, 2>::new(params)?;
        let inputs_public = vec![Fr::from(2), Fr::from(5)];
        let inputs_private = vec![Fr::from(8), Fr::from(2)];

        let ivc_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(inputs_public.clone()))?;
        let external_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(inputs_private.clone()))?;

        let z_i1 = circuit.generate_step_constraints(
            cs.clone(),
            0,
            ivc_inputs_var,
            VecFpVar(external_inputs_var),
        )?;
        let z_i1_native = external_inputs_step_native(inputs_public, inputs_private);

        assert_eq!(z_i1[0].value()?, z_i1_native[0]);
        assert_eq!(z_i1[1].value()?, z_i1_native[1]);
        Ok(())
    }

    #[test]
    fn test_step_constraints() -> Result<(), Error> {
        let cs = ConstraintSystem::<Fr>::new_ref();
        // external inputs length= 2
        let params = (NONAME_CIRCUIT_EXTERNAL_INPUTS.to_owned(), 2);
        let circuit = NonameFCircuit::<Fr, R1csBn254Field, 2>::new(params)?;
        let inputs_public = vec![Fr::from(2), Fr::from(5)];
        let inputs_private = vec![Fr::from(8), Fr::from(2)];

        let ivc_inputs_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(inputs_public))?;
        let external_inputs_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(inputs_private))?;

        let z_i1 = circuit.generate_step_constraints(
            cs.clone(),
            0,
            ivc_inputs_var,
            VecFpVar(external_inputs_var),
        )?;
        assert!(cs.is_satisfied()?);
        assert_eq!(z_i1[0].value()?, Fr::from(10_u8));
        assert_eq!(z_i1[1].value()?, Fr::from(10_u8));
        Ok(())
    }

    #[test]
    fn test_generate_constraints_no_external_inputs() -> Result<(), Error> {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let params = (NONAME_CIRCUIT_NO_EXTERNAL_INPUTS.to_owned(), 2); // state length = 2
        let inputs_public = vec![Fr::from(2), Fr::from(5)];

        let ivc_inputs_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(inputs_public))?;

        // external inputs length = 0
        let f_circuit = NonameFCircuit::<Fr, R1csBn254Field, 0>::new(params)?;
        f_circuit.generate_step_constraints(cs.clone(), 0, ivc_inputs_var, VecFpVar(vec![]))?;
        assert!(cs.is_satisfied()?);
        Ok(())
    }
}
