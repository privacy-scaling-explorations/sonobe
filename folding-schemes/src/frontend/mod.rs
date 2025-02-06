use crate::Error;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_std::fmt::Debug;

pub mod utils;

/// FCircuit defines the trait of the circuit of the F function, which is the one being folded (ie.
/// inside the agmented F' function).
/// The parameter z_i denotes the current state, and z_{i+1} denotes the next state after applying
/// the step.
/// Note that the external inputs for the specific circuit are defined at the implementation of
/// both `FCircuit::ExternalInputs` and `FCircuit::ExternalInputsVar`, where the `Default` trait
/// implementation for the `ExternalInputs` returns the initialized data structure (ie. if the type
/// contains a vector, it is initialized at the expected length).
pub trait FCircuit<F: PrimeField>: Clone + Debug {
    type Params: Debug;
    type ExternalInputs: Clone + Default + Debug;
    type ExternalInputsVar: Clone + Debug + AllocVar<Self::ExternalInputs, F>;

    /// returns a new FCircuit instance
    fn new(params: Self::Params) -> Result<Self, Error>;

    /// returns the number of elements in the state of the FCircuit, which corresponds to the
    /// FCircuit inputs.
    fn state_len(&self) -> usize;

    /// generates the constraints for the step of F for the given z_i
    fn generate_step_constraints(
        // this method uses self, so that each FCircuit implementation (and different frontends)
        // can hold a state if needed to store data to generate the constraints.
        &self,
        cs: ConstraintSystemRef<F>,
        i: usize,
        z_i: Vec<FpVar<F>>,
        external_inputs: Self::ExternalInputsVar, // inputs that are not part of the state
    ) -> Result<Vec<FpVar<F>>, SynthesisError>;
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_bn254::Fr;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};

    use utils::{custom_step_native, CubicFCircuit, CustomFCircuit, WrapperCircuit};

    #[test]
    fn test_testfcircuit() -> Result<(), Error> {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let F_circuit = CubicFCircuit::<Fr>::new(())?;

        let wrapper_circuit = WrapperCircuit::<Fr, CubicFCircuit<Fr>> {
            FC: F_circuit,
            z_i: Some(vec![Fr::from(3_u32)]),
            z_i1: Some(vec![Fr::from(35_u32)]),
        };
        wrapper_circuit.generate_constraints(cs.clone())?;
        assert_eq!(cs.num_constraints(), 3);
        Ok(())
    }

    #[test]
    fn test_customtestfcircuit() -> Result<(), Error> {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let n_constraints = 1000;
        let custom_circuit = CustomFCircuit::<Fr>::new(n_constraints)?;
        let z_i = vec![Fr::from(5_u32)];
        let wrapper_circuit = WrapperCircuit::<Fr, CustomFCircuit<Fr>> {
            FC: custom_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(custom_step_native(z_i, n_constraints)),
        };
        wrapper_circuit.generate_constraints(cs.clone())?;
        assert_eq!(cs.num_constraints(), n_constraints);
        Ok(())
    }
}
