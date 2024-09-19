use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
#[cfg(test)]
use ark_std::marker::PhantomData;
use ark_std::{fmt::Debug, Zero};

use super::FCircuit;
use crate::Error;

/// DummyCircuit is a circuit that has dummy state and external inputs whose
/// lengths are specified in the `state_len` and `external_inputs_len`
/// parameters, without any constraints.
#[derive(Clone, Debug)]
pub struct DummyCircuit {
    state_len: usize,
    external_inputs_len: usize,
}
impl<F: PrimeField> FCircuit<F> for DummyCircuit {
    type Params = (usize, usize);

    fn new((state_len, external_inputs_len): Self::Params) -> Result<Self, Error> {
        Ok(Self {
            state_len,
            external_inputs_len,
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
        _z_i: Vec<F>,
        _external_inputs: Vec<F>,
    ) -> Result<Vec<F>, Error> {
        Ok(vec![F::zero(); self.state_len])
    }
    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        _i: usize,
        _z_i: Vec<FpVar<F>>,
        _external_inputs: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        Vec::new_witness(cs.clone(), || Ok(vec![Zero::zero(); self.state_len]))
    }
}

/// CubicFCircuit is a struct that implements the FCircuit trait, for the R1CS example circuit
/// from https://www.vitalik.ca/general/2016/12/10/qap.html, which checks `x^3 + x + 5 = y`.
/// `z_i` is used as `x`, and `z_{i+1}` is used as `y`, and at the next step, `z_{i+1}` will be
/// assigned to `z_i`, and a new `z+{i+1}` will be computted.
#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub struct CubicFCircuit<F: PrimeField> {
    _f: PhantomData<F>,
}

#[cfg(test)]
impl<F: PrimeField> FCircuit<F> for CubicFCircuit<F> {
    type Params = ();
    fn new(_params: Self::Params) -> Result<Self, Error> {
        Ok(Self { _f: PhantomData })
    }
    fn state_len(&self) -> usize {
        1
    }
    fn external_inputs_len(&self) -> usize {
        0
    }
    fn step_native(
        &self,
        _i: usize,
        z_i: Vec<F>,
        _external_inputs: Vec<F>,
    ) -> Result<Vec<F>, Error> {
        Ok(vec![z_i[0] * z_i[0] * z_i[0] + z_i[0] + F::from(5_u32)])
    }
    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
        _external_inputs: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let five = FpVar::<F>::new_constant(cs.clone(), F::from(5u32))?;
        let z_i = z_i[0].clone();

        Ok(vec![&z_i * &z_i * &z_i + &z_i + &five])
    }
}

/// CustomFCircuit is a circuit that has the number of constraints specified in the
/// `n_constraints` parameter. Note that the generated circuit will have very sparse matrices.
#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub struct CustomFCircuit<F: PrimeField> {
    _f: PhantomData<F>,
    pub n_constraints: usize,
}

#[cfg(test)]
impl<F: PrimeField> FCircuit<F> for CustomFCircuit<F> {
    type Params = usize;

    fn new(params: Self::Params) -> Result<Self, Error> {
        Ok(Self {
            _f: PhantomData,
            n_constraints: params,
        })
    }
    fn state_len(&self) -> usize {
        1
    }
    fn external_inputs_len(&self) -> usize {
        0
    }
    fn step_native(
        &self,
        _i: usize,
        z_i: Vec<F>,
        _external_inputs: Vec<F>,
    ) -> Result<Vec<F>, Error> {
        let mut z_i1 = F::one();
        for _ in 0..self.n_constraints - 1 {
            z_i1 *= z_i[0];
        }
        Ok(vec![z_i1])
    }
    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
        _external_inputs: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let mut z_i1 = FpVar::<F>::new_witness(cs.clone(), || Ok(F::one()))?;
        for _ in 0..self.n_constraints - 1 {
            z_i1 *= z_i[0].clone();
        }

        Ok(vec![z_i1])
    }
}

/// WrapperCircuit is a circuit that wraps any circuit that implements the FCircuit trait. This
/// is used to test the `FCircuit.generate_step_constraints` method. This is a similar wrapping
/// than the one done in the `AugmentedFCircuit`, but without adding all the extra constraints
/// of the AugmentedF circuit logic, in order to run lighter tests when we're not interested in
/// the the AugmentedF logic but in the wrapping of the circuits.
#[cfg(test)]
pub struct WrapperCircuit<F: PrimeField, FC: FCircuit<F>> {
    pub FC: FC, // F circuit
    pub z_i: Option<Vec<F>>,
    pub z_i1: Option<Vec<F>>,
}

#[cfg(test)]
impl<F, FC> ark_relations::r1cs::ConstraintSynthesizer<F> for WrapperCircuit<F, FC>
where
    F: PrimeField,
    FC: FCircuit<F>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let z_i =
            Vec::<FpVar<F>>::new_witness(cs.clone(), || Ok(self.z_i.unwrap_or(vec![F::zero()])))?;
        let z_i1 =
            Vec::<FpVar<F>>::new_input(cs.clone(), || Ok(self.z_i1.unwrap_or(vec![F::zero()])))?;
        let computed_z_i1 =
            self.FC
                .generate_step_constraints(cs.clone(), 0, z_i.clone(), vec![])?;

        use ark_r1cs_std::eq::EqGadget;
        computed_z_i1.enforce_equal(&z_i1)?;
        Ok(())
    }
}
