//! Circuit implementations for Rank-1 Constraint Systems (R1CS).
//!
//! This module provides an in-circuit representation of R1CS for use within other circuits.
//! It includes support for both native field operations and non-native field arithmetic
//! through generic matrix and vector operations.

use crate::{
    arith::ArithGadget,
    utils::gadgets::{EquivalenceGadget, MatrixGadget, SparseMatrixVar, VectorGadget},
};
use ark_ff::PrimeField;
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::{borrow::Borrow, marker::PhantomData, One};

use super::R1CS;

/// An in-circuit representation of the `R1CS` struct.
///
/// This gadget allows R1CS operations to be performed within another constraint system.
///
/// # Type Parameters
///
/// * `M` - Type for the modulo operation in satisfiability checks when `FVar` is `NonNativeUintVar`
/// * `FVar` - Variable type representing field elements in the circuit
#[derive(Debug, Clone)]
pub struct R1CSMatricesVar<M, FVar> {
    /// Phantom data for the modulo type
    _m: PhantomData<M>,
    /// In-circuit representation of matrix A
    pub A: SparseMatrixVar<FVar>,
    /// In-circuit representation of matrix B
    pub B: SparseMatrixVar<FVar>,
    /// In-circuit representation of matrix C
    pub C: SparseMatrixVar<FVar>,
}

impl<F: PrimeField, ConstraintF: PrimeField, FVar: AllocVar<F, ConstraintF>>
    AllocVar<R1CS<F>, ConstraintF> for R1CSMatricesVar<F, FVar>
{
    /// Creates a new circuit representation of R1CS matrices
    ///
    /// # Type Parameters
    ///
    /// * `T` - Type that can be borrowed as `R1CS<F>`
    ///
    /// # Arguments
    ///
    /// * `cs` - Constraint system handle
    /// * `f` - Function that returns the R1CS to be converted to circuit form
    /// * `_mode` - Allocation mode (unused as matrices are allocated as constants)
    ///
    /// # Errors
    ///
    /// Returns a `SynthesisError` if:
    /// * Matrix conversion to circuit form fails
    /// * Circuit variable allocation fails
    fn new_variable<T: Borrow<R1CS<F>>>(
        cs: impl Into<Namespace<ConstraintF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        _mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            // TODO (autoparallel): How expensive are these clones? Is there a cheaper way to do this?
            Ok(Self {
                _m: PhantomData,
                A: SparseMatrixVar::<FVar>::new_constant(cs.clone(), &val.borrow().A)?,
                B: SparseMatrixVar::<FVar>::new_constant(cs.clone(), &val.borrow().B)?,
                C: SparseMatrixVar::<FVar>::new_constant(cs, &val.borrow().C)?,
            })
        })
    }
}

impl<M, FVar> R1CSMatricesVar<M, FVar>
where
    SparseMatrixVar<FVar>: MatrixGadget<FVar>,
    [FVar]: VectorGadget<FVar>,
{
    /// Evaluates the R1CS matrices at given circuit variable assignments
    ///
    /// # Arguments
    ///
    /// * `z` - Vector of circuit variables to evaluate at
    ///
    /// # Returns
    ///
    /// Returns a tuple (AzBz, uCz) where:
    /// * AzBz is the Hadamard product of Az and Bz
    /// * uCz is Cz scaled by z[0]
    ///
    /// # Errors
    ///
    /// Returns a `SynthesisError` if:
    /// * Matrix-vector multiplication fails
    /// * Hadamard product computation fails
    /// * Vector operations fail
    pub fn eval_at_z(&self, z: &[FVar]) -> Result<(Vec<FVar>, Vec<FVar>), SynthesisError> {
        // Multiply Cz by z[0] (u) here, allowing this method to be reused for
        // both relaxed and unrelaxed R1CS.
        let Az = self.A.mul_vector(z)?;
        let Bz = self.B.mul_vector(z)?;
        let Cz = self.C.mul_vector(z)?;
        let uCz = Cz.mul_scalar(&z[0])?;
        let AzBz = Az.hadamard(&Bz)?;
        Ok((AzBz, uCz))
    }
}

impl<M, FVar, WVar: AsRef<[FVar]>, UVar: AsRef<[FVar]>> ArithGadget<WVar, UVar>
    for R1CSMatricesVar<M, FVar>
where
    SparseMatrixVar<FVar>: MatrixGadget<FVar>,
    [FVar]: VectorGadget<FVar> + EquivalenceGadget<M>,
    FVar: Clone + One,
{
    /// Evaluation is a tuple of two vectors (`AzBz` and `uCz`) instead of a
    /// single vector `AzBz - uCz`, because subtraction is not supported for
    /// `FVar = NonNativeUintVar`.
    type Evaluation = (Vec<FVar>, Vec<FVar>);

    fn eval_relation(&self, w: &WVar, u: &UVar) -> Result<Self::Evaluation, SynthesisError> {
        self.eval_at_z(&[&[FVar::one()], u.as_ref(), w.as_ref()].concat())
    }

    fn enforce_evaluation(
        _w: &WVar,
        _u: &UVar,
        (lhs, rhs): Self::Evaluation,
    ) -> Result<(), SynthesisError> {
        lhs.enforce_equivalent(&rhs)
    }
}

#[cfg(test)]
pub mod tests {
    use std::cmp::max;

    use ark_crypto_primitives::crh::{
        sha256::{
            constraints::{Sha256Gadget, UnitVar},
            Sha256,
        },
        CRHScheme, CRHSchemeGadget,
    };
    use ark_ec::CurveGroup;
    use ark_ff::BigInteger;
    use ark_pallas::{Fq, Fr, Projective};
    use ark_r1cs_std::{eq::EqGadget, fields::fp::FpVar, uint8::UInt8};
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef};
    use ark_std::{
        rand::{thread_rng, Rng},
        One, UniformRand,
    };
    use ark_vesta::{constraints::GVar as GVar2, Projective as Projective2};

    use super::*;
    use crate::arith::{
        r1cs::{
            extract_r1cs, extract_w_x,
            tests::{get_test_r1cs, get_test_z},
        },
        Arith,
    };
    use crate::commitment::{pedersen::Pedersen, CommitmentScheme};
    use crate::folding::{
        circuits::{
            cyclefold::{CycleFoldCommittedInstanceVar, CycleFoldWitnessVar},
            nonnative::uint::NonNativeUintVar,
        },
        nova::{
            decider_eth_circuit::WitnessVar, nifs::nova_circuits::CommittedInstanceVar,
            CommittedInstance, Witness,
        },
    };
    use crate::frontend::{
        utils::{
            cubic_step_native, custom_step_native, CubicFCircuit, CustomFCircuit, WrapperCircuit,
        },
        FCircuit,
    };
    use crate::Error;

    fn prepare_instances<C: CurveGroup, CS: CommitmentScheme<C>, R: Rng>(
        mut rng: R,
        r1cs: &R1CS<C::ScalarField>,
        z: &[C::ScalarField],
    ) -> Result<(Witness<C>, CommittedInstance<C>), Error> {
        let (w, x) = r1cs.split_z(z);

        let (cs_pp, _) = CS::setup(&mut rng, max(w.len(), r1cs.A.n_rows))?;

        let mut w = Witness::new::<false>(w, r1cs.A.n_rows, &mut rng);
        w.E = r1cs.eval_at_z(z)?;
        let mut u = w.commit::<CS, false>(&cs_pp, x)?;
        u.u = z[0];

        Ok((w, u))
    }

    #[test]
    fn test_relaxed_r1cs_small_gadget_handcrafted() -> Result<(), Error> {
        let rng = &mut thread_rng();

        let r1cs: R1CS<Fr> = get_test_r1cs();
        let mut z = get_test_z(3);
        z[0] = Fr::rand(rng);
        let (w, u) = prepare_instances::<_, Pedersen<Projective>, _>(rng, &r1cs, &z)?;

        let cs = ConstraintSystem::<Fr>::new_ref();

        let wVar = WitnessVar::new_witness(cs.clone(), || Ok(w))?;
        let uVar = CommittedInstanceVar::new_witness(cs.clone(), || Ok(u))?;
        let r1csVar = R1CSMatricesVar::<Fr, FpVar<Fr>>::new_witness(cs.clone(), || Ok(r1cs))?;

        r1csVar.enforce_relation(&wVar, &uVar)?;
        assert!(cs.is_satisfied()?);
        Ok(())
    }

    // gets as input a circuit that implements the ConstraintSynthesizer trait, and that has been
    // initialized.
    fn test_relaxed_r1cs_gadget<CS: ConstraintSynthesizer<Fr>>(circuit: CS) -> Result<(), Error> {
        let rng = &mut thread_rng();

        let cs = ConstraintSystem::<Fr>::new_ref();

        circuit.generate_constraints(cs.clone())?;
        cs.finalize();
        assert!(cs.is_satisfied()?);

        let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;

        let r1cs = extract_r1cs::<Fr>(&cs)?;
        let (w, x) = extract_w_x::<Fr>(&cs);
        r1cs.check_relation(&w, &x)?;
        let mut z = [vec![Fr::one()], x, w].concat();
        z[0] = Fr::rand(rng);

        let (w, u) = prepare_instances::<_, Pedersen<Projective>, _>(rng, &r1cs, &z)?;
        r1cs.check_relation(&w, &u)?;

        // set new CS for the circuit that checks the RelaxedR1CS of our original circuit
        let cs = ConstraintSystem::<Fr>::new_ref();
        // prepare the inputs for our circuit
        let wVar = WitnessVar::new_witness(cs.clone(), || Ok(w))?;
        let uVar = CommittedInstanceVar::new_witness(cs.clone(), || Ok(u))?;
        let r1csVar = R1CSMatricesVar::<Fr, FpVar<Fr>>::new_witness(cs.clone(), || Ok(r1cs))?;

        r1csVar.enforce_relation(&wVar, &uVar)?;
        assert!(cs.is_satisfied()?);
        Ok(())
    }

    #[test]
    fn test_relaxed_r1cs_small_gadget_arkworks() -> Result<(), Error> {
        let z_i = vec![Fr::from(3_u32)];
        let cubic_circuit = CubicFCircuit::<Fr>::new(())?;
        let circuit = WrapperCircuit::<Fr, CubicFCircuit<Fr>> {
            FC: cubic_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(cubic_step_native(z_i)),
        };

        test_relaxed_r1cs_gadget(circuit)
    }

    struct Sha256TestCircuit<F: PrimeField> {
        _f: PhantomData<F>,
        pub x: Vec<u8>,
        pub y: Vec<u8>,
    }
    impl<F: PrimeField> ConstraintSynthesizer<F> for Sha256TestCircuit<F> {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let x = Vec::<UInt8<F>>::new_witness(cs.clone(), || Ok(self.x))?;
            let y = Vec::<UInt8<F>>::new_input(cs, || Ok(self.y))?;

            let unitVar = UnitVar::default();
            let comp_y = <Sha256Gadget<F> as CRHSchemeGadget<Sha256, F>>::evaluate(&unitVar, &x)?;
            comp_y.0.enforce_equal(&y)?;
            Ok(())
        }
    }
    #[test]
    fn test_relaxed_r1cs_medium_gadget_arkworks() -> Result<(), Error> {
        let x = Fr::from(5_u32).into_bigint().to_bytes_le();
        let y =
            <Sha256 as CRHScheme>::evaluate(&(), x.clone()).map_err(|_| Error::EvaluationFail)?;

        let circuit = Sha256TestCircuit::<Fr> {
            _f: PhantomData,
            x,
            y,
        };
        test_relaxed_r1cs_gadget(circuit)
    }

    #[test]
    fn test_relaxed_r1cs_custom_circuit() -> Result<(), Error> {
        let n_constraints = 10_000;
        let custom_circuit = CustomFCircuit::<Fr>::new(n_constraints)?;
        let z_i = vec![Fr::from(5_u32)];
        let circuit = WrapperCircuit::<Fr, CustomFCircuit<Fr>> {
            FC: custom_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(custom_step_native(z_i, n_constraints)),
        };
        test_relaxed_r1cs_gadget(circuit)
    }

    #[test]
    fn test_relaxed_r1cs_nonnative_circuit() -> Result<(), Error> {
        let n_constraints = 10;
        let rng = &mut thread_rng();

        let cs = ConstraintSystem::<Fq>::new_ref();
        // in practice we would use CycleFoldCircuit, but is a very big circuit (when computed
        // non-natively inside the RelaxedR1CS circuit), so in order to have a short test we use a
        // custom circuit.
        let custom_circuit = CustomFCircuit::<Fq>::new(n_constraints)?;
        let z_i = vec![Fq::from(5_u32)];
        let circuit = WrapperCircuit::<Fq, CustomFCircuit<Fq>> {
            FC: custom_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(custom_step_native(z_i, n_constraints)),
        };
        circuit.generate_constraints(cs.clone())?;
        cs.finalize();
        let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let r1cs = extract_r1cs::<Fq>(&cs)?;
        let (w, x) = extract_w_x::<Fq>(&cs);
        let z = [vec![Fq::rand(rng)], x, w].concat();

        let (w, u) = prepare_instances::<_, Pedersen<Projective2>, _>(rng, &r1cs, &z)?;

        // natively
        let cs = ConstraintSystem::<Fq>::new_ref();
        let wVar = WitnessVar::new_witness(cs.clone(), || Ok(&w))?;
        let uVar = CommittedInstanceVar::new_witness(cs.clone(), || Ok(&u))?;
        let r1csVar = R1CSMatricesVar::<Fq, FpVar<Fq>>::new_witness(cs, || Ok(&r1cs))?;
        r1csVar.enforce_relation(&wVar, &uVar)?;

        // non-natively
        let cs = ConstraintSystem::<Fr>::new_ref();
        let wVar = CycleFoldWitnessVar::new_witness(cs.clone(), || Ok(w))?;
        let uVar = CycleFoldCommittedInstanceVar::<_, GVar2>::new_witness(cs.clone(), || Ok(u))?;
        let r1csVar = R1CSMatricesVar::<Fq, NonNativeUintVar<Fr>>::new_witness(cs, || Ok(r1cs))?;
        r1csVar.enforce_relation(&wVar, &uVar)?;
        Ok(())
    }
}
