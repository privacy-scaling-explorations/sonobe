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
/// `M` is for the modulo operation involved in the satisfiability check when
/// the underlying `FVar` is `NonNativeUintVar`.
#[derive(Debug, Clone)]
pub struct R1CSMatricesVar<M, FVar> {
    _m: PhantomData<M>,
    pub A: SparseMatrixVar<FVar>,
    pub B: SparseMatrixVar<FVar>,
    pub C: SparseMatrixVar<FVar>,
}

impl<F: PrimeField, ConstraintF: PrimeField, FVar: AllocVar<F, ConstraintF>>
    AllocVar<R1CS<F>, ConstraintF> for R1CSMatricesVar<F, FVar>
{
    fn new_variable<T: Borrow<R1CS<F>>>(
        cs: impl Into<Namespace<ConstraintF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        _mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            Ok(Self {
                _m: PhantomData,
                A: SparseMatrixVar::<FVar>::new_constant(cs.clone(), &val.borrow().A)?,
                B: SparseMatrixVar::<FVar>::new_constant(cs.clone(), &val.borrow().B)?,
                C: SparseMatrixVar::<FVar>::new_constant(cs.clone(), &val.borrow().C)?,
            })
        })
    }
}

impl<M, FVar> R1CSMatricesVar<M, FVar>
where
    SparseMatrixVar<FVar>: MatrixGadget<FVar>,
    [FVar]: VectorGadget<FVar>,
{
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
    use ark_r1cs_std::{bits::uint8::UInt8, eq::EqGadget, fields::fp::FpVar};
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
        utils::{CubicFCircuit, CustomFCircuit, WrapperCircuit},
        FCircuit,
    };

    fn prepare_instances<C: CurveGroup, CS: CommitmentScheme<C>, R: Rng>(
        mut rng: R,
        r1cs: &R1CS<C::ScalarField>,
        z: &[C::ScalarField],
    ) -> (Witness<C>, CommittedInstance<C>) {
        let (w, x) = r1cs.split_z(z);

        let (cs_pp, _) = CS::setup(&mut rng, max(w.len(), r1cs.A.n_rows)).unwrap();

        let mut w = Witness::new::<false>(w, r1cs.A.n_rows, &mut rng);
        w.E = r1cs.eval_at_z(z).unwrap();
        let mut u = w.commit::<CS, false>(&cs_pp, x).unwrap();
        u.u = z[0];

        (w, u)
    }

    #[test]
    fn test_relaxed_r1cs_small_gadget_handcrafted() {
        let rng = &mut thread_rng();

        let r1cs: R1CS<Fr> = get_test_r1cs();
        let mut z = get_test_z(3);
        z[0] = Fr::rand(rng);
        let (w, u) = prepare_instances::<_, Pedersen<Projective>, _>(rng, &r1cs, &z);

        let cs = ConstraintSystem::<Fr>::new_ref();

        let wVar = WitnessVar::new_witness(cs.clone(), || Ok(w)).unwrap();
        let uVar = CommittedInstanceVar::new_witness(cs.clone(), || Ok(u)).unwrap();
        let r1csVar =
            R1CSMatricesVar::<Fr, FpVar<Fr>>::new_witness(cs.clone(), || Ok(r1cs)).unwrap();

        r1csVar.enforce_relation(&wVar, &uVar).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    // gets as input a circuit that implements the ConstraintSynthesizer trait, and that has been
    // initialized.
    fn test_relaxed_r1cs_gadget<CS: ConstraintSynthesizer<Fr>>(circuit: CS) {
        let rng = &mut thread_rng();

        let cs = ConstraintSystem::<Fr>::new_ref();

        circuit.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        assert!(cs.is_satisfied().unwrap());

        let cs = cs.into_inner().unwrap();

        let r1cs = extract_r1cs::<Fr>(&cs).unwrap();
        let (w, x) = extract_w_x::<Fr>(&cs);
        r1cs.check_relation(&w, &x).unwrap();
        let mut z = [vec![Fr::one()], x, w].concat();
        z[0] = Fr::rand(rng);

        let (w, u) = prepare_instances::<_, Pedersen<Projective>, _>(rng, &r1cs, &z);
        r1cs.check_relation(&w, &u).unwrap();

        // set new CS for the circuit that checks the RelaxedR1CS of our original circuit
        let cs = ConstraintSystem::<Fr>::new_ref();
        // prepare the inputs for our circuit
        let wVar = WitnessVar::new_witness(cs.clone(), || Ok(w)).unwrap();
        let uVar = CommittedInstanceVar::new_witness(cs.clone(), || Ok(u)).unwrap();
        let r1csVar =
            R1CSMatricesVar::<Fr, FpVar<Fr>>::new_witness(cs.clone(), || Ok(r1cs)).unwrap();

        r1csVar.enforce_relation(&wVar, &uVar).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_relaxed_r1cs_small_gadget_arkworks() {
        let z_i = vec![Fr::from(3_u32)];
        let cubic_circuit = CubicFCircuit::<Fr>::new(()).unwrap();
        let circuit = WrapperCircuit::<Fr, CubicFCircuit<Fr>> {
            FC: cubic_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(cubic_circuit.step_native(0, &z_i, &[]).unwrap()),
        };

        test_relaxed_r1cs_gadget(circuit);
    }

    struct Sha256TestCircuit<F: PrimeField> {
        _f: PhantomData<F>,
        pub x: Vec<u8>,
        pub y: Vec<u8>,
    }
    impl<F: PrimeField> ConstraintSynthesizer<F> for Sha256TestCircuit<F> {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let x = Vec::<UInt8<F>>::new_witness(cs.clone(), || Ok(self.x))?;
            let y = Vec::<UInt8<F>>::new_input(cs.clone(), || Ok(self.y))?;

            let unitVar = UnitVar::default();
            let comp_y = <Sha256Gadget<F> as CRHSchemeGadget<Sha256, F>>::evaluate(&unitVar, &x)?;
            comp_y.0.enforce_equal(&y)?;
            Ok(())
        }
    }
    #[test]
    fn test_relaxed_r1cs_medium_gadget_arkworks() {
        let x = Fr::from(5_u32).into_bigint().to_bytes_le();
        let y = <Sha256 as CRHScheme>::evaluate(&(), x.clone()).unwrap();

        let circuit = Sha256TestCircuit::<Fr> {
            _f: PhantomData,
            x,
            y,
        };
        test_relaxed_r1cs_gadget(circuit);
    }

    #[test]
    fn test_relaxed_r1cs_custom_circuit() {
        let n_constraints = 10_000;
        let custom_circuit = CustomFCircuit::<Fr>::new(n_constraints).unwrap();
        let z_i = vec![Fr::from(5_u32)];
        let circuit = WrapperCircuit::<Fr, CustomFCircuit<Fr>> {
            FC: custom_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(custom_circuit.step_native(0, &z_i, &[]).unwrap()),
        };
        test_relaxed_r1cs_gadget(circuit);
    }

    #[test]
    fn test_relaxed_r1cs_nonnative_circuit() {
        let rng = &mut thread_rng();

        let cs = ConstraintSystem::<Fq>::new_ref();
        // in practice we would use CycleFoldCircuit, but is a very big circuit (when computed
        // non-natively inside the RelaxedR1CS circuit), so in order to have a short test we use a
        // custom circuit.
        let custom_circuit = CustomFCircuit::<Fq>::new(10).unwrap();
        let z_i = vec![Fq::from(5_u32)];
        let circuit = WrapperCircuit::<Fq, CustomFCircuit<Fq>> {
            FC: custom_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(custom_circuit.step_native(0, &z_i, &[]).unwrap()),
        };
        circuit.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        let cs = cs.into_inner().unwrap();
        let r1cs = extract_r1cs::<Fq>(&cs).unwrap();
        let (w, x) = extract_w_x::<Fq>(&cs);
        let z = [vec![Fq::rand(rng)], x, w].concat();

        let (w, u) = prepare_instances::<_, Pedersen<Projective2>, _>(rng, &r1cs, &z);

        // natively
        let cs = ConstraintSystem::<Fq>::new_ref();
        let wVar = WitnessVar::new_witness(cs.clone(), || Ok(&w)).unwrap();
        let uVar = CommittedInstanceVar::new_witness(cs.clone(), || Ok(&u)).unwrap();
        let r1csVar =
            R1CSMatricesVar::<Fq, FpVar<Fq>>::new_witness(cs.clone(), || Ok(&r1cs)).unwrap();
        r1csVar.enforce_relation(&wVar, &uVar).unwrap();

        // non-natively
        let cs = ConstraintSystem::<Fr>::new_ref();
        let wVar = CycleFoldWitnessVar::new_witness(cs.clone(), || Ok(w)).unwrap();
        let uVar =
            CycleFoldCommittedInstanceVar::<_, GVar2>::new_witness(cs.clone(), || Ok(u)).unwrap();
        let r1csVar =
            R1CSMatricesVar::<Fq, NonNativeUintVar<Fr>>::new_witness(cs.clone(), || Ok(r1cs))
                .unwrap();
        r1csVar.enforce_relation(&wVar, &uVar).unwrap();
    }
}
