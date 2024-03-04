/// This file implements the onchain (Ethereum's EVM) decider circuit. For non-ethereum use cases,
/// other more efficient approaches can be used.
use ark_crypto_primitives::crh::poseidon::constraints::CRHParametersVar;
use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig, Absorb};
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, nonnative::NonNativeFieldVar, FieldVar},
    groups::GroupOpsBounds,
    prelude::CurveVar,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::{One, Zero};
use core::{borrow::Borrow, marker::PhantomData};

use crate::ccs::r1cs::R1CS;
use crate::commitment::{pedersen::Params as PedersenParams, CommitmentProver};
use crate::folding::nova::{
    circuits::{CommittedInstanceVar, CF1, CF2},
    CommittedInstance, Nova, Witness,
};
use crate::frontend::FCircuit;
use crate::utils::gadgets::{
    hadamard, mat_vec_mul_sparse, vec_add, vec_scalar_mul, SparseMatrixVar,
};

#[derive(Debug, Clone)]
pub struct RelaxedR1CSGadget<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>> {
    _f: PhantomData<F>,
    _cf: PhantomData<CF>,
    _fv: PhantomData<FV>,
}
impl<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>> RelaxedR1CSGadget<F, CF, FV> {
    /// performs the RelaxedR1CS check (Az∘Bz==uCz+E)
    pub fn check(
        r1cs: R1CSVar<F, CF, FV>,
        E: Vec<FV>,
        u: FV,
        z: Vec<FV>,
    ) -> Result<(), SynthesisError> {
        let Az = mat_vec_mul_sparse(r1cs.A, z.clone());
        let Bz = mat_vec_mul_sparse(r1cs.B, z.clone());
        let Cz = mat_vec_mul_sparse(r1cs.C, z.clone());
        let uCz = vec_scalar_mul(&Cz, &u);
        let uCzE = vec_add(&uCz, &E)?;
        let AzBz = hadamard(&Az, &Bz)?;
        for i in 0..AzBz.len() {
            AzBz[i].enforce_equal(&uCzE[i].clone())?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct R1CSVar<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>> {
    _f: PhantomData<F>,
    _cf: PhantomData<CF>,
    _fv: PhantomData<FV>,
    pub A: SparseMatrixVar<F, CF, FV>,
    pub B: SparseMatrixVar<F, CF, FV>,
    pub C: SparseMatrixVar<F, CF, FV>,
}

impl<F, CF, FV> AllocVar<R1CS<F>, CF> for R1CSVar<F, CF, FV>
where
    F: PrimeField,
    CF: PrimeField,
    FV: FieldVar<F, CF>,
{
    fn new_variable<T: Borrow<R1CS<F>>>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        _mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let A = SparseMatrixVar::<F, CF, FV>::new_constant(cs.clone(), &val.borrow().A)?;
            let B = SparseMatrixVar::<F, CF, FV>::new_constant(cs.clone(), &val.borrow().B)?;
            let C = SparseMatrixVar::<F, CF, FV>::new_constant(cs.clone(), &val.borrow().C)?;

            Ok(Self {
                _f: PhantomData,
                _cf: PhantomData,
                _fv: PhantomData,
                A,
                B,
                C,
            })
        })
    }
}

/// In-circuit representation of the Witness associated to the CommittedInstance.
#[derive(Debug, Clone)]
pub struct WitnessVar<C: CurveGroup> {
    pub E: Vec<FpVar<C::ScalarField>>,
    pub rE: FpVar<C::ScalarField>,
    pub W: Vec<FpVar<C::ScalarField>>,
    pub rW: FpVar<C::ScalarField>,
}

impl<C> AllocVar<Witness<C>, CF1<C>> for WitnessVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<Witness<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let E: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().E.clone()), mode)?;
            let rE =
                FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().rE), mode)?;

            let W: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().W.clone()), mode)?;
            let rW =
                FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().rW), mode)?;

            Ok(Self { E, rE, W, rW })
        })
    }
}

/// In-circuit representation of the Witness associated to the CommittedInstance, but with
/// non-native representation, since it is used to represent the CycleFold witness.
#[derive(Debug, Clone)]
pub struct CycleFoldWitnessVar<C: CurveGroup> {
    pub E: Vec<NonNativeFieldVar<C::ScalarField, CF2<C>>>,
    pub rE: NonNativeFieldVar<C::ScalarField, CF2<C>>,
    pub W: Vec<NonNativeFieldVar<C::ScalarField, CF2<C>>>,
    pub rW: NonNativeFieldVar<C::ScalarField, CF2<C>>,
}

impl<C> AllocVar<Witness<C>, CF2<C>> for CycleFoldWitnessVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<Witness<C>>>(
        cs: impl Into<Namespace<CF2<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let E: Vec<NonNativeFieldVar<C::ScalarField, CF2<C>>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().E.clone()), mode)?;
            let rE = NonNativeFieldVar::<C::ScalarField, CF2<C>>::new_variable(
                cs.clone(),
                || Ok(val.borrow().rE),
                mode,
            )?;

            let W: Vec<NonNativeFieldVar<C::ScalarField, CF2<C>>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().W.clone()), mode)?;
            let rW = NonNativeFieldVar::<C::ScalarField, CF2<C>>::new_variable(
                cs.clone(),
                || Ok(val.borrow().rW),
                mode,
            )?;

            Ok(Self { E, rE, W, rW })
        })
    }
}

/// Circuit that implements the in-circuit checks needed for the onchain (Ethereum's EVM)
/// verification.
#[derive(Clone, Debug)]
pub struct DeciderEthCircuit<C1, GC1, C2, GC2, CP1, CP2>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    CP1: CommitmentProver<C1>,
    CP2: CommitmentProver<C2>,
{
    _c1: PhantomData<C1>,
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,
    _cp1: PhantomData<CP1>,
    _cp2: PhantomData<CP2>,

    /// E vector's length of the Nova instance witness
    pub E_len: usize,
    /// E vector's length of the CycleFold instance witness
    pub cf_E_len: usize,
    /// R1CS of the Augmented Function circuit
    pub r1cs: R1CS<C1::ScalarField>,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: R1CS<C2::ScalarField>,
    /// CycleFold PedersenParams over C2
    pub cf_pedersen_params: PedersenParams<C2>,
    pub poseidon_config: PoseidonConfig<CF1<C1>>,
    pub i: Option<CF1<C1>>,
    /// initial state
    pub z_0: Option<Vec<C1::ScalarField>>,
    /// current i-th state
    pub z_i: Option<Vec<C1::ScalarField>>,
    /// Nova instances
    pub u_i: Option<CommittedInstance<C1>>,
    pub w_i: Option<Witness<C1>>,
    pub U_i: Option<CommittedInstance<C1>>,
    pub W_i: Option<Witness<C1>>,
    /// CycleFold running instance
    pub cf_U_i: Option<CommittedInstance<C2>>,
    pub cf_W_i: Option<Witness<C2>>,
}
impl<C1, GC1, C2, GC2, CP1, CP2> DeciderEthCircuit<C1, GC1, C2, GC2, CP1, CP2>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>>,
    CP1: CommitmentProver<C1>,
    // enforce that the CP2 is Pedersen commitment, since we're at Ethereum's EVM decider
    CP2: CommitmentProver<C2, Params = PedersenParams<C2>>,
{
    pub fn from_nova<FC: FCircuit<C1::ScalarField>>(
        nova: Nova<C1, GC1, C2, GC2, FC, CP1, CP2>,
    ) -> Self {
        Self {
            _c1: PhantomData,
            _gc1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,
            _cp1: PhantomData,
            _cp2: PhantomData,

            E_len: nova.W_i.E.len(),
            cf_E_len: nova.cf_W_i.E.len(),
            r1cs: nova.r1cs,
            cf_r1cs: nova.cf_r1cs,
            cf_pedersen_params: nova.cf_cm_params,
            poseidon_config: nova.poseidon_config,
            i: Some(nova.i),
            z_0: Some(nova.z_0),
            z_i: Some(nova.z_i),
            u_i: Some(nova.u_i),
            w_i: Some(nova.w_i),
            U_i: Some(nova.U_i),
            W_i: Some(nova.W_i),
            cf_U_i: Some(nova.cf_U_i),
            cf_W_i: Some(nova.cf_W_i),
        }
    }
}

impl<C1, GC1, C2, GC2, CP1, CP2> ConstraintSynthesizer<CF1<C1>>
    for DeciderEthCircuit<C1, GC1, C2, GC2, CP1, CP2>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>>,
    CP1: CommitmentProver<C1>,
    CP2: CommitmentProver<C2>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
        let r1cs =
            R1CSVar::<C1::ScalarField, CF1<C1>, FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
                Ok(self.r1cs.clone())
            })?;

        let i =
            FpVar::<CF1<C1>>::new_input(cs.clone(), || Ok(self.i.unwrap_or_else(CF1::<C1>::zero)))?;
        let z_0 = Vec::<FpVar<CF1<C1>>>::new_input(cs.clone(), || {
            Ok(self.z_0.unwrap_or(vec![CF1::<C1>::zero()]))
        })?;
        let z_i = Vec::<FpVar<CF1<C1>>>::new_input(cs.clone(), || {
            Ok(self.z_i.unwrap_or(vec![CF1::<C1>::zero()]))
        })?;

        let u_dummy_native = CommittedInstance::<C1>::dummy(1);
        let w_dummy_native = Witness::<C1>::new(
            vec![C1::ScalarField::zero(); self.r1cs.A.n_cols - 2 /* (2=1+1, since u_i.x.len=1) */],
            self.E_len,
        );

        let u_i = CommittedInstanceVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.u_i.unwrap_or(u_dummy_native.clone()))
        })?;
        let w_i = WitnessVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.w_i.unwrap_or(w_dummy_native.clone()))
        })?;
        let U_i = CommittedInstanceVar::<C1>::new_input(cs.clone(), || {
            Ok(self.U_i.unwrap_or(u_dummy_native.clone()))
        })?;
        let W_i = WitnessVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.W_i.unwrap_or(w_dummy_native.clone()))
        })?;

        let crh_params = CRHParametersVar::<C1::ScalarField>::new_constant(
            cs.clone(),
            self.poseidon_config.clone(),
        )?;

        // 1. check RelaxedR1CS of u_i
        let z_u: Vec<FpVar<CF1<C1>>> = [
            vec![FpVar::<CF1<C1>>::one()],
            u_i.x.to_vec(),
            w_i.W.to_vec(),
        ]
        .concat();
        RelaxedR1CSGadget::<C1::ScalarField, CF1<C1>, FpVar<CF1<C1>>>::check(
            r1cs.clone(),
            w_i.E,
            u_i.u.clone(),
            z_u,
        )?;

        // 2. check RelaxedR1CS of U_i
        let z_U: Vec<FpVar<CF1<C1>>> =
            [vec![U_i.u.clone()], U_i.x.to_vec(), W_i.W.to_vec()].concat();
        RelaxedR1CSGadget::<C1::ScalarField, CF1<C1>, FpVar<CF1<C1>>>::check(
            r1cs,
            W_i.E,
            U_i.u.clone(),
            z_U,
        )?;

        // 3. u_i.cmE==cm(0), u_i.u==1
        // Here zero_x & zero_y are the x & y coordinates of the zero point affine representation.
        let zero_x = NonNativeFieldVar::<C1::BaseField, C1::ScalarField>::new_constant(
            cs.clone(),
            C1::BaseField::zero(),
        )?;
        let zero_y = NonNativeFieldVar::<C1::BaseField, C1::ScalarField>::new_constant(
            cs.clone(),
            C1::BaseField::one(),
        )?;
        (u_i.cmE.x.is_eq(&zero_x)?).enforce_equal(&Boolean::TRUE)?;
        (u_i.cmE.y.is_eq(&zero_y)?).enforce_equal(&Boolean::TRUE)?;
        (u_i.u.is_one()?).enforce_equal(&Boolean::TRUE)?;

        // 4. u_i.x == H(i, z_0, z_i, U_i)
        let (u_i_x, _) = U_i
            .clone()
            .hash(&crh_params, i.clone(), z_0.clone(), z_i.clone())?;
        (u_i.x[0]).enforce_equal(&u_i_x)?;

        // The following two checks (and their respective allocations) are disabled for normal
        // tests since they take ~24.5M constraints and would take several minutes (and RAM) to run
        // the test
        #[cfg(not(test))]
        {
            // imports here instead of at the top of the file, so we avoid having multiple
            // `#[cfg(not(test))]`
            use crate::commitment::pedersen::PedersenGadget;
            use crate::folding::nova::cyclefold::{CycleFoldCommittedInstanceVar, CF_IO_LEN};
            use ark_r1cs_std::ToBitsGadget;

            let cf_u_dummy_native = CommittedInstance::<C2>::dummy(CF_IO_LEN);
            let w_dummy_native = Witness::<C2>::new(
                vec![C2::ScalarField::zero(); self.cf_r1cs.A.n_cols - 1 - self.cf_r1cs.l],
                self.cf_E_len,
            );
            let cf_U_i = CycleFoldCommittedInstanceVar::<C2, GC2>::new_witness(cs.clone(), || {
                Ok(self.cf_U_i.unwrap_or_else(|| cf_u_dummy_native.clone()))
            })?;
            let cf_W_i = CycleFoldWitnessVar::<C2>::new_witness(cs.clone(), || {
                Ok(self.cf_W_i.unwrap_or(w_dummy_native.clone()))
            })?;

            // 5. check Pedersen commitments of cf_U_i.{cmE, cmW}
            let H = GC2::new_constant(cs.clone(), self.cf_pedersen_params.h)?;
            let G = Vec::<GC2>::new_constant(cs.clone(), self.cf_pedersen_params.generators)?;
            let cf_W_i_E_bits: Result<Vec<Vec<Boolean<CF1<C1>>>>, SynthesisError> =
                cf_W_i.E.iter().map(|E_i| E_i.to_bits_le()).collect();
            let cf_W_i_W_bits: Result<Vec<Vec<Boolean<CF1<C1>>>>, SynthesisError> =
                cf_W_i.W.iter().map(|W_i| W_i.to_bits_le()).collect();

            let computed_cmE = PedersenGadget::<C2, GC2>::commit(
                H.clone(),
                G.clone(),
                cf_W_i_E_bits?,
                cf_W_i.rE.to_bits_le()?,
            )?;
            cf_U_i.cmE.enforce_equal(&computed_cmE)?;
            let computed_cmW =
                PedersenGadget::<C2, GC2>::commit(H, G, cf_W_i_W_bits?, cf_W_i.rW.to_bits_le()?)?;
            cf_U_i.cmW.enforce_equal(&computed_cmW)?;

            let cf_r1cs = R1CSVar::<
                C1::BaseField,
                CF1<C1>,
                NonNativeFieldVar<C1::BaseField, CF1<C1>>,
            >::new_witness(cs.clone(), || Ok(self.cf_r1cs.clone()))?;

            // 6. check RelaxedR1CS of cf_U_i
            let cf_z_U: Vec<NonNativeFieldVar<C2::ScalarField, CF1<C1>>> =
                [vec![cf_U_i.u.clone()], cf_U_i.x.to_vec(), cf_W_i.W.to_vec()].concat();
            RelaxedR1CSGadget::<
                C2::ScalarField,
                CF1<C1>,
                NonNativeFieldVar<C2::ScalarField, CF1<C1>>,
            >::check(cf_r1cs, cf_W_i.E, cf_U_i.u.clone(), cf_z_U)?;
        }

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_crypto_primitives::crh::{
        sha256::{
            constraints::{Sha256Gadget, UnitVar},
            Sha256,
        },
        CRHScheme, CRHSchemeGadget,
    };
    use ark_ff::BigInteger;
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_r1cs_std::{
        alloc::AllocVar,
        bits::uint8::UInt8,
        eq::EqGadget,
        fields::{fp::FpVar, nonnative::NonNativeFieldVar},
    };
    use ark_relations::r1cs::ConstraintSystem;
    use ark_vesta::{constraints::GVar as GVar2, Projective as Projective2};

    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::{get_pedersen_params_len, ProverParams, VerifierParams};
    use crate::frontend::tests::{CubicFCircuit, CustomFCircuit, WrapperCircuit};
    use crate::transcript::poseidon::poseidon_test_config;
    use crate::FoldingScheme;

    use crate::ccs::r1cs::{extract_r1cs, extract_w_x};
    use crate::ccs::r1cs::{
        tests::{get_test_r1cs, get_test_z},
        R1CS,
    };

    #[test]
    fn test_relaxed_r1cs_small_gadget_handcrafted() {
        let r1cs: R1CS<Fr> = get_test_r1cs();
        let rel_r1cs = r1cs.clone().relax();
        let z = get_test_z(3);

        let cs = ConstraintSystem::<Fr>::new_ref();

        let zVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z)).unwrap();
        let EVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(rel_r1cs.E)).unwrap();
        let uVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(rel_r1cs.u)).unwrap();
        let r1csVar = R1CSVar::<Fr, Fr, FpVar<Fr>>::new_witness(cs.clone(), || Ok(r1cs)).unwrap();

        RelaxedR1CSGadget::<Fr, Fr, FpVar<Fr>>::check(r1csVar, EVar, uVar, zVar).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    // gets as input a circuit that implements the ConstraintSynthesizer trait, and that has been
    // initialized.
    fn test_relaxed_r1cs_gadget<CS: ConstraintSynthesizer<Fr>>(circuit: CS) {
        let cs = ConstraintSystem::<Fr>::new_ref();

        circuit.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        assert!(cs.is_satisfied().unwrap());

        let cs = cs.into_inner().unwrap();

        let r1cs = extract_r1cs::<Fr>(&cs);
        let (w, x) = extract_w_x::<Fr>(&cs);
        let z = [vec![Fr::one()], x, w].concat();
        r1cs.check_relation(&z).unwrap();

        let relaxed_r1cs = r1cs.clone().relax();
        relaxed_r1cs.check_relation(&z).unwrap();

        // set new CS for the circuit that checks the RelaxedR1CS of our original circuit
        let cs = ConstraintSystem::<Fr>::new_ref();
        // prepare the inputs for our circuit
        let zVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z)).unwrap();
        let EVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(relaxed_r1cs.E)).unwrap();
        let uVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(relaxed_r1cs.u)).unwrap();
        let r1csVar = R1CSVar::<Fr, Fr, FpVar<Fr>>::new_witness(cs.clone(), || Ok(r1cs)).unwrap();

        RelaxedR1CSGadget::<Fr, Fr, FpVar<Fr>>::check(r1csVar, EVar, uVar, zVar).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_relaxed_r1cs_small_gadget_arkworks() {
        let z_i = vec![Fr::from(3_u32)];
        let cubic_circuit = CubicFCircuit::<Fr>::new(());
        let circuit = WrapperCircuit::<Fr, CubicFCircuit<Fr>> {
            FC: cubic_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(cubic_circuit.step_native(0, z_i).unwrap()),
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
        let custom_circuit = CustomFCircuit::<Fr>::new(n_constraints);
        let z_i = vec![Fr::from(5_u32)];
        let circuit = WrapperCircuit::<Fr, CustomFCircuit<Fr>> {
            FC: custom_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(custom_circuit.step_native(0, z_i).unwrap()),
        };
        test_relaxed_r1cs_gadget(circuit);
    }

    #[test]
    fn test_relaxed_r1cs_nonnative_circuit() {
        let cs = ConstraintSystem::<Fq>::new_ref();
        // in practice we would use CycleFoldCircuit, but is a very big circuit (when computed
        // non-natively inside the RelaxedR1CS circuit), so in order to have a short test we use a
        // custom circuit.
        let custom_circuit = CustomFCircuit::<Fq>::new(10);
        let z_i = vec![Fq::from(5_u32)];
        let circuit = WrapperCircuit::<Fq, CustomFCircuit<Fq>> {
            FC: custom_circuit,
            z_i: Some(z_i.clone()),
            z_i1: Some(custom_circuit.step_native(0, z_i).unwrap()),
        };
        circuit.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        let cs = cs.into_inner().unwrap();
        let r1cs = extract_r1cs::<Fq>(&cs);
        let (w, x) = extract_w_x::<Fq>(&cs);
        let z = [vec![Fq::one()], x, w].concat();

        let relaxed_r1cs = r1cs.clone().relax();

        // natively
        let cs = ConstraintSystem::<Fq>::new_ref();
        let zVar = Vec::<FpVar<Fq>>::new_witness(cs.clone(), || Ok(z.clone())).unwrap();
        let EVar =
            Vec::<FpVar<Fq>>::new_witness(cs.clone(), || Ok(relaxed_r1cs.clone().E)).unwrap();
        let uVar = FpVar::<Fq>::new_witness(cs.clone(), || Ok(relaxed_r1cs.u)).unwrap();
        let r1csVar =
            R1CSVar::<Fq, Fq, FpVar<Fq>>::new_witness(cs.clone(), || Ok(r1cs.clone())).unwrap();
        RelaxedR1CSGadget::<Fq, Fq, FpVar<Fq>>::check(r1csVar, EVar, uVar, zVar).unwrap();

        // non-natively
        let cs = ConstraintSystem::<Fr>::new_ref();
        let zVar = Vec::<NonNativeFieldVar<Fq, Fr>>::new_witness(cs.clone(), || Ok(z)).unwrap();
        let EVar = Vec::<NonNativeFieldVar<Fq, Fr>>::new_witness(cs.clone(), || Ok(relaxed_r1cs.E))
            .unwrap();
        let uVar =
            NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(relaxed_r1cs.u)).unwrap();
        let r1csVar =
            R1CSVar::<Fq, Fr, NonNativeFieldVar<Fq, Fr>>::new_witness(cs.clone(), || Ok(r1cs))
                .unwrap();
        RelaxedR1CSGadget::<Fq, Fr, NonNativeFieldVar<Fq, Fr>>::check(r1csVar, EVar, uVar, zVar)
            .unwrap();
    }

    #[test]
    fn test_decider_circuit() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(());
        let z_0 = vec![Fr::from(3_u32)];

        // get the CM & CF_CM len
        let (cm_len, cf_cm_len) =
            get_pedersen_params_len::<Projective, GVar, Projective2, GVar2, CubicFCircuit<Fr>>(
                &poseidon_config,
                F_circuit,
            )
            .unwrap();
        let pedersen_params = Pedersen::<Projective>::new_params(&mut rng, cm_len);
        let cf_pedersen_params = Pedersen::<Projective2>::new_params(&mut rng, cf_cm_len);

        let prover_params =
            ProverParams::<Projective, Projective2, Pedersen<Projective>, Pedersen<Projective2>> {
                poseidon_config: poseidon_config.clone(),
                cm_params: pedersen_params,
                cf_cm_params: cf_pedersen_params,
            };

        type NOVA = Nova<
            Projective,
            GVar,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
            Pedersen<Projective>,
            Pedersen<Projective2>,
        >;

        // generate a Nova instance and do a step of it
        let mut nova = NOVA::init(&prover_params, F_circuit, z_0.clone()).unwrap();
        nova.prove_step().unwrap();
        let ivc_v = nova.clone();
        let verifier_params = VerifierParams::<Projective, Projective2> {
            poseidon_config: poseidon_config.clone(),
            r1cs: ivc_v.clone().r1cs,
            cf_r1cs: ivc_v.clone().cf_r1cs,
        };
        let (running_instance, incoming_instance, cyclefold_instance) = ivc_v.instances();
        NOVA::verify(
            verifier_params,
            z_0,
            ivc_v.z_i,
            Fr::one(),
            running_instance,
            incoming_instance,
            cyclefold_instance,
        )
        .unwrap();

        // load the DeciderEthCircuit from the generated Nova instance
        let decider_circuit = DeciderEthCircuit::<
            Projective,
            GVar,
            Projective2,
            GVar2,
            Pedersen<Projective>,
            Pedersen<Projective2>,
        >::from_nova(nova);

        let cs = ConstraintSystem::<Fr>::new_ref();

        // generate the constraints and check that are satisfied by the inputs
        decider_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }
}
