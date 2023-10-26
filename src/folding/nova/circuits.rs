use ark_crypto_primitives::crh::{
    poseidon::constraints::{CRHGadget, CRHParametersVar},
    CRHSchemeGadget,
};
use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig, Absorb};
use ark_ec::{AffineRepr, CurveGroup, Group};
use ark_ff::{Field, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    groups::GroupOpsBounds,
    prelude::CurveVar,
    ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::Zero;
use core::{borrow::Borrow, marker::PhantomData};

use super::CommittedInstance;
use crate::folding::circuits::{cyclefold::ECRLC, nonnative::NonNativeAffineVar};

/// CF1 represents the ConstraintField used for the main Nova circuit which is over E1::Fr, where
/// E1 is the main curve where we do the folding.
pub type CF1<C> = <<C as CurveGroup>::Affine as AffineRepr>::ScalarField;
/// CF2 represents the ConstraintField used for the CycleFold circuit which is over E2::Fr=E1::Fq,
/// where E2 is the auxiliary curve (from [CycleFold](https://eprint.iacr.org/2023/1192.pdf)
/// approach) where we check the folding of the commitments.
pub type CF2<C> = <<C as CurveGroup>::BaseField as Field>::BasePrimeField;

/// CommittedInstanceVar contains the u, x, cmE and cmW values which are folded on the main Nova
/// constraints field (E1::Fr, where E1 is the main curve).
#[derive(Debug, Clone)]
pub struct CommittedInstanceVar<C: CurveGroup> {
    _c: PhantomData<C>,
    u: FpVar<C::ScalarField>,
    x: Vec<FpVar<C::ScalarField>>,
    cmE: NonNativeAffineVar<CF2<C>, C::ScalarField>,
    cmW: NonNativeAffineVar<CF2<C>, C::ScalarField>,
}

impl<C> AllocVar<CommittedInstance<C>, CF1<C>> for CommittedInstanceVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<CommittedInstance<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let u = FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().u), mode)?;
            let x: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().x.clone()), mode)?;

            let cmE = NonNativeAffineVar::<CF2<C>, C::ScalarField>::new_variable(
                cs.clone(),
                || Ok(val.borrow().cmE),
                mode,
            )?;
            let cmW = NonNativeAffineVar::<CF2<C>, C::ScalarField>::new_variable(
                cs.clone(),
                || Ok(val.borrow().cmW),
                mode,
            )?;

            Ok(Self {
                _c: PhantomData,
                u,
                x,
                cmE,
                cmW,
            })
        })
    }
}

impl<C> CommittedInstanceVar<C>
where
    C: CurveGroup,
    <C as Group>::ScalarField: Absorb,
{
    /// hash implements the committed instance hash compatible with the native implementation from
    /// CommittedInstance.hash.
    /// Returns `H(i, z_0, z_i, U_i)`, where `i` can be `i` but also `i+1`, and `U` is the
    /// `CommittedInstance`.
    fn hash(
        self,
        crh_params: &CRHParametersVar<CF1<C>>,
        i: FpVar<CF1<C>>,
        z_0: FpVar<CF1<C>>,
        z_i: FpVar<CF1<C>>,
    ) -> Result<FpVar<CF1<C>>, SynthesisError> {
        let input = vec![
            vec![i, z_0, z_i, self.u],
            self.x,
            self.cmE.x.to_constraint_field()?,
            self.cmE.y.to_constraint_field()?,
            self.cmW.x.to_constraint_field()?,
            self.cmW.y.to_constraint_field()?,
        ]
        .concat();
        CRHGadget::<C::ScalarField>::evaluate(crh_params, &input)
    }
}

/// CommittedInstanceCycleFoldVar represents the commitments to E and W from the CommittedInstance
/// on the E2, which are folded on the auxiliary curve constraints field (E2::Fr = E1::Fq).
pub struct CommittedInstanceCycleFoldVar<C: CurveGroup, GC: CurveVar<C, CF2<C>>>
where
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    _c: PhantomData<C>,
    cmE: GC,
    cmW: GC,
}

impl<C, GC> AllocVar<CommittedInstance<C>, CF2<C>> for CommittedInstanceCycleFoldVar<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>>,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    fn new_variable<T: Borrow<CommittedInstance<C>>>(
        cs: impl Into<Namespace<CF2<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let cmE = GC::new_variable(cs.clone(), || Ok(val.borrow().cmE), mode)?;
            let cmW = GC::new_variable(cs.clone(), || Ok(val.borrow().cmW), mode)?;

            Ok(Self {
                _c: PhantomData,
                cmE,
                cmW,
            })
        })
    }
}

/// Implements the circuit that does the checks of the Non-Interactive Folding Scheme Verifier
/// described in section 4 of [Nova](https://eprint.iacr.org/2021/370.pdf), where the cmE & cmW checks are
/// delegated to the NIFSCycleFoldGadget.
pub struct NIFSGadget<C: CurveGroup> {
    _c: PhantomData<C>,
}

impl<C: CurveGroup> NIFSGadget<C>
where
    C: CurveGroup,
{
    /// Implements the constraints for NIFS.V for u and x, since cm(E) and cm(W) are delegated to
    /// the CycleFold circuit.
    pub fn verify(
        r: FpVar<CF1<C>>,
        ci1: CommittedInstanceVar<C>,
        ci2: CommittedInstanceVar<C>,
        ci3: CommittedInstanceVar<C>,
    ) -> Result<Boolean<CF1<C>>, SynthesisError> {
        // ensure that: ci3.u == ci1.u + r * ci2.u
        let first_check = ci3.u.is_eq(&(ci1.u + r.clone() * ci2.u))?;

        // ensure that: ci3.x == ci1.x + r * ci2.x
        let x_rlc = ci1
            .x
            .iter()
            .zip(ci2.x)
            .map(|(a, b)| a + &r * &b)
            .collect::<Vec<FpVar<CF1<C>>>>();
        let second_check = x_rlc.is_eq(&ci3.x)?;

        first_check.and(&second_check)
    }
}

/// NIFSCycleFoldGadget performs the Nova NIFS.V elliptic curve points relation checks in the other
/// curve following [CycleFold](https://eprint.iacr.org/2023/1192.pdf).
pub struct NIFSCycleFoldGadget<C: CurveGroup, GC: CurveVar<C, CF2<C>>> {
    _c: PhantomData<C>,
    _gc: PhantomData<GC>,
}
impl<C: CurveGroup, GC: CurveVar<C, CF2<C>>> NIFSCycleFoldGadget<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>>,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    pub fn verify(
        r_bits: Vec<Boolean<CF2<C>>>,
        cmT: GC,
        ci1: CommittedInstanceCycleFoldVar<C, GC>,
        ci2: CommittedInstanceCycleFoldVar<C, GC>,
        ci3: CommittedInstanceCycleFoldVar<C, GC>,
    ) -> Result<Boolean<CF2<C>>, SynthesisError> {
        // cm(E) check: ci3.cmE == ci1.cmE + r * cmT + r^2 * ci2.cmE
        let first_check = ci3.cmE.is_eq(
            &((ci2.cmE.scalar_mul_le(r_bits.iter())? + cmT).scalar_mul_le(r_bits.iter())?
                + ci1.cmE),
        )?;
        // cm(W) check: ci3.cmW == ci1.cmW + r * ci2.cmW
        let second_check = ECRLC::<C, GC>::check(r_bits, ci1.cmW, ci2.cmW, ci3.cmW)?;

        first_check.and(&second_check)
    }
}

/// FCircuit defines the trait of the circuit of the F function, which is the one being executed
/// inside the agmented F' function.
pub trait FCircuit<F: PrimeField>: ConstraintSynthesizer<F> + Copy {
    /// method that returns z_i (input), z_{i+1} (output)
    fn public(self) -> (F, F);

    /// method that computes the next state values in place, assigning z_{i+1} into z_i, and
    /// computing the new z_i
    fn step(&mut self);
}

/// AugmentedFCircuit implements the F' circuit (augmented F) defined in
/// [Nova](https://eprint.iacr.org/2021/370.pdf).
#[derive(Debug, Clone)]
pub struct AugmentedFCircuit<C: CurveGroup, FC: FCircuit<CF1<C>>> {
    _c: PhantomData<C>,
    pub poseidon_config: PoseidonConfig<CF1<C>>,
    pub i: Option<CF1<C>>,
    pub z_0: Option<C::ScalarField>,
    pub u_i: Option<CommittedInstance<C>>,
    pub U_i: Option<CommittedInstance<C>>,
    pub U_i1: Option<CommittedInstance<C>>,
    pub cmT: Option<C>,
    pub r: Option<C::ScalarField>, // This will not be an input and derived from a hash internally in the circuit (poseidon transcript)
    pub F: FC,                     // F circuit
    pub x: Option<CF1<C>>,         // public inputs (u_{i+1}.x)
}

impl<C: CurveGroup, FC: FCircuit<CF1<C>>> ConstraintSynthesizer<CF1<C>> for AugmentedFCircuit<C, FC>
where
    C: CurveGroup,
    <C as CurveGroup>::BaseField: PrimeField,
    <C as Group>::ScalarField: Absorb,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C>>) -> Result<(), SynthesisError> {
        let i =
            FpVar::<CF1<C>>::new_witness(cs.clone(), || Ok(self.i.unwrap_or_else(CF1::<C>::zero)))?;
        let z_0 = FpVar::<CF1<C>>::new_witness(cs.clone(), || {
            Ok(self.z_0.unwrap_or_else(CF1::<C>::zero))
        })?;

        // get z_i & z_{i+1} from the folded circuit
        let (z_i_native, z_i1_native) = self.F.public();
        let z_i = FpVar::<CF1<C>>::new_witness(cs.clone(), || Ok(z_i_native))?;
        let z_i1 = FpVar::<CF1<C>>::new_witness(cs.clone(), || Ok(z_i1_native))?;

        let u_dummy_native = CommittedInstance {
            cmE: C::zero(),
            u: C::ScalarField::zero(),
            cmW: C::zero(),
            x: vec![CF1::<C>::zero()],
        };

        let u_dummy =
            CommittedInstanceVar::<C>::new_witness(cs.clone(), || Ok(u_dummy_native.clone()))?;
        let u_i = CommittedInstanceVar::<C>::new_witness(cs.clone(), || {
            Ok(self.u_i.unwrap_or_else(|| u_dummy_native.clone()))
        })?;
        let U_i = CommittedInstanceVar::<C>::new_witness(cs.clone(), || {
            Ok(self.U_i.unwrap_or_else(|| u_dummy_native.clone()))
        })?;
        let U_i1 = CommittedInstanceVar::<C>::new_witness(cs.clone(), || {
            Ok(self.U_i1.unwrap_or_else(|| u_dummy_native.clone()))
        })?;
        let _cmT =
            NonNativeAffineVar::new_witness(cs.clone(), || Ok(self.cmT.unwrap_or_else(C::zero)))?;
        let r =
            FpVar::<CF1<C>>::new_witness(cs.clone(), || Ok(self.r.unwrap_or_else(CF1::<C>::zero)))?; // r will come from higher level transcript
        let x =
            FpVar::<CF1<C>>::new_input(cs.clone(), || Ok(self.x.unwrap_or_else(CF1::<C>::zero)))?;

        let crh_params =
            CRHParametersVar::<C::ScalarField>::new_constant(cs.clone(), self.poseidon_config)?;

        let zero = FpVar::<CF1<C>>::new_constant(cs.clone(), CF1::<C>::zero())?;
        let is_basecase = i.is_eq(&zero)?;
        let is_not_basecase = i.is_neq(&zero)?;

        // 1. h_{i+1} = u_i.X == H(i, z_0, z_i, U_i)
        let u_i_x = U_i
            .clone()
            .hash(&crh_params, i.clone(), z_0.clone(), z_i.clone())?;

        // check that h == u_i.x
        (u_i.x[0]).conditional_enforce_equal(&u_i_x, &is_not_basecase)?;

        // 2. u_i.cmE==cm(0), u_i.u==1
        (u_i.cmE.x.is_eq(&u_dummy.cmE.x)?)
            .conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;
        (u_i.cmE.y.is_eq(&u_dummy.cmE.y)?)
            .conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;
        (u_i.u.is_one()?).conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;

        // 3. nifs.verify, checks that folding u_i & U_i obtains U_{i+1}.
        // Notice that NIFSGadget::verify is not checking the folding of cmE & cmW, since it will
        // be done on the other curve.
        let nifs_check = NIFSGadget::<C>::verify(r, u_i, U_i.clone(), U_i1.clone())?;
        nifs_check.conditional_enforce_equal(&Boolean::TRUE, &is_not_basecase)?;

        // 4. (base case) u_{i+1}.X == H(1, z_0, F(z_0)=F(z_i)=z_i1, U_i) (with U_i being dummy)
        let u_i1_x_basecase = U_i.hash(
            &crh_params,
            FpVar::<CF1<C>>::one(),
            z_0.clone(),
            z_i1.clone(),
        )?;

        // 4. (non-base case). u_{i+1}.x = H(i+1, z_0, z_i+1, U_{i+1}), this is the output of F'
        let u_i1_x = U_i1.hash(
            &crh_params,
            i + FpVar::<CF1<C>>::one(),
            z_0.clone(),
            z_i1.clone(),
        )?;

        // if i==0: check x==u_{i+1}.x_basecase
        u_i1_x_basecase.conditional_enforce_equal(&x, &is_basecase)?;
        // else: check x==u_{i+1}.x
        u_i1_x.conditional_enforce_equal(&x, &is_not_basecase)?;

        // WIP assert that z_i1 == F(z_i)
        self.F.generate_constraints(cs.clone())?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::BigInteger;
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar};
    use ark_relations::r1cs::{ConstraintLayer, ConstraintSystem, TracingMode};
    use ark_std::One;
    use ark_std::UniformRand;
    use tracing_subscriber::layer::SubscriberExt;

    use crate::ccs::r1cs::tests::{get_test_r1cs, get_test_z};
    use crate::folding::nova::{check_instance_relation, nifs::NIFS, Witness};
    use crate::frontend::arkworks::{extract_r1cs, extract_z};
    use crate::pedersen::Pedersen;
    use crate::transcript::poseidon::{tests::poseidon_test_config, PoseidonTranscript};
    use crate::transcript::Transcript;

    #[derive(Clone, Copy, Debug)]
    /// TestFCircuit is a variation of `x^3 + x + 5 = y` (as in
    /// src/frontend/arkworks/mod.rs#tests::TestCircuit), adapted to have 2 public inputs which are
    /// used as the state. `z_i` is used as `x`, and `z_{i+1}` is used as `y`, and at the next
    /// step, `z_{i+1}` will be assigned to `z_i`, and a new `z+{i+1}` will be computted.
    pub struct TestFCircuit<F: PrimeField> {
        z_i: F,  // z_i
        z_i1: F, // z_{i+1}
    }
    impl<F: PrimeField> FCircuit<F> for TestFCircuit<F> {
        fn public(self) -> (F, F) {
            (self.z_i, self.z_i1)
        }
        fn step(&mut self) {
            self.z_i = self.z_i1;
            self.z_i1 = self.z_i * self.z_i * self.z_i + self.z_i + F::from(5_u32);
        }
    }
    impl<F: PrimeField> ConstraintSynthesizer<F> for TestFCircuit<F> {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let z_i = FpVar::<F>::new_witness(cs.clone(), || Ok(self.z_i))?;
            let z_i1 = FpVar::<F>::new_witness(cs.clone(), || Ok(self.z_i1))?;
            let five = FpVar::<F>::new_constant(cs.clone(), F::from(5u32))?;

            let y = &z_i * &z_i * &z_i + &z_i + &five;
            y.enforce_equal(&z_i1)?;
            Ok(())
        }
    }

    #[test]
    fn test_committed_instance_var() {
        let mut rng = ark_std::test_rng();

        let ci = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };

        let cs = ConstraintSystem::<Fr>::new_ref();
        let ciVar =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(ci.clone())).unwrap();
        assert_eq!(ciVar.u.value().unwrap(), ci.u);
        assert_eq!(ciVar.x.value().unwrap(), ci.x);

        // check the instantiation of the CycleFold side:
        let cs = ConstraintSystem::<Fq>::new_ref();
        let ciVar =
            CommittedInstanceCycleFoldVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(ci.clone())
            })
            .unwrap();
        assert_eq!(ciVar.cmE.value().unwrap(), ci.cmE);
        assert_eq!(ciVar.cmW.value().unwrap(), ci.cmW);
    }

    #[test]
    fn test_nifs_gadget() {
        let r1cs = get_test_r1cs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);
        let (w1, x1) = r1cs.split_z(&z1);
        let (w2, x2) = r1cs.split_z(&z2);

        let w1 = Witness::<Projective>::new(w1.clone(), r1cs.A.n_rows);
        let w2 = Witness::<Projective>::new(w2.clone(), r1cs.A.n_rows);

        let mut rng = ark_std::test_rng();
        let pedersen_params = Pedersen::<Projective>::new_params(&mut rng, r1cs.A.n_rows);

        // compute committed instances
        let ci1 = w1.commit(&pedersen_params, x1.clone());
        let ci2 = w2.commit(&pedersen_params, x2.clone());

        // get challenge from transcript
        let poseidon_config = poseidon_test_config::<Fr>();
        let mut tr = PoseidonTranscript::<Projective>::new(&poseidon_config);
        let r_bits = tr.get_challenge_nbits(128);
        let r_Fr = Fr::from_bigint(BigInteger::from_bits_le(&r_bits)).unwrap();

        let (_w3, ci3, _T, cmT) =
            NIFS::<Projective>::prove(&pedersen_params, r_Fr, &r1cs, &w1, &ci1, &w2, &ci2).unwrap();

        let ci3_verifier = NIFS::<Projective>::verify(r_Fr, &ci1, &ci2, &cmT);
        assert_eq!(ci3_verifier, ci3);

        let cs = ConstraintSystem::<Fr>::new_ref();

        let rVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(r_Fr)).unwrap();
        let ci1Var =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(ci1.clone()))
                .unwrap();
        let ci2Var =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(ci2.clone()))
                .unwrap();
        let ci3Var =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(ci3.clone()))
                .unwrap();

        let nifs_check = NIFSGadget::<Projective>::verify(
            rVar.clone(),
            ci1Var.clone(),
            ci2Var.clone(),
            ci3Var.clone(),
        )
        .unwrap();
        nifs_check.enforce_equal(&Boolean::<Fr>::TRUE).unwrap();
        assert!(cs.is_satisfied().unwrap());

        // cs_CC is the Constraint System on the Curve Cycle auxiliary curve constraints field
        // (E2::Fr)
        let cs_CC = ConstraintSystem::<Fq>::new_ref();

        let r_bitsVar = Vec::<Boolean<Fq>>::new_witness(cs_CC.clone(), || Ok(r_bits)).unwrap();

        let cmTVar = GVar::new_witness(cs_CC.clone(), || Ok(cmT)).unwrap();
        let ci1Var =
            CommittedInstanceCycleFoldVar::<Projective, GVar>::new_witness(cs_CC.clone(), || {
                Ok(ci1.clone())
            })
            .unwrap();
        let ci2Var =
            CommittedInstanceCycleFoldVar::<Projective, GVar>::new_witness(cs_CC.clone(), || {
                Ok(ci2.clone())
            })
            .unwrap();
        let ci3Var =
            CommittedInstanceCycleFoldVar::<Projective, GVar>::new_witness(cs_CC.clone(), || {
                Ok(ci3.clone())
            })
            .unwrap();

        let nifs_cf_check = NIFSCycleFoldGadget::<Projective, GVar>::verify(
            r_bitsVar, cmTVar, ci1Var, ci2Var, ci3Var,
        )
        .unwrap();
        nifs_cf_check.enforce_equal(&Boolean::<Fq>::TRUE).unwrap();
        assert!(cs_CC.is_satisfied().unwrap());
    }

    #[test]
    fn test_committed_instance_hash() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();

        let i = Fr::from(3_u32);
        let z_0 = Fr::from(3_u32);
        let z_i = Fr::from(3_u32);
        let ci = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };

        // compute the CommittedInstance hash natively
        let h = ci.hash(&poseidon_config, i, z_0, z_i).unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();

        let iVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(i)).unwrap();
        let z_0Var = FpVar::<Fr>::new_witness(cs.clone(), || Ok(z_0)).unwrap();
        let z_iVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(z_i)).unwrap();
        let ciVar =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(ci.clone())).unwrap();

        let crh_params = CRHParametersVar::<Fr>::new_constant(cs.clone(), poseidon_config).unwrap();

        // compute the CommittedInstance hash in-circuit
        let hVar = ciVar.hash(&crh_params, iVar, z_0Var, z_iVar).unwrap();
        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        assert_eq!(hVar.value().unwrap(), h);
    }

    #[test]
    /// test_augmented_f_circuit folds the TestFCircuit circuit in multiple iterations, feeding the
    /// values into the AugmentedFCircuit.
    fn test_augmented_f_circuit() {
        let mut layer = ConstraintLayer::default();
        layer.mode = TracingMode::OnlyConstraints;
        let subscriber = tracing_subscriber::Registry::default().with(layer);
        let _guard = tracing::subscriber::set_default(subscriber);

        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();

        // compute z vector for the initial instance
        let cs = ConstraintSystem::<Fr>::new_ref();

        // prepare the circuit to obtain its R1CS
        let test_F_circuit_dummy = TestFCircuit::<Fr> {
            z_i: Fr::zero(),
            z_i1: Fr::zero(),
        };
        let mut augmented_F_circuit = AugmentedFCircuit::<Projective, TestFCircuit<Fr>> {
            _c: PhantomData,
            poseidon_config: poseidon_config.clone(),
            i: None,
            z_0: None,
            u_i: None,
            U_i: None,
            U_i1: None,
            cmT: None,
            r: None,
            F: test_F_circuit_dummy,
            x: None,
        };
        augmented_F_circuit
            .generate_constraints(cs.clone())
            .unwrap();
        cs.finalize();
        let cs = cs.into_inner().unwrap();
        let r1cs = extract_r1cs::<Fr>(&cs);
        let z = extract_z::<Fr>(&cs); // includes 1 and public inputs
        let (w, x) = r1cs.split_z(&z);
        let F_witness_len = w.len();

        let mut tr = PoseidonTranscript::<Projective>::new(&poseidon_config);

        let pedersen_params = Pedersen::<Projective>::new_params(&mut rng, r1cs.A.n_rows);

        // first step
        let z_0 = Fr::from(3_u32);
        let z_i = z_0;
        let mut z_i1 = Fr::from(35_u32);

        // set the circuit to be folded with z_i=z_0=3 and z_{i+1}=35 (initial values)
        let mut test_F_circuit = TestFCircuit::<Fr> { z_i, z_i1 };

        let w_dummy = Witness::<Projective>::new(vec![Fr::zero(); F_witness_len], r1cs.A.n_rows);
        let u_dummy = CommittedInstance::<Projective>::dummy(x.len());

        // Wi is a 'dummy witness', all zeroes, but with the size corresponding to the R1CS that
        // we're working with.
        // set U_i <-- dummay instance
        let mut W_i = w_dummy.clone();
        let mut U_i = u_dummy.clone();
        check_instance_relation(&r1cs, &W_i, &U_i).unwrap();

        let mut w_i = w_dummy.clone();
        let mut u_i = u_dummy.clone();
        let (mut W_i1, mut U_i1, mut _T, mut cmT) = (
            w_dummy.clone(),
            u_dummy.clone(),
            vec![],
            Projective::generator(),
        );
        // as expected, dummy instances pass the relaxed_r1cs check
        check_instance_relation(&r1cs, &W_i1, &U_i1).unwrap();

        let mut i = Fr::zero();
        let mut u_i1_x: Fr;
        let n_steps: usize = 4;
        for _ in 0..n_steps {
            if i == Fr::zero() {
                // base case: i=0, z_i=z_0, U_i = U_d := dummy instance
                // u_1.x = H(1, z_0, z_i, U_i)
                u_i1_x = U_i.hash(&poseidon_config, Fr::one(), z_0, z_i1).unwrap();

                // base case
                augmented_F_circuit = AugmentedFCircuit::<Projective, TestFCircuit<Fr>> {
                    _c: PhantomData,
                    poseidon_config: poseidon_config.clone(),
                    i: Some(i),               // = 0
                    z_0: Some(z_0),           // = z_i=3
                    u_i: Some(u_i.clone()),   // = dummy
                    U_i: Some(U_i.clone()),   // = dummy
                    U_i1: Some(U_i1.clone()), // = dummy
                    cmT: Some(cmT),
                    r: Some(Fr::one()),
                    F: test_F_circuit,
                    x: Some(u_i1_x),
                };
            } else {
                // get challenge from transcript (since this is a test, we skip absorbing values to
                // the transcript for simplicity)
                let r_bits = tr.get_challenge_nbits(128); // TODO N_BITS_CHALLENGE
                let r_Fr = Fr::from_bigint(BigInteger::from_bits_le(&r_bits)).unwrap();

                check_instance_relation(&r1cs, &w_i, &u_i).unwrap();
                check_instance_relation(&r1cs, &W_i, &U_i).unwrap();

                // U_{i+1}
                (W_i1, U_i1, _T, cmT) = NIFS::<Projective>::prove(
                    &pedersen_params,
                    r_Fr,
                    &r1cs,
                    &w_i,
                    &u_i,
                    &W_i,
                    &U_i,
                )
                .unwrap();

                check_instance_relation(&r1cs, &W_i1, &U_i1).unwrap();

                // folded instance output (public input, x)
                // u_{i+1}.x = H(i+1, z_0, z_{i+1}, U_{i+1})
                u_i1_x = U_i1
                    .hash(&poseidon_config, i + Fr::one(), z_0, z_i1)
                    .unwrap();

                augmented_F_circuit = AugmentedFCircuit::<Projective, TestFCircuit<Fr>> {
                    _c: PhantomData,
                    poseidon_config: poseidon_config.clone(),
                    i: Some(i),
                    z_0: Some(z_0),
                    u_i: Some(u_i),
                    U_i: Some(U_i.clone()),
                    U_i1: Some(U_i1.clone()),
                    cmT: Some(cmT),
                    r: Some(r_Fr),
                    F: test_F_circuit,
                    x: Some(u_i1_x),
                };
            }

            let cs = ConstraintSystem::<Fr>::new_ref();

            augmented_F_circuit
                .generate_constraints(cs.clone())
                .unwrap();
            let is_satisfied = cs.is_satisfied().unwrap();
            if !is_satisfied {
                println!("{:?}", cs.which_is_unsatisfied());
            }
            assert!(is_satisfied);

            cs.finalize();
            let cs = cs.into_inner().unwrap();
            // notice that here we use 'Z' (uppercase) to denote the 'z-vector' as in the paper,
            // not the value 'z_i' (lowercase) which is the next state
            let Z_i1 = extract_z::<Fr>(&cs);
            let (w_i1, x_i1) = r1cs.split_z(&Z_i1);
            assert_eq!(x_i1.len(), 1);
            assert_eq!(x_i1[0], u_i1_x);

            // compute committed instances, w_{i+1}, u_{i+1}, which will be used as w_i, u_i, so we
            // assign them directly to w_i, u_i.
            w_i = Witness::<Projective>::new(w_i1.clone(), r1cs.A.n_rows);
            u_i = w_i.commit(&pedersen_params, vec![u_i1_x]);

            check_instance_relation(&r1cs, &w_i, &u_i).unwrap();
            check_instance_relation(&r1cs, &W_i1, &U_i1).unwrap();

            // set values for next iteration
            i += Fr::one();
            test_F_circuit.step(); // advance the F circuit state
            (_, z_i1) = test_F_circuit.public();
            U_i = U_i1.clone();
            W_i = W_i1.clone();
        }
    }
}
