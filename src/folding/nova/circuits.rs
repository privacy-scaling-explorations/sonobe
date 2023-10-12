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
    ) -> Result<(), SynthesisError> {
        // ensure that: ci3.u == ci1.u + r * ci2.u
        ci3.u.enforce_equal(&(ci1.u + r.clone() * ci2.u))?;

        // ensure that: ci3.x == ci1.x + r * ci2.x
        let x_rlc = ci1
            .x
            .iter()
            .zip(ci2.x)
            .map(|(a, b)| a + &r * &b)
            .collect::<Vec<FpVar<CF1<C>>>>();
        x_rlc.enforce_equal(&ci3.x)?;

        Ok(())
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
    ) -> Result<(), SynthesisError> {
        // cm(E) check: ci3.cmE == ci1.cmE + r * cmT + r^2 * ci2.cmE
        ci3.cmE.enforce_equal(
            &((ci2.cmE.scalar_mul_le(r_bits.iter())? + cmT).scalar_mul_le(r_bits.iter())?
                + ci1.cmE),
        )?;
        // cm(W) check: ci3.cmW == ci1.cmW + r * ci2.cmW
        ECRLC::<C, GC>::check(r_bits, ci1.cmW, ci2.cmW, ci3.cmW)?;
        Ok(())
    }
}

/// FCircuit defines the trait of the circuit of the F function, which is the one being executed
/// inside the agmented F' function.
pub trait FCircuit<F: PrimeField>: ConstraintSynthesizer<F> + Copy {
    /// method that returns z_i (input), z_{i+1} (output)
    fn public(self) -> (F, F);
}

/// AugmentedFCircuit implements the F' circuit (augmented F) defined in
/// [Nova](https://eprint.iacr.org/2021/370.pdf).
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
        let i = FpVar::<CF1<C>>::new_input(cs.clone(), || Ok(self.i.unwrap()))?;
        let z_0 = FpVar::<CF1<C>>::new_input(cs.clone(), || Ok(self.z_0.unwrap()))?;

        // get z_i & z_{i+1} from the folded circuit
        let (z_i_native, z_i1_native) = self.F.public();
        let z_i = FpVar::<CF1<C>>::new_input(cs.clone(), || Ok(z_i_native))?;
        let z_i1 = FpVar::<CF1<C>>::new_input(cs.clone(), || Ok(z_i1_native))?;

        let u_i = CommittedInstanceVar::<C>::new_witness(cs.clone(), || Ok(self.u_i.unwrap()))?;
        let U_i = CommittedInstanceVar::<C>::new_witness(cs.clone(), || Ok(self.U_i.unwrap()))?;
        let U_i1 = CommittedInstanceVar::<C>::new_witness(cs.clone(), || Ok(self.U_i1.unwrap()))?;
        // let cmT = NonNativeAffineVar::new_witness(cs.clone(), || Ok(self.cmT.unwrap()))?;
        let r = FpVar::<CF1<C>>::new_witness(cs.clone(), || Ok(self.r.unwrap()))?; // r will come from transcript
        let x = FpVar::<CF1<C>>::new_input(cs.clone(), || Ok(self.x.unwrap()))?;

        let crh_params =
            CRHParametersVar::<C::ScalarField>::new_constant(cs.clone(), self.poseidon_config)?;

        // if i=0, output (u_{i+1}.x), u_{i+1}.x = H(vk_nifs, 1, z_0, z_i1, u_empty)

        // (first iteration) u_i.X == H(1, z_0, z_i, U_i)
        // TODO WIP
        // let u_i_x_first_iter = U_i.clone().hash(
        //     &crh_params,
        //     FpVar::<CF1<C>>::one(),
        //     z_0.clone(),
        //     z_i.clone(),
        // );

        // 1. h_{i+1} = u_i.X == H(i, z_0, z_i, U_i)
        let u_i_x = U_i
            .clone()
            .hash(&crh_params, i.clone(), z_0.clone(), z_i.clone())?;
        // TODO WIP: x is the output when i=0

        // check that h == phi.x.
        (u_i.x[0]).enforce_equal(&u_i_x)?;

        // 2. phi.cmE==cm(0), phi.u==1
        // (phi.cmE.is_zero()?).enforce_equal(&Boolean::TRUE)?; // TODO not cmE=0, but check that cmE = cm(0)
        (u_i.u.is_one()?).enforce_equal(&Boolean::TRUE)?;

        // 3. nifs.verify, checks that folding u_i & U_i obtains U_{i+1}.
        // Notice that NIFSGadget::verify is not checking the folding of cmE & cmW, since it will
        // be done on the other curve.
        NIFSGadget::<C>::verify(r, u_i, U_i, U_i1.clone())?;

        // 4. zksnark.V(vk_snark, phi_new, proof_phi)

        // h_{i+1} == u_i.X, this is the output of F'
        // 5. (u_{i+1}.x) phiOut.x == H(i+1, z_0, z_i+1, phiBigOut)
        let h_i1 = U_i1.hash(
            &crh_params,
            i + FpVar::<CF1<C>>::one(),
            z_0.clone(),
            z_i1.clone(),
        )?;

        // check that inputed 'x' is equal to phiOut_x_first_iter or phiOut_x depending if we're at
        // i=0 or not.
        // if i==0: check x==phiOut_x_first_iter
        // u_i1_x_first_iter.enforce_equal(&x)?;
        // else: check x==h_{i+1}
        h_i1.enforce_equal(&x)?;

        // WIP assert that z_i1 == F(z_i).z_i1
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
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;
    use ark_std::{One, Zero};

    use crate::ccs::r1cs::tests::{get_test_r1cs, get_test_z};
    use crate::folding::nova::{nifs::NIFS, Witness};
    use crate::frontend::arkworks::extract_r1cs_and_z;
    use crate::pedersen::Pedersen;
    use crate::transcript::poseidon::{tests::poseidon_test_config, PoseidonTranscript};
    use crate::transcript::Transcript;

    #[derive(Clone, Copy, Debug)]
    pub struct TestFCircuit<F: PrimeField> {
        z_i: F,  // z_i
        z_i1: F, // z_{i+1}
    }
    impl<F: PrimeField> FCircuit<F> for TestFCircuit<F> {
        fn public(self) -> (F, F) {
            (self.z_i, self.z_i1)
        }
    }
    impl<F: PrimeField> ConstraintSynthesizer<F> for TestFCircuit<F> {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let z_i = FpVar::<F>::new_input(cs.clone(), || Ok(self.z_i))?;
            let z_i1 = FpVar::<F>::new_input(cs.clone(), || Ok(self.z_i1))?;
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
        let pedersen_params = Pedersen::<Projective>::new_params(&mut rng, r1cs.A.n_cols);

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

        NIFSGadget::<Projective>::verify(
            rVar.clone(),
            ci1Var.clone(),
            ci2Var.clone(),
            ci3Var.clone(),
        )
        .unwrap();
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

        NIFSCycleFoldGadget::<Projective, GVar>::verify(r_bitsVar, cmTVar, ci1Var, ci2Var, ci3Var)
            .unwrap();
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
    fn test_augmented_f_circuit() {
        // compute z vector for the initial instance
        let cs = ConstraintSystem::<Fr>::new_ref();

        let i = Fr::zero();
        let s_i = Fr::from(3_u32);
        let s_0 = s_i;
        let s_i1 = Fr::from(35_u32);
        let test_F_circuit = TestFCircuit::<Fr> {
            z_i: s_i,
            z_i1: s_i1,
        };
        test_F_circuit.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        assert!(cs.is_satisfied().unwrap());

        let cs = cs.into_inner().unwrap();
        let (r1cs, z0) = extract_r1cs_and_z::<Fr>(&cs);
        // let (w0, x0) = r1cs.split_z(&z0);

        let mut rng = ark_std::test_rng();
        let pedersen_params = Pedersen::<Projective>::new_params(&mut rng, r1cs.A.n_cols);
        let poseidon_config = poseidon_test_config::<Fr>();

        // dummy instance
        let dummy_instance = CommittedInstance::<Projective>::empty(&pedersen_params);
        // base case output:
        // u_0.x = H(0, s_0, s_0, U_d) (U_d := dummy instance)
        let u0_x = dummy_instance.hash(&poseidon_config, i, s_0, s_i).unwrap();
        let U0 = dummy_instance.clone();

        // compute committed instances
        let w0 = Witness::<Projective>::new(z0.clone(), r1cs.A.n_rows);
        let u0 = w0.commit(&pedersen_params, vec![u0_x]);

        // get challenge from transcript
        let mut tr = PoseidonTranscript::<Projective>::new(&poseidon_config);
        let r_bits = tr.get_challenge_nbits(128);
        let r_Fr = Fr::from_bigint(BigInteger::from_bits_le(&r_bits)).unwrap();

        let (_w3, U1, _T, cmT) = NIFS::<Projective>::prove(
            &pedersen_params,
            r_Fr,
            &r1cs,
            &w0,
            &u0,
            &w0.clone(),
            &U0.clone(),
        )
        .unwrap();

        // folded instance output (public input, x)
        // ci3_x = u_{i+1}.x = H(i+1, s_0, s_{i+1}, U_{i+1})
        let u1_x = U1.hash(&poseidon_config, i + Fr::one(), s_i, s_i1).unwrap();

        // new ConstraintSystem
        let cs = ConstraintSystem::<Fr>::new_ref();

        let augmented_F_circuit = AugmentedFCircuit::<Projective, TestFCircuit<Fr>> {
            _c: PhantomData,
            poseidon_config,
            i: Some(i),
            z_0: Some(s_0),
            u_i: Some(u0),
            U_i: Some(U0),
            U_i1: Some(U1),
            cmT: Some(cmT),
            r: Some(r_Fr),
            F: test_F_circuit,
            x: Some(u1_x),
        };

        augmented_F_circuit
            .generate_constraints(cs.clone())
            .unwrap();
        assert!(cs.is_satisfied().unwrap());
        println!("num_constraints={:?}", cs.num_constraints());
    }
}
