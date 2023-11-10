/// contains [CycleFold](https://eprint.iacr.org/2023/1192.pdf) related circuits
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, nonnative::NonNativeFieldVar},
    groups::GroupOpsBounds,
    prelude::CurveVar,
    ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::fmt::Debug;
use ark_std::Zero;
use core::{borrow::Borrow, marker::PhantomData};

use super::circuits::CF2;
use super::CommittedInstance;
use crate::constants::N_BITS_RO;
use crate::folding::circuits::nonnative::{
    scalar_to_nonnative_limbs, scalar_vec_to_nonnative_limbs,
};

// publi inputs length for the CycleFoldCircuit, |[u_i, U_i, U_{i+1}]|
pub const CF_IO_LEN: usize = 12;

/// CycleFoldCommittedInstance is like the normal Nova CommittedInstance, but with its values over
/// the Nova's circuit field (=E2.Fq)
#[derive(Debug, Clone)]
pub struct CycleFoldCommittedInstance<C: CurveGroup> {
    pub cmE: C,
    pub u: C::BaseField,
    pub cmW: C,
    pub x: Vec<C::BaseField>,
}
impl<C: CurveGroup> CycleFoldCommittedInstance<C> {
    pub fn dummy(io_len: usize) -> Self {
        Self {
            cmE: C::zero(),
            u: C::BaseField::zero(),
            cmW: C::zero(),
            x: vec![C::BaseField::zero(); io_len],
        }
    }
}

/// CycleFoldCommittedInstanceVar is the CycleFold CommittedInstance representation in the Nova
/// circuit.
#[derive(Debug, Clone)]
pub struct CycleFoldCommittedInstanceVar<C: CurveGroup, GC: CurveVar<C, CF2<C>>>
where
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    _c: PhantomData<C>,
    pub cmE: GC,
    pub u: NonNativeFieldVar<C::ScalarField, CF2<C>>,
    pub cmW: GC,
    pub x: Vec<NonNativeFieldVar<C::ScalarField, CF2<C>>>,
}
impl<C, GC> AllocVar<CommittedInstance<C>, CF2<C>> for CycleFoldCommittedInstanceVar<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>>,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
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
            let u = NonNativeFieldVar::<C::ScalarField, CF2<C>>::new_variable(
                cs.clone(),
                || Ok(val.borrow().u),
                mode,
            )?;
            let x = Vec::<NonNativeFieldVar<C::ScalarField, CF2<C>>>::new_variable(
                cs.clone(),
                || Ok(val.borrow().x.clone()),
                mode,
            )?;

            Ok(Self {
                _c: PhantomData,
                cmE,
                u,
                cmW,
                x,
            })
        })
    }
}

/// CommittedInstanceInCycleFoldVar represents the Nova CommittedInstance in the CycleFold circuit,
/// where the commitments to E and W (cmW and cmW) from the CommittedInstance on the E2,
/// represented as native points, which are folded on the auxiliary curve constraints field (E2::Fr
/// = E1::Fq).
#[derive(Debug, Clone)]
pub struct CommittedInstanceInCycleFoldVar<C: CurveGroup, GC: CurveVar<C, CF2<C>>>
where
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    _c: PhantomData<C>,
    pub cmE: GC,
    pub cmW: GC,
}

impl<C, GC> AllocVar<CommittedInstance<C>, CF2<C>> for CommittedInstanceInCycleFoldVar<C, GC>
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

/// NIFSinCycleFoldGadget performs the Nova NIFS.V elliptic curve points relation checks in the other
/// curve (natively) following [CycleFold](https://eprint.iacr.org/2023/1192.pdf).
pub struct NIFSinCycleFoldGadget<C: CurveGroup, GC: CurveVar<C, CF2<C>>> {
    _c: PhantomData<C>,
    _gc: PhantomData<GC>,
}
impl<C: CurveGroup, GC: CurveVar<C, CF2<C>>> NIFSinCycleFoldGadget<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>>,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    pub fn verify(
        r_bits: Vec<Boolean<CF2<C>>>,
        cmT: GC,
        ci1: CommittedInstanceInCycleFoldVar<C, GC>,
        ci2: CommittedInstanceInCycleFoldVar<C, GC>,
        ci3: CommittedInstanceInCycleFoldVar<C, GC>,
    ) -> Result<Boolean<CF2<C>>, SynthesisError> {
        // cm(E) check: ci3.cmE == ci1.cmE + r * cmT + r^2 * ci2.cmE
        let first_check = ci3.cmE.is_eq(
            &((ci2.cmE.scalar_mul_le(r_bits.iter())? + cmT).scalar_mul_le(r_bits.iter())?
                + ci1.cmE),
        )?;
        // cm(W) check: ci3.cmW == ci1.cmW + r * ci2.cmW
        let second_check = ci3
            .cmW
            .is_eq(&(ci1.cmW + ci2.cmW.scalar_mul_le(r_bits.iter())?))?;

        first_check.and(&second_check)
    }
}

/// This is the gadget used in the AugmentedFCircuit to verify the CycleFold instances folding,
/// which checks the correct RLC of u,x,cmE,cmW (hence the name containing 'Full', since it checks
/// all the RLC values, not only the native ones). It assumes that ci2.cmE=0, ci2.u=1.
pub struct NIFSFullGadget<C: CurveGroup, GC: CurveVar<C, CF2<C>>> {
    _c: PhantomData<C>,
    _gc: PhantomData<GC>,
}
impl<C: CurveGroup, GC: CurveVar<C, CF2<C>>> NIFSFullGadget<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>>,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    pub fn verify(
        r_bits: Vec<Boolean<CF2<C>>>,
        r_nonnat: NonNativeFieldVar<C::ScalarField, CF2<C>>,
        cmT: GC,
        // ci1 is assumed to be always with cmE=0, u=1 (checks done previous to this method)
        ci1: CycleFoldCommittedInstanceVar<C, GC>,
        ci2: CycleFoldCommittedInstanceVar<C, GC>,
        ci3: CycleFoldCommittedInstanceVar<C, GC>,
    ) -> Result<Boolean<CF2<C>>, SynthesisError> {
        // cm(E) check: ci3.cmE == ci1.cmE + r * cmT (ci2.cmE=0)
        let first_check = ci3
            .cmE
            .is_eq(&(cmT.scalar_mul_le(r_bits.iter())? + ci1.cmE))?;

        // cm(W) check: ci3.cmW == ci1.cmW + r * ci2.cmW
        let second_check = ci3
            .cmW
            .is_eq(&(ci1.cmW + ci2.cmW.scalar_mul_le(r_bits.iter())?))?;

        let u_rlc: NonNativeFieldVar<C::ScalarField, CF2<C>> = ci1.u + r_nonnat.clone();
        let third_check = u_rlc.is_eq(&ci3.u)?;

        // ensure that: ci3.x == ci1.x + r * ci2.x
        let x_rlc: Vec<NonNativeFieldVar<C::ScalarField, CF2<C>>> = ci1
            .x
            .iter()
            .zip(ci2.x)
            .map(|(a, b)| a + &r_nonnat * &b)
            .collect::<Vec<NonNativeFieldVar<C::ScalarField, CF2<C>>>>();
        let fourth_check = x_rlc.is_eq(&ci3.x)?;

        first_check
            .and(&second_check)?
            .and(&third_check)?
            .and(&fourth_check)
    }
}

/// ChallengeGadget computes the RO challenge used for the CycleFold instances NIFS, it contains a
/// rust-native and a in-circuit compatible versions.
pub struct CycleFoldChallengeGadget<C: CurveGroup, GC: CurveVar<C, CF2<C>>> {
    _c: PhantomData<C>, // Nova's Curve2, the one used for the CycleFold circuit
    _gc: PhantomData<GC>,
}
impl<C, GC> CycleFoldChallengeGadget<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>>,
    <C as CurveGroup>::BaseField: PrimeField,
    <C as CurveGroup>::BaseField: Absorb,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    pub fn get_challenge_native(
        poseidon_config: &PoseidonConfig<C::BaseField>,
        u_i: CommittedInstance<C>,
        U_i: CommittedInstance<C>,
        _cmT: C,
    ) -> Result<Vec<bool>, SynthesisError> {
        let mut sponge = PoseidonSponge::<C::BaseField>::new(poseidon_config);
        let input: Vec<C::BaseField> = [
            scalar_to_nonnative_limbs::<C>(u_i.u)?,
            scalar_vec_to_nonnative_limbs::<C>(u_i.x)?,
            scalar_to_nonnative_limbs::<C>(U_i.u)?,
            scalar_vec_to_nonnative_limbs::<C>(U_i.x)?,
            // depends on the gadget version (get_challenge_gadget)
        ]
        .concat();
        sponge.absorb(&input);
        let bits = sponge.squeeze_bits(N_BITS_RO);
        Ok(bits)
    }
    // compatible with the native get_challenge_native
    pub fn get_challenge_gadget(
        cs: ConstraintSystemRef<C::BaseField>,
        poseidon_config: &PoseidonConfig<C::BaseField>,
        u_i: CycleFoldCommittedInstanceVar<C, GC>,
        // this is u_i.x, which is already computed previous to this method call, so we don't need
        // to duplicate constraints
        u_i_x: Vec<FpVar<CF2<C>>>,
        U_i: CycleFoldCommittedInstanceVar<C, GC>,
        _cmT: GC,
    ) -> Result<Vec<Boolean<C::BaseField>>, SynthesisError> {
        let mut sponge = PoseidonSpongeVar::<C::BaseField>::new(cs, poseidon_config);

        let mut U_i_x: Vec<FpVar<CF2<C>>> = vec![];
        for x_i in U_i.x.iter() {
            let mut x_fpvar = x_i.to_constraint_field()?;
            U_i_x.append(&mut x_fpvar);
        }

        let input: Vec<FpVar<C::BaseField>> = [
            u_i.u.to_constraint_field()?,
            u_i_x,
            U_i.u.to_constraint_field()?,
            U_i_x,
            // TODO add x,y coordinates of u_i.{cmE,cmW}, U_i.{cmE,cmW}, cmT. Depends exposing x,y
            // coordinates of GC.
            // Issue to keep track of this: https://github.com/privacy-scaling-explorations/folding-schemes/issues/44
        ]
        .concat();
        sponge.absorb(&input)?;
        let bits = sponge.squeeze_bits(N_BITS_RO)?;
        Ok(bits)
    }
}

/// CycleFoldCircuit contains the constraints that check the correct fold of the committed
/// instances from Curve1. Namely, it checks the random linear combinations of the elliptic curve
/// (Curve1) points of u_i, U_i leading to U_{i+1}
#[derive(Debug, Clone)]
pub struct CycleFoldCircuit<C: CurveGroup, GC: CurveVar<C, CF2<C>>> {
    pub _gc: PhantomData<GC>,
    pub r_bits: Option<Vec<bool>>,
    pub cmT: Option<C>,
    // u_i,U_i,U_i1 are the nova instances from AugmentedFCircuit which will be (their elliptic
    // curve points) checked natively in CycleFoldCircuit
    pub u_i: Option<CommittedInstance<C>>,
    pub U_i: Option<CommittedInstance<C>>,
    pub U_i1: Option<CommittedInstance<C>>,
    pub x: Option<Vec<CF2<C>>>, // public inputs (cf_u_{i+1}.x)
}
impl<C: CurveGroup, GC: CurveVar<C, CF2<C>>> CycleFoldCircuit<C, GC> {
    pub fn empty() -> Self {
        Self {
            _gc: PhantomData,
            r_bits: None,
            cmT: None,
            u_i: None,
            U_i: None,
            U_i1: None,
            x: None,
        }
    }
}
impl<C, GC> ConstraintSynthesizer<CF2<C>> for CycleFoldCircuit<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>>,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF2<C>>) -> Result<(), SynthesisError> {
        let r_bits: Vec<Boolean<CF2<C>>> = Vec::new_witness(cs.clone(), || {
            Ok(self.r_bits.unwrap_or(vec![false; N_BITS_RO]))
        })?;
        let cmT = GC::new_witness(cs.clone(), || Ok(self.cmT.unwrap_or(C::zero())))?;

        let u_dummy_native = CommittedInstance::<C>::dummy(1);

        let u_i = CommittedInstanceInCycleFoldVar::<C, GC>::new_witness(cs.clone(), || {
            Ok(self.u_i.unwrap_or(u_dummy_native.clone()))
        })?;
        let U_i = CommittedInstanceInCycleFoldVar::<C, GC>::new_witness(cs.clone(), || {
            Ok(self.U_i.unwrap_or(u_dummy_native.clone()))
        })?;
        let U_i1 = CommittedInstanceInCycleFoldVar::<C, GC>::new_witness(cs.clone(), || {
            Ok(self.U_i1.unwrap_or(u_dummy_native.clone()))
        })?;
        let _x = Vec::<FpVar<CF2<C>>>::new_input(cs.clone(), || {
            Ok(self.x.unwrap_or(vec![CF2::<C>::zero(); CF_IO_LEN]))
        })?;
        #[cfg(test)]
        assert_eq!(_x.len(), CF_IO_LEN); // non-constrained sanity check

        // fold the original Nova instances natively in CycleFold
        let v =
            NIFSinCycleFoldGadget::<C, GC>::verify(r_bits.clone(), cmT, u_i.clone(), U_i, U_i1)?;
        v.enforce_equal(&Boolean::TRUE)?;

        // check that x == [u_i, U_i, U_{i+1}], check that the cmW & cmW from u_i, U_i, U_{i+1} in
        // the CycleFoldCircuit are the sames used in the public inputs 'x', which come from the
        // AugmentedFCircuit.
        // TODO: Issue to keep track of this: https://github.com/privacy-scaling-explorations/folding-schemes/issues/44

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_ff::BigInteger;
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use crate::folding::nova::nifs::tests::prepare_simple_fold_inputs;
    use crate::transcript::poseidon::tests::poseidon_test_config;

    #[test]
    fn test_committed_instance_cyclefold_var() {
        let mut rng = ark_std::test_rng();

        let ci = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };

        // check the instantiation of the CycleFold side:
        let cs = ConstraintSystem::<Fq>::new_ref();
        let ciVar =
            CommittedInstanceInCycleFoldVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(ci.clone())
            })
            .unwrap();
        assert_eq!(ciVar.cmE.value().unwrap(), ci.cmE);
        assert_eq!(ciVar.cmW.value().unwrap(), ci.cmW);
    }

    #[test]
    fn test_nifs_gadget_cyclefold() {
        let (_, _, _, _, ci1, _, ci2, _, ci3, _, cmT, r_bits, _) = prepare_simple_fold_inputs();

        // cs is the Constraint System on the Curve Cycle auxiliary curve constraints field
        // (E2::Fr)
        let cs = ConstraintSystem::<Fq>::new_ref();

        let r_bitsVar = Vec::<Boolean<Fq>>::new_witness(cs.clone(), || Ok(r_bits)).unwrap();

        let cmTVar = GVar::new_witness(cs.clone(), || Ok(cmT)).unwrap();
        let ci1Var =
            CommittedInstanceInCycleFoldVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(ci1.clone())
            })
            .unwrap();
        let ci2Var =
            CommittedInstanceInCycleFoldVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(ci2.clone())
            })
            .unwrap();
        let ci3Var =
            CommittedInstanceInCycleFoldVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(ci3.clone())
            })
            .unwrap();

        let nifs_cf_check = NIFSinCycleFoldGadget::<Projective, GVar>::verify(
            r_bitsVar, cmTVar, ci1Var, ci2Var, ci3Var,
        )
        .unwrap();
        nifs_cf_check.enforce_equal(&Boolean::<Fq>::TRUE).unwrap();
        assert!(cs.is_satisfied().unwrap());
        dbg!(cs.num_constraints());
    }

    #[test]
    fn test_nifs_full_gadget() {
        let (_, _, _, _, ci1, _, ci2, _, ci3, _, cmT, r_bits, r_Fr) = prepare_simple_fold_inputs();

        let cs = ConstraintSystem::<Fq>::new_ref();

        let r_nonnatVar =
            NonNativeFieldVar::<Fr, Fq>::new_witness(cs.clone(), || Ok(r_Fr)).unwrap();
        let r_bitsVar = Vec::<Boolean<Fq>>::new_witness(cs.clone(), || Ok(r_bits)).unwrap();

        let ci1Var =
            CycleFoldCommittedInstanceVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(ci1.clone())
            })
            .unwrap();
        let ci2Var =
            CycleFoldCommittedInstanceVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(ci2.clone())
            })
            .unwrap();
        let ci3Var =
            CycleFoldCommittedInstanceVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(ci3.clone())
            })
            .unwrap();
        let cmTVar = GVar::new_witness(cs.clone(), || Ok(cmT)).unwrap();

        let nifs_check = NIFSFullGadget::<Projective, GVar>::verify(
            r_bitsVar,
            r_nonnatVar,
            cmTVar,
            ci1Var,
            ci2Var,
            ci3Var,
        )
        .unwrap();
        nifs_check.enforce_equal(&Boolean::<Fq>::TRUE).unwrap();
        assert!(cs.is_satisfied().unwrap());
        dbg!(cs.num_constraints());
    }

    #[test]
    fn test_cyclefold_challenge_gadget() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fq>();

        let u_i = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); CF_IO_LEN],
        };
        let U_i = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); CF_IO_LEN],
        };
        let cmT = Projective::rand(&mut rng);

        // compute the challenge natively
        let r_bits = CycleFoldChallengeGadget::<Projective, GVar>::get_challenge_native(
            &poseidon_config,
            u_i.clone(),
            U_i.clone(),
            cmT,
        )
        .unwrap();

        let cs = ConstraintSystem::<Fq>::new_ref();
        let u_iVar =
            CycleFoldCommittedInstanceVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(u_i.clone())
            })
            .unwrap();
        let U_iVar =
            CycleFoldCommittedInstanceVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(U_i.clone())
            })
            .unwrap();
        let cmTVar = GVar::new_witness(cs.clone(), || Ok(cmT)).unwrap();

        // compute the challenge in-circuit
        let mut u_iVar_x: Vec<FpVar<CF2<Projective>>> = vec![];
        for x_i in u_iVar.x.iter() {
            let mut x_fpvar = x_i.to_constraint_field().unwrap();
            u_iVar_x.append(&mut x_fpvar);
        }
        let r_bitsVar = CycleFoldChallengeGadget::<Projective, GVar>::get_challenge_gadget(
            cs.clone(),
            &poseidon_config,
            u_iVar,
            u_iVar_x,
            U_iVar,
            cmTVar,
        )
        .unwrap();
        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        let rVar = Boolean::le_bits_to_fp_var(&r_bitsVar).unwrap();
        let r = Fq::from_bigint(BigInteger::from_bits_le(&r_bits)).unwrap();
        assert_eq!(rVar.value().unwrap(), r);
        assert_eq!(r_bitsVar.value().unwrap(), r_bits);
    }
}
