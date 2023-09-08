use ark_crypto_primitives::crh::{
    poseidon::constraints::{CRHGadget, CRHParametersVar},
    CRHSchemeGadget,
};
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{AffineRepr, CurveGroup, Group};
use ark_ff::Field;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::fp::FpVar,
    groups::GroupOpsBounds,
    prelude::CurveVar,
    ToConstraintFieldGadget,
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use core::{borrow::Borrow, marker::PhantomData};

use super::CommittedInstance;
use crate::folding::circuits::{cyclefold::ECRLC, nonnative::NonNativeAffineVar};

/// CF1 represents the ConstraintField used for the main Nova circuit which is over E1::Fr.
pub type CF1<C> = <<C as CurveGroup>::Affine as AffineRepr>::ScalarField;
/// CF2 represents the ConstraintField used for the CycleFold circuit which is over E2::Fr=E1::Fq.
pub type CF2<C> = <<C as CurveGroup>::BaseField as Field>::BasePrimeField;

/// CommittedInstance on E1 contains the u, x, cmE and cmW values which are folded on the main Nova
/// constraints field (E1::Fr).
#[derive(Debug, Clone)]
pub struct CommittedInstanceVar<C: CurveGroup> {
    _c: PhantomData<C>,
    u: FpVar<C::ScalarField>,
    x: Vec<FpVar<C::ScalarField>>,
    #[allow(dead_code)] // tmp while we don't have the code of the AugmentedFGadget
    cmE: NonNativeAffineVar<CF2<C>, C::ScalarField>,
    cmW: NonNativeAffineVar<CF2<C>, C::ScalarField>,
}

impl<C> AllocVar<CommittedInstance<C>, CF1<C>> for CommittedInstanceVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
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
    #[allow(dead_code)] // tmp while we don't have the code of the AugmentedFGadget
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

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{BigInteger, PrimeField};
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use crate::ccs::r1cs::tests::{get_test_r1cs, get_test_z};
    use crate::folding::nova::{nifs::NIFS, Witness};
    use crate::pedersen::Pedersen;
    use crate::transcript::poseidon::{tests::poseidon_test_config, PoseidonTranscript};
    use crate::transcript::Transcript;

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
}
