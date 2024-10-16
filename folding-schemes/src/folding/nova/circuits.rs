/// contains [Nova](https://eprint.iacr.org/2021/370.pdf) related circuits
use ark_crypto_primitives::sponge::{
    constraints::{AbsorbGadget, CryptographicSpongeVar},
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig},
    Absorb, CryptographicSponge,
};
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    groups::GroupOpsBounds,
    prelude::CurveVar,
    uint8::UInt8,
    R1CSVar, ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::{fmt::Debug, One, Zero};
use core::{borrow::Borrow, marker::PhantomData};

use super::{CommittedInstance, NovaCycleFoldConfig};
use crate::folding::circuits::{
    cyclefold::{
        CycleFoldChallengeGadget, CycleFoldCommittedInstance, CycleFoldCommittedInstanceVar,
        CycleFoldConfig, NIFSFullGadget,
    },
    nonnative::{affine::NonNativeAffineVar, uint::NonNativeUintVar},
    CF1, CF2,
};
use crate::frontend::FCircuit;
use crate::transcript::{AbsorbNonNativeGadget, Transcript, TranscriptVar};
use crate::{
    constants::NOVA_N_BITS_RO,
    folding::traits::{CommittedInstanceVarOps, Dummy},
};

/// CommittedInstanceVar contains the u, x, cmE and cmW values which are folded on the main Nova
/// constraints field (E1::Fr, where E1 is the main curve). The peculiarity is that cmE and cmW are
/// represented non-natively over the constraint field.
#[derive(Debug, Clone)]
pub struct CommittedInstanceVar<C: CurveGroup> {
    pub u: FpVar<C::ScalarField>,
    pub x: Vec<FpVar<C::ScalarField>>,
    pub cmE: NonNativeAffineVar<C>,
    pub cmW: NonNativeAffineVar<C>,
}

impl<C> AllocVar<CommittedInstance<C>, CF1<C>> for CommittedInstanceVar<C>
where
    C: CurveGroup,
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

            let cmE =
                NonNativeAffineVar::<C>::new_variable(cs.clone(), || Ok(val.borrow().cmE), mode)?;
            let cmW =
                NonNativeAffineVar::<C>::new_variable(cs.clone(), || Ok(val.borrow().cmW), mode)?;

            Ok(Self { u, x, cmE, cmW })
        })
    }
}

impl<C> AbsorbGadget<C::ScalarField> for CommittedInstanceVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<C::ScalarField>>, SynthesisError> {
        FpVar::batch_to_sponge_bytes(&self.to_sponge_field_elements()?)
    }

    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<C::ScalarField>>, SynthesisError> {
        Ok([
            vec![self.u.clone()],
            self.x.clone(),
            self.cmE.to_constraint_field()?,
            self.cmW.to_constraint_field()?,
        ]
        .concat())
    }
}

impl<C: CurveGroup> CommittedInstanceVarOps<C> for CommittedInstanceVar<C> {
    type PointVar = NonNativeAffineVar<C>;

    fn get_commitments(&self) -> Vec<Self::PointVar> {
        vec![self.cmW.clone(), self.cmE.clone()]
    }

    fn get_public_inputs(&self) -> &[FpVar<CF1<C>>] {
        &self.x
    }

    fn enforce_incoming(&self) -> Result<(), SynthesisError> {
        let zero = NonNativeUintVar::new_constant(ConstraintSystemRef::None, CF2::<C>::zero())?;
        self.cmE.x.enforce_equal_unaligned(&zero)?;
        self.cmE.y.enforce_equal_unaligned(&zero)?;
        self.u.enforce_equal(&FpVar::one())
    }

    fn enforce_partial_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        self.u.enforce_equal(&other.u)?;
        self.x.enforce_equal(&other.x)
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
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    pub fn fold_committed_instance(
        r: FpVar<CF1<C>>,
        ci1: CommittedInstanceVar<C>, // U_i
        ci2: CommittedInstanceVar<C>, // u_i
    ) -> Result<CommittedInstanceVar<C>, SynthesisError> {
        Ok(CommittedInstanceVar {
            cmE: NonNativeAffineVar::new_constant(ConstraintSystemRef::None, C::zero())?,
            cmW: NonNativeAffineVar::new_constant(ConstraintSystemRef::None, C::zero())?,
            // ci3.u = ci1.u + r * ci2.u
            u: ci1.u + &r * ci2.u,
            // ci3.x = ci1.x + r * ci2.x
            x: ci1
                .x
                .iter()
                .zip(ci2.x)
                .map(|(a, b)| a + &r * &b)
                .collect::<Vec<FpVar<CF1<C>>>>(),
        })
    }

    /// Implements the constraints for NIFS.V for u and x, since cm(E) and cm(W) are delegated to
    /// the CycleFold circuit.
    pub fn verify(
        r: FpVar<CF1<C>>,
        ci1: CommittedInstanceVar<C>, // U_i
        ci2: CommittedInstanceVar<C>, // u_i
        ci3: CommittedInstanceVar<C>, // U_{i+1}
    ) -> Result<(), SynthesisError> {
        let ci = Self::fold_committed_instance(r, ci1, ci2)?;

        ci.u.enforce_equal(&ci3.u)?;
        ci.x.enforce_equal(&ci3.x)?;

        Ok(())
    }
}

/// ChallengeGadget computes the RO challenge used for the Nova instances NIFS, it contains a
/// rust-native and a in-circuit compatible versions.
pub struct ChallengeGadget<C: CurveGroup, CI: Absorb> {
    _c: PhantomData<C>,
    _ci: PhantomData<CI>,
}
impl<C: CurveGroup, CI: Absorb> ChallengeGadget<C, CI>
where
    C: CurveGroup,
    <C as CurveGroup>::BaseField: PrimeField,
    <C as Group>::ScalarField: Absorb,
{
    pub fn get_challenge_native<T: Transcript<C::ScalarField>>(
        transcript: &mut T,
        pp_hash: C::ScalarField, // public params hash
        U_i: &CI,
        u_i: &CI,
        cmT: Option<&C>,
    ) -> Vec<bool> {
        transcript.absorb(&pp_hash);
        transcript.absorb(&U_i);
        transcript.absorb(&u_i);
        // in the Nova case we absorb the cmT, in Ova case we don't since it is not used.
        if let Some(cmT_value) = cmT {
            transcript.absorb_nonnative(cmT_value);
        }
        transcript.squeeze_bits(NOVA_N_BITS_RO)
    }

    // compatible with the native get_challenge_native
    pub fn get_challenge_gadget<S: CryptographicSponge, T: TranscriptVar<CF1<C>, S>>(
        transcript: &mut T,
        pp_hash: FpVar<CF1<C>>,      // public params hash
        U_i_vec: Vec<FpVar<CF1<C>>>, // apready processed input, so we don't have to recompute these values
        u_i: CommittedInstanceVar<C>,
        cmT: Option<NonNativeAffineVar<C>>,
    ) -> Result<Vec<Boolean<C::ScalarField>>, SynthesisError> {
        transcript.absorb(&pp_hash)?;
        transcript.absorb(&U_i_vec)?;
        transcript.absorb(&u_i)?;
        // in the Nova case we absorb the cmT, in Ova case we don't since it is not used.
        if let Some(cmT_value) = cmT {
            transcript.absorb_nonnative(&cmT_value)?;
        }
        transcript.squeeze_bits(NOVA_N_BITS_RO)
    }
}

/// `AugmentedFCircuit` enhances the original step function `F`, so that it can
/// be used in recursive arguments such as IVC.
///
/// The method for converting `F` to `AugmentedFCircuit` (`F'`) is defined in
/// [Nova](https://eprint.iacr.org/2021/370.pdf), where `AugmentedFCircuit` not
/// only invokes `F`, but also adds additional constraints for verifying the
/// correct folding of primary instances (i.e., Nova's `CommittedInstance`s over
/// `C1`).
///
/// Furthermore, to reduce circuit size over `C2`, we implement the constraints
/// defined in [CycleFold](https://eprint.iacr.org/2023/1192.pdf). These extra
/// constraints verify the correct folding of CycleFold instances.
#[derive(Debug, Clone)]
pub struct AugmentedFCircuit<
    C1: CurveGroup,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<CF1<C1>>,
> where
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    pub(super) _gc2: PhantomData<GC2>,
    pub(super) poseidon_config: PoseidonConfig<CF1<C1>>,
    pub(super) pp_hash: Option<CF1<C1>>,
    pub(super) i: Option<CF1<C1>>,
    pub(super) i_usize: Option<usize>,
    pub(super) z_0: Option<Vec<C1::ScalarField>>,
    pub(super) z_i: Option<Vec<C1::ScalarField>>,
    pub(super) external_inputs: Option<Vec<C1::ScalarField>>,
    pub(super) u_i_cmW: Option<C1>,
    pub(super) U_i: Option<CommittedInstance<C1>>,
    pub(super) U_i1_cmE: Option<C1>,
    pub(super) U_i1_cmW: Option<C1>,
    pub(super) cmT: Option<C1>,
    pub(super) F: FC,              // F circuit
    pub(super) x: Option<CF1<C1>>, // public input (u_{i+1}.x[0])

    // cyclefold verifier on C1
    // Here 'cf1, cf2' are for each of the CycleFold circuits, corresponding to the fold of cmW and
    // cmE respectively
    pub(super) cf1_u_i_cmW: Option<C2>, // input
    pub(super) cf2_u_i_cmW: Option<C2>, // input
    pub(super) cf_U_i: Option<CycleFoldCommittedInstance<C2>>, // input
    pub(super) cf1_cmT: Option<C2>,
    pub(super) cf2_cmT: Option<C2>,
    pub(super) cf_x: Option<CF1<C1>>, // public input (u_{i+1}.x[1])
}

impl<C1: CurveGroup, C2: CurveGroup, GC2: CurveVar<C2, CF2<C2>>, FC: FCircuit<CF1<C1>>>
    AugmentedFCircuit<C1, C2, GC2, FC>
where
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    pub fn empty(poseidon_config: &PoseidonConfig<CF1<C1>>, F_circuit: FC) -> Self {
        Self {
            _gc2: PhantomData,
            poseidon_config: poseidon_config.clone(),
            pp_hash: None,
            i: None,
            i_usize: None,
            z_0: None,
            z_i: None,
            external_inputs: None,
            u_i_cmW: None,
            U_i: None,
            U_i1_cmE: None,
            U_i1_cmW: None,
            cmT: None,
            F: F_circuit,
            x: None,
            // cyclefold values
            cf1_u_i_cmW: None,
            cf2_u_i_cmW: None,
            cf_U_i: None,
            cf1_cmT: None,
            cf2_cmT: None,
            cf_x: None,
        }
    }
}

impl<C1, C2, GC2, FC> ConstraintSynthesizer<CF1<C1>> for AugmentedFCircuit<C1, C2, GC2, FC>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<CF1<C1>>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
        let pp_hash = FpVar::<CF1<C1>>::new_witness(cs.clone(), || {
            Ok(self.pp_hash.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let i = FpVar::<CF1<C1>>::new_witness(cs.clone(), || {
            Ok(self.i.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let z_0 = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self
                .z_0
                .unwrap_or(vec![CF1::<C1>::zero(); self.F.state_len()]))
        })?;
        let z_i = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self
                .z_i
                .unwrap_or(vec![CF1::<C1>::zero(); self.F.state_len()]))
        })?;
        let external_inputs = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self
                .external_inputs
                .unwrap_or(vec![CF1::<C1>::zero(); self.F.external_inputs_len()]))
        })?;

        let u_dummy = CommittedInstance::dummy(2);
        let U_i = CommittedInstanceVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.U_i.unwrap_or(u_dummy.clone()))
        })?;
        let U_i1_cmE = NonNativeAffineVar::new_witness(cs.clone(), || {
            Ok(self.U_i1_cmE.unwrap_or_else(C1::zero))
        })?;
        let U_i1_cmW = NonNativeAffineVar::new_witness(cs.clone(), || {
            Ok(self.U_i1_cmW.unwrap_or_else(C1::zero))
        })?;

        let cmT =
            NonNativeAffineVar::new_witness(cs.clone(), || Ok(self.cmT.unwrap_or_else(C1::zero)))?;

        let cf_u_dummy = CycleFoldCommittedInstance::dummy(NovaCycleFoldConfig::<C1>::IO_LEN);
        let cf_U_i = CycleFoldCommittedInstanceVar::<C2, GC2>::new_witness(cs.clone(), || {
            Ok(self.cf_U_i.unwrap_or(cf_u_dummy.clone()))
        })?;
        let cf1_cmT = GC2::new_witness(cs.clone(), || Ok(self.cf1_cmT.unwrap_or_else(C2::zero)))?;
        let cf2_cmT = GC2::new_witness(cs.clone(), || Ok(self.cf2_cmT.unwrap_or_else(C2::zero)))?;

        // `sponge` is for digest computation.
        let sponge = PoseidonSpongeVar::<C1::ScalarField>::new(cs.clone(), &self.poseidon_config);
        // `transcript` is for challenge generation.
        let mut transcript = sponge.clone();

        let is_basecase = i.is_zero()?;

        // Primary Part
        // P.1. Compute u_i.x
        // u_i.x[0] = H(i, z_0, z_i, U_i)
        let (u_i_x, U_i_vec) = U_i.clone().hash(&sponge, &pp_hash, &i, &z_0, &z_i)?;
        // u_i.x[1] = H(cf_U_i)
        let (cf_u_i_x, cf_U_i_vec) = cf_U_i.clone().hash(&sponge, pp_hash.clone())?;

        // P.2. Construct u_i
        let u_i = CommittedInstanceVar {
            // u_i.cmE = cm(0)
            cmE: NonNativeAffineVar::new_constant(cs.clone(), C1::zero())?,
            // u_i.u = 1
            u: FpVar::one(),
            // u_i.cmW is provided by the prover as witness
            cmW: NonNativeAffineVar::new_witness(cs.clone(), || {
                Ok(self.u_i_cmW.unwrap_or(C1::zero()))
            })?,
            // u_i.x is computed in step 1
            x: vec![u_i_x, cf_u_i_x],
        };

        // P.3. nifs.verify, obtains U_{i+1} by folding u_i & U_i .

        // compute r = H(u_i, U_i, cmT)
        let r_bits = ChallengeGadget::<C1, CommittedInstance<C1>>::get_challenge_gadget(
            &mut transcript,
            pp_hash.clone(),
            U_i_vec,
            u_i.clone(),
            Some(cmT.clone()),
        )?;
        let r = Boolean::le_bits_to_fp_var(&r_bits)?;
        // Also convert r_bits to a `NonNativeFieldVar`
        let r_nonnat = {
            let mut bits = r_bits;
            bits.resize(C1::BaseField::MODULUS_BIT_SIZE as usize, Boolean::FALSE);
            NonNativeUintVar::from(&bits)
        };

        // Notice that NIFSGadget::fold_committed_instance does not fold cmE & cmW.
        // We set `U_i1.cmE` and `U_i1.cmW` to unconstrained witnesses `U_i1_cmE` and `U_i1_cmW`
        // respectively.
        // The correctness of them will be checked on the other curve.
        let mut U_i1 = NIFSGadget::<C1>::fold_committed_instance(r, U_i.clone(), u_i.clone())?;
        U_i1.cmE = U_i1_cmE;
        U_i1.cmW = U_i1_cmW;

        // P.4.a compute and check the first output of F'

        // get z_{i+1} from the F circuit
        let i_usize = self.i_usize.unwrap_or(0);
        let z_i1 = self
            .F
            .generate_step_constraints(cs.clone(), i_usize, z_i, external_inputs)?;

        // Base case: u_{i+1}.x[0] == H((i+1, z_0, z_{i+1}, U_{\bot})
        // Non-base case: u_{i+1}.x[0] == H((i+1, z_0, z_{i+1}, U_{i+1})
        let (u_i1_x, _) = U_i1.clone().hash(
            &sponge,
            &pp_hash,
            &(i + FpVar::<CF1<C1>>::one()),
            &z_0,
            &z_i1,
        )?;
        let (u_i1_x_base, _) = CommittedInstanceVar::new_constant(cs.clone(), u_dummy)?.hash(
            &sponge,
            &pp_hash,
            &FpVar::<CF1<C1>>::one(),
            &z_0,
            &z_i1,
        )?;
        let x = FpVar::new_input(cs.clone(), || Ok(self.x.unwrap_or(u_i1_x_base.value()?)))?;
        x.enforce_equal(&is_basecase.select(&u_i1_x_base, &u_i1_x)?)?;

        // CycleFold part
        // C.1. Compute cf1_u_i.x and cf2_u_i.x
        let cfW_x = vec![
            r_nonnat.clone(),
            U_i.cmW.x,
            U_i.cmW.y,
            u_i.cmW.x,
            u_i.cmW.y,
            U_i1.cmW.x,
            U_i1.cmW.y,
        ];
        let cfE_x = vec![
            r_nonnat, U_i.cmE.x, U_i.cmE.y, cmT.x, cmT.y, U_i1.cmE.x, U_i1.cmE.y,
        ];

        // ensure that cf1_u & cf2_u have as public inputs the cmW & cmE from main instances U_i,
        // u_i, U_i+1 coordinates of the commitments
        // C.2. Construct `cf1_u_i` and `cf2_u_i`
        let cf1_u_i = CycleFoldCommittedInstanceVar {
            // cf1_u_i.cmE = 0
            cmE: GC2::zero(),
            // cf1_u_i.u = 1
            u: NonNativeUintVar::new_constant(cs.clone(), C1::BaseField::one())?,
            // cf1_u_i.cmW is provided by the prover as witness
            cmW: GC2::new_witness(cs.clone(), || Ok(self.cf1_u_i_cmW.unwrap_or(C2::zero())))?,
            // cf1_u_i.x is computed in step 1
            x: cfW_x,
        };
        let cf2_u_i = CycleFoldCommittedInstanceVar {
            // cf2_u_i.cmE = 0
            cmE: GC2::zero(),
            // cf2_u_i.u = 1
            u: NonNativeUintVar::new_constant(cs.clone(), C1::BaseField::one())?,
            // cf2_u_i.cmW is provided by the prover as witness
            cmW: GC2::new_witness(cs.clone(), || Ok(self.cf2_u_i_cmW.unwrap_or(C2::zero())))?,
            // cf2_u_i.x is computed in step 1
            x: cfE_x,
        };

        // C.3. nifs.verify, obtains cf1_U_{i+1} by folding cf1_u_i & cf_U_i, and then cf_U_{i+1}
        // by folding cf2_u_i & cf1_U_{i+1}.

        // compute cf1_r = H(cf1_u_i, cf_U_i, cf1_cmT)
        // cf_r_bits is denoted by rho* in the paper.
        let cf1_r_bits = CycleFoldChallengeGadget::<C2, GC2>::get_challenge_gadget(
            &mut transcript,
            pp_hash.clone(),
            cf_U_i_vec,
            cf1_u_i.clone(),
            cf1_cmT.clone(),
        )?;
        // Fold cf1_u_i & cf_U_i into cf1_U_{i+1}
        let cf1_U_i1 = NIFSFullGadget::<C2, GC2>::fold_committed_instance(
            cf1_r_bits, cf1_cmT, cf_U_i, cf1_u_i,
        )?;

        // same for cf2_r:
        let cf2_r_bits = CycleFoldChallengeGadget::<C2, GC2>::get_challenge_gadget(
            &mut transcript,
            pp_hash.clone(),
            cf1_U_i1.to_native_sponge_field_elements()?,
            cf2_u_i.clone(),
            cf2_cmT.clone(),
        )?;
        let cf_U_i1 = NIFSFullGadget::<C2, GC2>::fold_committed_instance(
            cf2_r_bits, cf2_cmT, cf1_U_i1, // the output from NIFS.V(cf1_r, cf_U, cfE_u)
            cf2_u_i,
        )?;

        // Back to Primary Part
        // P.4.b compute and check the second output of F'
        // Base case: u_{i+1}.x[1] == H(cf_U_{\bot})
        // Non-base case: u_{i+1}.x[1] == H(cf_U_{i+1})
        let (cf_u_i1_x, _) = cf_U_i1.clone().hash(&sponge, pp_hash.clone())?;
        let (cf_u_i1_x_base, _) =
            CycleFoldCommittedInstanceVar::new_constant(cs.clone(), cf_u_dummy)?
                .hash(&sponge, pp_hash)?;
        let cf_x = FpVar::new_input(cs.clone(), || {
            Ok(self.cf_x.unwrap_or(cf_u_i1_x_base.value()?))
        })?;
        cf_x.enforce_equal(&is_basecase.select(&cf_u_i1_x_base, &cf_u_i1_x)?)?;

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_bn254::{Fr, G1Projective as Projective};
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use ark_ff::BigInteger;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::nifs::NIFS;
    use crate::folding::nova::traits::NIFSTrait;
    use crate::folding::traits::CommittedInstanceOps;
    use crate::transcript::poseidon::poseidon_canonical_config;

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
        // the values cmE and cmW are checked in the CycleFold's circuit
        // CommittedInstanceInCycleFoldVar in
        // cyclefold::tests::test_committed_instance_cyclefold_var
    }

    #[test]
    fn test_nifs_gadget() {
        let mut rng = ark_std::test_rng();

        // prepare the committed instances to test in-circuit
        let ci: Vec<CommittedInstance<Projective>> = (0..2)
            .into_iter()
            .map(|_| CommittedInstance::<Projective> {
                cmE: Projective::rand(&mut rng),
                u: Fr::rand(&mut rng),
                cmW: Projective::rand(&mut rng),
                x: vec![Fr::rand(&mut rng); 1],
            })
            .collect();
        let (ci1, ci2) = (ci[0].clone(), ci[1].clone());
        let r_Fr = Fr::rand(&mut rng);
        let cmT = Projective::rand(&mut rng);
        let ci3 = NIFS::<Projective, Pedersen<Projective>>::verify(r_Fr, &ci1, &ci2, &cmT);

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
    }

    /// test that checks the native CommittedInstance.to_sponge_{bytes,field_elements}
    /// vs the R1CS constraints version
    #[test]
    pub fn test_committed_instance_to_sponge_preimage() {
        let mut rng = ark_std::test_rng();

        let ci = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };

        let bytes = ci.to_sponge_bytes_as_vec();
        let field_elements = ci.to_sponge_field_elements_as_vec();

        let cs = ConstraintSystem::<Fr>::new_ref();

        let ciVar =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(ci.clone())).unwrap();
        let bytes_var = ciVar.to_sponge_bytes().unwrap();
        let field_elements_var = ciVar.to_sponge_field_elements().unwrap();

        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        assert_eq!(bytes_var.value().unwrap(), bytes);
        assert_eq!(field_elements_var.value().unwrap(), field_elements);
    }

    #[test]
    fn test_committed_instance_hash() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let sponge = PoseidonSponge::<Fr>::new(&poseidon_config);
        let pp_hash = Fr::from(42u32); // only for test

        let i = Fr::from(3_u32);
        let z_0 = vec![Fr::from(3_u32)];
        let z_i = vec![Fr::from(3_u32)];
        let ci = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };

        // compute the CommittedInstance hash natively
        let h = ci.hash(&sponge, pp_hash, i, &z_0, &z_i);

        let cs = ConstraintSystem::<Fr>::new_ref();

        let pp_hashVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(pp_hash)).unwrap();
        let iVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(i)).unwrap();
        let z_0Var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_0.clone())).unwrap();
        let z_iVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i.clone())).unwrap();
        let ciVar =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(ci.clone())).unwrap();

        let sponge = PoseidonSpongeVar::<Fr>::new(cs.clone(), &poseidon_config);

        // compute the CommittedInstance hash in-circuit
        let (hVar, _) = ciVar
            .hash(&sponge, &pp_hashVar, &iVar, &z_0Var, &z_iVar)
            .unwrap();
        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        assert_eq!(hVar.value().unwrap(), h);
    }

    // checks that the gadget and native implementations of the challenge computation match
    #[test]
    fn test_challenge_gadget() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript = PoseidonSponge::<Fr>::new(&poseidon_config);

        let u_i = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };
        let U_i = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };
        let cmT = Projective::rand(&mut rng);

        let pp_hash = Fr::from(42u32); // only for testing

        // compute the challenge natively
        let r_bits =
            ChallengeGadget::<Projective, CommittedInstance<Projective>>::get_challenge_native(
                &mut transcript,
                pp_hash,
                &U_i,
                &u_i,
                Some(&cmT),
            );
        let r = Fr::from_bigint(BigInteger::from_bits_le(&r_bits)).unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let pp_hashVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(pp_hash)).unwrap();
        let u_iVar =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(u_i.clone()))
                .unwrap();
        let U_iVar =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(U_i.clone()))
                .unwrap();
        let cmTVar = NonNativeAffineVar::<Projective>::new_witness(cs.clone(), || Ok(cmT)).unwrap();
        let mut transcriptVar = PoseidonSpongeVar::<Fr>::new(cs.clone(), &poseidon_config);

        // compute the challenge in-circuit
        let U_iVar_vec = [
            vec![U_iVar.u.clone()],
            U_iVar.x.clone(),
            U_iVar.cmE.to_constraint_field().unwrap(),
            U_iVar.cmW.to_constraint_field().unwrap(),
        ]
        .concat();
        let r_bitsVar =
            ChallengeGadget::<Projective, CommittedInstance<Projective>>::get_challenge_gadget(
                &mut transcriptVar,
                pp_hashVar,
                U_iVar_vec,
                u_iVar,
                Some(cmTVar),
            )
            .unwrap();
        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        let rVar = Boolean::le_bits_to_fp_var(&r_bitsVar).unwrap();
        assert_eq!(rVar.value().unwrap(), r);
        assert_eq!(r_bitsVar.value().unwrap(), r_bits);
    }
}
