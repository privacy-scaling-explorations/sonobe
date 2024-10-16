/// Contains [CycleFold](https://eprint.iacr.org/2023/1192.pdf) related circuits and functions that
/// are shared across the different folding schemes
use ark_crypto_primitives::sponge::{Absorb, CryptographicSponge};
use ark_ec::{AffineRepr, CurveGroup, Group};
use ark_ff::{BigInteger, Field, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::fp::FpVar,
    groups::GroupOpsBounds,
    prelude::CurveVar,
    ToConstraintFieldGadget,
};
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, Namespace, SynthesisError,
};
use ark_std::fmt::Debug;
use ark_std::rand::RngCore;
use ark_std::Zero;
use core::{borrow::Borrow, marker::PhantomData};

use super::{nonnative::uint::NonNativeUintVar, CF1, CF2};
use crate::arith::r1cs::{extract_w_x, R1CS};
use crate::commitment::CommitmentScheme;
use crate::constants::NOVA_N_BITS_RO;
use crate::folding::nova::{nifs::NIFS, traits::NIFSTrait};
use crate::transcript::{AbsorbNonNative, AbsorbNonNativeGadget, Transcript, TranscriptVar};
use crate::Error;

/// Re-export the Nova committed instance as `CycleFoldCommittedInstance` and
/// witness as `CycleFoldWitness`, for clarity and consistency
pub use crate::folding::nova::{
    CommittedInstance as CycleFoldCommittedInstance, Witness as CycleFoldWitness,
};

/// CycleFoldCommittedInstanceVar is the CycleFold CommittedInstance represented
/// in folding verifier circuit
#[derive(Debug, Clone)]
pub struct CycleFoldCommittedInstanceVar<C: CurveGroup, GC: CurveVar<C, CF2<C>>>
where
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    pub cmE: GC,
    pub u: NonNativeUintVar<CF2<C>>,
    pub cmW: GC,
    pub x: Vec<NonNativeUintVar<CF2<C>>>,
}
impl<C, GC> AllocVar<CycleFoldCommittedInstance<C>, CF2<C>> for CycleFoldCommittedInstanceVar<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>>,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    fn new_variable<T: Borrow<CycleFoldCommittedInstance<C>>>(
        cs: impl Into<Namespace<CF2<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let u =
                NonNativeUintVar::<CF2<C>>::new_variable(cs.clone(), || Ok(val.borrow().u), mode)?;
            let x: Vec<NonNativeUintVar<CF2<C>>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().x.clone()), mode)?;
            let cmE = GC::new_variable(cs.clone(), || Ok(val.borrow().cmE), mode)?;
            let cmW = GC::new_variable(cs.clone(), || Ok(val.borrow().cmW), mode)?;

            Ok(Self { cmE, u, cmW, x })
        })
    }
}

impl<C: CurveGroup> AbsorbNonNative<C::BaseField> for CycleFoldCommittedInstance<C>
where
    C::BaseField: PrimeField + Absorb,
{
    // Compatible with the in-circuit `CycleFoldCommittedInstanceVar::to_native_sponge_field_elements`
    fn to_native_sponge_field_elements(&self, dest: &mut Vec<C::BaseField>) {
        [self.u].to_native_sponge_field_elements(dest);
        self.x.to_native_sponge_field_elements(dest);
        let (cmE_x, cmE_y) = match self.cmE.into_affine().xy() {
            Some((&x, &y)) => (x, y),
            None => (C::BaseField::zero(), C::BaseField::zero()),
        };
        let (cmW_x, cmW_y) = match self.cmW.into_affine().xy() {
            Some((&x, &y)) => (x, y),
            None => (C::BaseField::zero(), C::BaseField::zero()),
        };
        cmE_x.to_sponge_field_elements(dest);
        cmE_y.to_sponge_field_elements(dest);
        cmW_x.to_sponge_field_elements(dest);
        cmW_y.to_sponge_field_elements(dest);
    }
}

impl<C, GC> AbsorbNonNativeGadget<C::BaseField> for CycleFoldCommittedInstanceVar<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>> + ToConstraintFieldGadget<CF2<C>>,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField + Absorb,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    /// Extracts the underlying field elements from `CycleFoldCommittedInstanceVar`, in the order
    /// of `u`, `x`, `cmE.x`, `cmE.y`, `cmW.x`, `cmW.y`, `cmE.is_inf || cmW.is_inf` (|| is for
    /// concat).
    fn to_native_sponge_field_elements(&self) -> Result<Vec<FpVar<CF2<C>>>, SynthesisError> {
        let mut cmE_elems = self.cmE.to_constraint_field()?;
        let mut cmW_elems = self.cmW.to_constraint_field()?;

        // See `transcript/poseidon.rs: TranscriptVar::absorb_point` for details
        // why the last element is unnecessary.
        cmE_elems.pop();
        cmW_elems.pop();

        Ok([
            self.u.to_native_sponge_field_elements()?,
            self.x
                .iter()
                .map(|i| i.to_native_sponge_field_elements())
                .collect::<Result<Vec<_>, _>>()?
                .concat(),
            cmE_elems,
            cmW_elems,
        ]
        .concat())
    }
}

impl<C: CurveGroup> CycleFoldCommittedInstance<C>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField + Absorb,
{
    /// hash_cyclefold implements the committed instance hash compatible with the
    /// in-circuit implementation `CycleFoldCommittedInstanceVar::hash`.
    /// Returns `H(U_i)`, where `U_i` is a `CycleFoldCommittedInstance`.
    pub fn hash_cyclefold<T: Transcript<C::BaseField>>(
        &self,
        sponge: &T,
        pp_hash: C::BaseField, // public params hash
    ) -> C::BaseField {
        let mut sponge = sponge.clone();
        sponge.absorb(&pp_hash);
        sponge.absorb_nonnative(self);
        sponge.squeeze_field_elements(1)[0]
    }
}

impl<C, GC> CycleFoldCommittedInstanceVar<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>> + ToConstraintFieldGadget<CF2<C>>,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField + Absorb,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    /// hash implements the committed instance hash compatible with the native
    /// implementation `CycleFoldCommittedInstance::hash_cyclefold`.
    /// Returns `H(U_i)`, where `U` is a `CycleFoldCommittedInstanceVar`.
    ///
    /// Additionally it returns the vector of the field elements from the self
    /// parameters, so they can be reused in other gadgets without recalculating
    /// (reconstraining) them.
    #[allow(clippy::type_complexity)]
    pub fn hash<S: CryptographicSponge, T: TranscriptVar<CF2<C>, S>>(
        self,
        sponge: &T,
        pp_hash: FpVar<CF2<C>>, // public params hash
    ) -> Result<(FpVar<CF2<C>>, Vec<FpVar<CF2<C>>>), SynthesisError> {
        let mut sponge = sponge.clone();
        let U_vec = self.to_native_sponge_field_elements()?;
        sponge.absorb(&pp_hash)?;
        sponge.absorb(&U_vec)?;
        Ok((sponge.squeeze_field_elements(1)?.pop().unwrap(), U_vec))
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

impl<C, GC> AllocVar<CycleFoldCommittedInstance<C>, CF2<C>>
    for CommittedInstanceInCycleFoldVar<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>>,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    fn new_variable<T: Borrow<CycleFoldCommittedInstance<C>>>(
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

/// In-circuit representation of the Witness associated to the CommittedInstance, but with
/// non-native representation, since it is used to represent the CycleFold witness. This struct is
/// used in the Decider circuit.
#[derive(Debug, Clone)]
pub struct CycleFoldWitnessVar<C: CurveGroup> {
    pub E: Vec<NonNativeUintVar<CF2<C>>>,
    pub rE: NonNativeUintVar<CF2<C>>,
    pub W: Vec<NonNativeUintVar<CF2<C>>>,
    pub rW: NonNativeUintVar<CF2<C>>,
}

impl<C> AllocVar<CycleFoldWitness<C>, CF2<C>> for CycleFoldWitnessVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<CycleFoldWitness<C>>>(
        cs: impl Into<Namespace<CF2<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let E = Vec::new_variable(cs.clone(), || Ok(val.borrow().E.clone()), mode)?;
            let rE = NonNativeUintVar::new_variable(cs.clone(), || Ok(val.borrow().rE), mode)?;

            let W = Vec::new_variable(cs.clone(), || Ok(val.borrow().W.clone()), mode)?;
            let rW = NonNativeUintVar::new_variable(cs.clone(), || Ok(val.borrow().rW), mode)?;

            Ok(Self { E, rE, W, rW })
        })
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
    pub fn fold_committed_instance(
        r_bits: Vec<Boolean<CF2<C>>>,
        cmT: GC,
        ci1: CycleFoldCommittedInstanceVar<C, GC>,
        // ci2 is assumed to be always with cmE=0, u=1 (checks done previous to this method)
        ci2: CycleFoldCommittedInstanceVar<C, GC>,
    ) -> Result<CycleFoldCommittedInstanceVar<C, GC>, SynthesisError> {
        // r_nonnat is equal to r_bits just that in a different format
        let r_nonnat = {
            let mut bits = r_bits.clone();
            bits.resize(CF1::<C>::MODULUS_BIT_SIZE as usize, Boolean::FALSE);
            NonNativeUintVar::from(&bits)
        };
        Ok(CycleFoldCommittedInstanceVar {
            cmE: cmT.scalar_mul_le(r_bits.iter())? + ci1.cmE,
            cmW: ci1.cmW + ci2.cmW.scalar_mul_le(r_bits.iter())?,
            u: ci1.u.add_no_align(&r_nonnat).modulo::<CF1<C>>()?,
            x: ci1
                .x
                .iter()
                .zip(ci2.x)
                .map(|(a, b)| {
                    a.add_no_align(&r_nonnat.mul_no_align(&b)?)
                        .modulo::<CF1<C>>()
                })
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    pub fn verify(
        // assumes that r_bits is equal to r_nonnat just that in a different format
        r_bits: Vec<Boolean<CF2<C>>>,
        cmT: GC,
        ci1: CycleFoldCommittedInstanceVar<C, GC>,
        // ci2 is assumed to be always with cmE=0, u=1 (checks done previous to this method)
        ci2: CycleFoldCommittedInstanceVar<C, GC>,
        ci3: CycleFoldCommittedInstanceVar<C, GC>,
    ) -> Result<(), SynthesisError> {
        let ci = Self::fold_committed_instance(r_bits, cmT, ci1, ci2)?;

        ci.cmE.enforce_equal(&ci3.cmE)?;
        ci.u.enforce_equal_unaligned(&ci3.u)?;
        ci.cmW.enforce_equal(&ci3.cmW)?;
        for (x, y) in ci.x.iter().zip(ci3.x.iter()) {
            x.enforce_equal_unaligned(y)?;
        }

        Ok(())
    }
}

/// CycleFoldChallengeGadget computes the RO challenge used for the CycleFold instances NIFS, it contains a
/// rust-native and a in-circuit compatible versions.
pub struct CycleFoldChallengeGadget<C: CurveGroup, GC: CurveVar<C, CF2<C>>> {
    _c: PhantomData<C>, // Nova's Curve2, the one used for the CycleFold circuit
    _gc: PhantomData<GC>,
}
impl<C, GC> CycleFoldChallengeGadget<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>> + ToConstraintFieldGadget<CF2<C>>,
    <C as CurveGroup>::BaseField: PrimeField,
    <C as CurveGroup>::BaseField: Absorb,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    pub fn get_challenge_native<T: Transcript<C::BaseField>>(
        transcript: &mut T,
        pp_hash: C::BaseField, // public params hash
        U_i: CycleFoldCommittedInstance<C>,
        u_i: CycleFoldCommittedInstance<C>,
        cmT: C,
    ) -> Vec<bool> {
        transcript.absorb(&pp_hash);
        transcript.absorb_nonnative(&U_i);
        transcript.absorb_nonnative(&u_i);
        transcript.absorb_point(&cmT);
        transcript.squeeze_bits(NOVA_N_BITS_RO)
    }

    // compatible with the native get_challenge_native
    pub fn get_challenge_gadget<S: CryptographicSponge, T: TranscriptVar<C::BaseField, S>>(
        transcript: &mut T,
        pp_hash: FpVar<C::BaseField>, // public params hash
        U_i_vec: Vec<FpVar<C::BaseField>>,
        u_i: CycleFoldCommittedInstanceVar<C, GC>,
        cmT: GC,
    ) -> Result<Vec<Boolean<C::BaseField>>, SynthesisError> {
        transcript.absorb(&pp_hash)?;
        transcript.absorb(&U_i_vec)?;
        transcript.absorb_nonnative(&u_i)?;
        transcript.absorb_point(&cmT)?;
        transcript.squeeze_bits(NOVA_N_BITS_RO)
    }
}

/// `CycleFoldConfig` allows us to customize the behavior of CycleFold circuit
/// according to the folding scheme we are working with.
pub trait CycleFoldConfig {
    /// `N_INPUT_POINTS` specifies the number of input points that are folded in
    /// [`CycleFoldCircuit`] via random linear combinations.
    const N_INPUT_POINTS: usize;
    /// `RANDOMNESS_BIT_LENGTH` is the (maximum) bit length of randomness `r`.
    const RANDOMNESS_BIT_LENGTH: usize;
    /// `FIELD_CAPACITY` is the maximum number of bits that can be stored in a
    /// field element.
    ///
    /// E.g., given a randomness `r` with `RANDOMNESS_BIT_LENGTH` bits, we need
    /// `RANDOMNESS_BIT_LENGTH / FIELD_CAPACITY` field elements to represent `r`
    /// compactly in-circuit.
    const FIELD_CAPACITY: usize = CF2::<Self::C>::MODULUS_BIT_SIZE as usize - 1;

    /// Public inputs length for the CycleFoldCircuit.
    /// * For Nova this is: `|[r, p1.x,y, p2.x,y, p3.x,y]|`
    /// * In general, `|[r, (p_i.x,y)*n_points, p_folded.x,y]|`.
    ///
    /// Thus, `IO_LEN` is:
    /// `RANDOMNESS_BIT_LENGTH / FIELD_CAPACITY  + 2 * N_INPUT_POINTS + 2`
    const IO_LEN: usize = {
        Self::RANDOMNESS_BIT_LENGTH.div_ceil(Self::FIELD_CAPACITY) + 2 * Self::N_INPUT_POINTS + 2
    };

    type F: Field;
    type C: CurveGroup<BaseField = Self::F>;
}

/// CycleFoldCircuit contains the constraints that check the correct fold of the committed
/// instances from Curve1. Namely, it checks the random linear combinations of the elliptic curve
/// (Curve1) points of u_i, U_i leading to U_{i+1}
#[derive(Debug, Clone)]
pub struct CycleFoldCircuit<CFG: CycleFoldConfig, GC: CurveVar<CFG::C, CFG::F>> {
    pub _gc: PhantomData<GC>,
    /// r_bits is the bit representation of the r whose powers are used in the
    /// random-linear-combination inside the CycleFoldCircuit
    pub r_bits: Option<Vec<bool>>,
    /// points to be folded in the CycleFoldCircuit
    pub points: Option<Vec<CFG::C>>,
    /// public inputs (cf_u_{i+1}.x)
    pub x: Option<Vec<CFG::F>>,
}

impl<CFG: CycleFoldConfig, GC: CurveVar<CFG::C, CFG::F>> CycleFoldCircuit<CFG, GC> {
    /// n_points indicates the number of points being folded in the CycleFoldCircuit
    pub fn empty() -> Self {
        Self {
            _gc: PhantomData,
            r_bits: None,
            points: None,
            x: None,
        }
    }
}

impl<CFG: CycleFoldConfig, GC: CurveVar<CFG::C, CFG::F>> ConstraintSynthesizer<CFG::F>
    for CycleFoldCircuit<CFG, GC>
where
    GC: ToConstraintFieldGadget<CFG::F>,
    CFG::F: PrimeField,
    for<'a> &'a GC: GroupOpsBounds<'a, CFG::C, GC>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CFG::F>) -> Result<(), SynthesisError> {
        let r_bits = Vec::<Boolean<CFG::F>>::new_witness(cs.clone(), || {
            Ok(self
                .r_bits
                .unwrap_or(vec![false; CFG::RANDOMNESS_BIT_LENGTH]))
        })?;
        let points = Vec::<GC>::new_witness(cs.clone(), || {
            Ok(self
                .points
                .unwrap_or(vec![CFG::C::zero(); CFG::N_INPUT_POINTS]))
        })?;

        #[cfg(test)]
        {
            assert_eq!(CFG::N_INPUT_POINTS, points.len());
            assert_eq!(CFG::RANDOMNESS_BIT_LENGTH, r_bits.len());
        }

        // Fold the original points of the instances natively in CycleFold.
        // In Nova,
        // - for the cmW we're computing: U_i1.cmW = U_i.cmW + r * u_i.cmW
        // - for the cmE we're computing: U_i1.cmE = U_i.cmE + r * cmT + r^2 * u_i.cmE, where u_i.cmE
        // is assumed to be 0, so, U_i1.cmE = U_i.cmE + r * cmT
        // We want to compute
        // P_folded = p_0 + r * P_1 + r^2 * P_2 + r^3 * P_3 + ... + r^{n-2} * P_{n-2} + r^{n-1} * P_{n-1}
        // so in order to do it more efficiently (less constraints) we do
        // P_folded = (((P_{n-1} * r + P_{n-2}) * r + P_{n-3})... ) * r + P_0
        let mut p_folded: GC = points[CFG::N_INPUT_POINTS - 1].clone();
        for i in (0..CFG::N_INPUT_POINTS - 1).rev() {
            p_folded = p_folded.scalar_mul_le(r_bits.iter())? + points[i].clone();
        }

        let x = Vec::<FpVar<CFG::F>>::new_input(cs.clone(), || {
            Ok(self.x.unwrap_or(vec![CFG::F::zero(); CFG::IO_LEN]))
        })?;
        #[cfg(test)]
        assert_eq!(x.len(), CFG::IO_LEN); // non-constrained sanity check

        // Check that the points coordinates are placed as the public input x:
        // In Nova, this is: x == [r, p1, p2, p3] (wheere p3 is the p_folded).
        // In multifolding schemes such as HyperNova, this is:
        // computed_x = [r, p_0, p_1, p_2, ..., p_n, p_folded],
        // where each p_i is in fact p_i.to_constraint_field()
        let r_fp = r_bits
            .chunks(CFG::F::MODULUS_BIT_SIZE as usize - 1)
            .map(Boolean::le_bits_to_fp_var)
            .collect::<Result<Vec<_>, _>>()?;
        let points_aux: Vec<FpVar<CFG::F>> = points
            .iter()
            .map(|p_i| Ok(p_i.to_constraint_field()?[..2].to_vec()))
            .collect::<Result<Vec<_>, SynthesisError>>()?
            .into_iter()
            .flatten()
            .collect();

        let computed_x: Vec<FpVar<CFG::F>> = [
            r_fp,
            points_aux,
            p_folded.to_constraint_field()?[..2].to_vec(),
        ]
        .concat();
        computed_x.enforce_equal(&x)?;

        Ok(())
    }
}

/// Folds the given cyclefold circuit and its instances. This method is abstracted from any folding
/// scheme struct because it is used both by Nova & HyperNova's CycleFold.
#[allow(clippy::type_complexity)]
#[allow(clippy::too_many_arguments)]
pub fn fold_cyclefold_circuit<CFG, C1, GC1, C2, GC2, CS2, const H: bool>(
    transcript: &mut impl Transcript<C1::ScalarField>,
    cf_r1cs: R1CS<C2::ScalarField>,
    cf_cs_params: CS2::ProverParams,
    pp_hash: C1::ScalarField,               // public params hash
    cf_W_i: CycleFoldWitness<C2>,           // witness of the running instance
    cf_U_i: CycleFoldCommittedInstance<C2>, // running instance
    cf_u_i_x: Vec<C2::ScalarField>,
    cf_circuit: CycleFoldCircuit<CFG, GC1>,
    mut rng: impl RngCore,
) -> Result<
    (
        CycleFoldWitness<C2>,
        CycleFoldCommittedInstance<C2>, // u_i
        CycleFoldWitness<C2>,           // W_i1
        CycleFoldCommittedInstance<C2>, // U_i1
        C2,                             // cmT
        C2::ScalarField,                // r_Fq
    ),
    Error,
>
where
    CFG: CycleFoldConfig<C = C1, F = CF2<C1>>,
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    CS2: CommitmentScheme<C2, H>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();
    cf_circuit.generate_constraints(cs2.clone())?;

    let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
    let (cf_w_i, cf_x_i) = extract_w_x::<C1::BaseField>(&cs2);
    if cf_x_i != cf_u_i_x {
        return Err(Error::NotEqual);
    }

    #[cfg(test)]
    assert_eq!(cf_x_i.len(), CFG::IO_LEN);

    // fold cyclefold instances
    let cf_w_i = CycleFoldWitness::<C2>::new::<H>(cf_w_i.clone(), cf_r1cs.A.n_rows, &mut rng);
    let cf_u_i: CycleFoldCommittedInstance<C2> =
        cf_w_i.commit::<CS2, H>(&cf_cs_params, cf_x_i.clone())?;

    // compute T* and cmT* for CycleFoldCircuit
    let (cf_T, cf_cmT) = NIFS::<C2, CS2, H>::compute_cyclefold_cmT(
        &cf_cs_params,
        &cf_r1cs,
        &cf_w_i,
        &cf_u_i,
        &cf_W_i,
        &cf_U_i,
    )?;

    let cf_r_bits = CycleFoldChallengeGadget::<C2, GC2>::get_challenge_native(
        transcript,
        pp_hash,
        cf_U_i.clone(),
        cf_u_i.clone(),
        cf_cmT,
    );
    let cf_r_Fq = C1::BaseField::from_bigint(BigInteger::from_bits_le(&cf_r_bits))
        .expect("cf_r_bits out of bounds");

    let (cf_W_i1, cf_U_i1) =
        NIFS::<C2, CS2, H>::prove(cf_r_Fq, &cf_W_i, &cf_U_i, &cf_w_i, &cf_u_i, &cf_T, &cf_cmT)?;
    Ok((cf_w_i, cf_u_i, cf_W_i1, cf_U_i1, cf_cmT, cf_r_Fq))
}

#[cfg(test)]
pub mod tests {
    use ark_bn254::{constraints::GVar, Fq, Fr, G1Projective as Projective};
    use ark_crypto_primitives::sponge::{
        constraints::CryptographicSpongeVar,
        poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge},
    };
    use ark_r1cs_std::R1CSVar;
    use ark_std::{One, UniformRand};

    use super::*;
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::CommittedInstance;
    use crate::transcript::poseidon::poseidon_canonical_config;
    use crate::utils::get_cm_coordinates;

    struct TestCycleFoldConfig<C: CurveGroup, const N: usize> {
        _c: PhantomData<C>,
    }

    impl<C: CurveGroup, const N: usize> CycleFoldConfig for TestCycleFoldConfig<C, N> {
        const RANDOMNESS_BIT_LENGTH: usize = NOVA_N_BITS_RO;
        const N_INPUT_POINTS: usize = N;
        type C = C;
        type F = C::BaseField;
    }

    #[test]
    fn test_committed_instance_cyclefold_var() {
        let mut rng = ark_std::test_rng();

        let ci = CycleFoldCommittedInstance::<Projective> {
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
    fn test_CycleFoldCircuit_n_points_constraints() {
        const n: usize = 16;
        let mut rng = ark_std::test_rng();

        // points to random-linear-combine
        let points: Vec<Projective> = std::iter::repeat_with(|| Projective::rand(&mut rng))
            .take(n)
            .collect();

        use std::ops::Mul;
        let rho_raw = Fq::rand(&mut rng);
        let rho_bits = rho_raw.into_bigint().to_bits_le()[..NOVA_N_BITS_RO].to_vec();
        let rho_Fq = Fq::from_bigint(BigInteger::from_bits_le(&rho_bits)).unwrap();
        let rho_Fr = Fr::from_bigint(BigInteger::from_bits_le(&rho_bits)).unwrap();
        let mut res = Projective::zero();
        use ark_std::One;
        let mut rho_i = Fr::one();
        for point_i in points.iter() {
            res += point_i.mul(rho_i);
            rho_i *= rho_Fr;
        }

        // cs is the Constraint System on the Curve Cycle auxiliary curve constraints field
        // (E1::Fq=E2::Fr)
        let cs = ConstraintSystem::<Fq>::new_ref();

        let x: Vec<Fq> = [
            vec![rho_Fq],
            points.iter().flat_map(get_cm_coordinates).collect(),
            get_cm_coordinates(&res),
        ]
        .concat();
        let cf_circuit = CycleFoldCircuit::<TestCycleFoldConfig<Projective, n>, GVar> {
            _gc: PhantomData,
            r_bits: Some(rho_bits),
            points: Some(points),
            x: Some(x.clone()),
        };
        cf_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_nifs_full_gadget() {
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
        let (ci1, mut ci2) = (ci[0].clone(), ci[1].clone());
        // make the 2nd instance a 'fresh' instance (ie. cmE=0, u=1)
        ci2.cmE = Projective::zero();
        ci2.u = Fr::one();
        let r_bits: Vec<bool> =
            Fr::rand(&mut rng).into_bigint().to_bits_le()[..NOVA_N_BITS_RO].to_vec();
        let r_Fr = Fr::from_bigint(BigInteger::from_bits_le(&r_bits)).unwrap();
        let cmT = Projective::rand(&mut rng);
        let ci3 = NIFS::<Projective, Pedersen<Projective>>::verify(r_Fr, &ci1, &ci2, &cmT);

        let cs = ConstraintSystem::<Fq>::new_ref();
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

        NIFSFullGadget::<Projective, GVar>::verify(r_bitsVar, cmTVar, ci1Var, ci2Var, ci3Var)
            .unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_cyclefold_challenge_gadget() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fq>();
        let mut transcript = PoseidonSponge::<Fq>::new(&poseidon_config);

        let u_i = CycleFoldCommittedInstance::<Projective> {
            cmE: Projective::zero(), // zero on purpose, so we test also the zero point case
            u: Fr::zero(),
            cmW: Projective::rand(&mut rng),
            x: std::iter::repeat_with(|| Fr::rand(&mut rng))
                .take(TestCycleFoldConfig::<Projective, 2>::IO_LEN)
                .collect(),
        };
        let U_i = CycleFoldCommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: std::iter::repeat_with(|| Fr::rand(&mut rng))
                .take(TestCycleFoldConfig::<Projective, 2>::IO_LEN)
                .collect(),
        };
        let cmT = Projective::rand(&mut rng);

        // compute the challenge natively
        let pp_hash = Fq::from(42u32); // only for test
        let r_bits = CycleFoldChallengeGadget::<Projective, GVar>::get_challenge_native(
            &mut transcript,
            pp_hash,
            U_i.clone(),
            u_i.clone(),
            cmT,
        );

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
        let mut transcript_var =
            PoseidonSpongeVar::<Fq>::new(ConstraintSystem::<Fq>::new_ref(), &poseidon_config);

        let pp_hashVar = FpVar::<Fq>::new_witness(cs.clone(), || Ok(pp_hash)).unwrap();
        let r_bitsVar = CycleFoldChallengeGadget::<Projective, GVar>::get_challenge_gadget(
            &mut transcript_var,
            pp_hashVar,
            U_iVar.to_native_sponge_field_elements().unwrap(),
            u_iVar,
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

    #[test]
    fn test_cyclefold_hash_gadget() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fq>();
        let sponge = PoseidonSponge::<Fq>::new(&poseidon_config);

        let U_i = CycleFoldCommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: std::iter::repeat_with(|| Fr::rand(&mut rng))
                .take(TestCycleFoldConfig::<Projective, 2>::IO_LEN)
                .collect(),
        };
        let pp_hash = Fq::from(42u32); // only for test
        let h = U_i.hash_cyclefold(&sponge, pp_hash);

        let cs = ConstraintSystem::<Fq>::new_ref();
        let U_iVar =
            CycleFoldCommittedInstanceVar::<Projective, GVar>::new_witness(cs.clone(), || {
                Ok(U_i.clone())
            })
            .unwrap();
        let pp_hashVar = FpVar::<Fq>::new_witness(cs.clone(), || Ok(pp_hash)).unwrap();
        let (hVar, _) = U_iVar
            .hash(
                &PoseidonSpongeVar::new(cs.clone(), &poseidon_config),
                pp_hashVar,
            )
            .unwrap();
        hVar.enforce_equal(&FpVar::new_witness(cs.clone(), || Ok(h)).unwrap())
            .unwrap();
        assert!(cs.is_satisfied().unwrap());
    }
}
