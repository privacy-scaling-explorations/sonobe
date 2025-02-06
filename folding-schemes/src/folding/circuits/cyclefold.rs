/// Contains [CycleFold](https://eprint.iacr.org/2023/1192.pdf) related circuits and functions that
/// are shared across the different folding schemes
use ark_crypto_primitives::sponge::{poseidon::PoseidonSponge, Absorb, CryptographicSponge};
use ark_ec::AffineRepr;
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    convert::ToConstraintFieldGadget,
    eq::EqGadget,
    fields::fp::FpVar,
    prelude::CurveVar,
    R1CSVar,
};
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, Namespace, SynthesisError,
};
use ark_std::fmt::Debug;
use ark_std::rand::RngCore;
use ark_std::Zero;
use core::{borrow::Borrow, marker::PhantomData};

use super::{nonnative::uint::NonNativeUintVar, CF1, CF2};
use crate::arith::{
    r1cs::{circuits::R1CSMatricesVar, extract_w_x, R1CS},
    Arith, ArithRelationGadget,
};
use crate::commitment::CommitmentScheme;
use crate::constants::NOVA_N_BITS_RO;
use crate::folding::{
    nova::nifs::{nova::NIFS, NIFSTrait},
    traits::InputizeNonNative,
};
use crate::transcript::{AbsorbNonNative, AbsorbNonNativeGadget, Transcript, TranscriptVar};
use crate::utils::gadgets::{EquivalenceGadget, VectorGadget};
use crate::{Curve, Error};

/// Re-export the Nova committed instance as `CycleFoldCommittedInstance` and
/// witness as `CycleFoldWitness`, for clarity and consistency
pub use crate::folding::nova::{
    CommittedInstance as CycleFoldCommittedInstance, Witness as CycleFoldWitness,
};

impl<C: Curve> InputizeNonNative<CF2<C>> for CycleFoldCommittedInstance<C> {
    /// Returns the internal representation in the same order as how the value
    /// is allocated in `CycleFoldCommittedInstanceVar::new_input`.
    fn inputize_nonnative(&self) -> Vec<CF2<C>> {
        [
            self.u.inputize_nonnative(),
            self.x.inputize_nonnative(),
            self.cmE.inputize(),
            self.cmW.inputize(),
        ]
        .concat()
    }
}

/// CycleFoldCommittedInstanceVar is the CycleFold CommittedInstance represented
/// in folding verifier circuit
#[derive(Debug, Clone)]
pub struct CycleFoldCommittedInstanceVar<C: Curve> {
    pub cmE: C::Var,
    pub u: NonNativeUintVar<CF2<C>>,
    pub cmW: C::Var,
    pub x: Vec<NonNativeUintVar<CF2<C>>>,
}
impl<C: Curve> AllocVar<CycleFoldCommittedInstance<C>, CF2<C>>
    for CycleFoldCommittedInstanceVar<C>
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
            let cmE = C::Var::new_variable(cs.clone(), || Ok(val.borrow().cmE), mode)?;
            let cmW = C::Var::new_variable(cs.clone(), || Ok(val.borrow().cmW), mode)?;

            Ok(Self { cmE, u, cmW, x })
        })
    }
}

impl<C: Curve> AbsorbNonNative for CycleFoldCommittedInstance<C> {
    // Compatible with the in-circuit `CycleFoldCommittedInstanceVar::to_native_sponge_field_elements`
    fn to_native_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        self.u.to_native_sponge_field_elements(dest);
        self.x.to_native_sponge_field_elements(dest);
        let (cmE_x, cmE_y) = self.cmE.into_affine().xy().unwrap_or_default();
        let (cmW_x, cmW_y) = self.cmW.into_affine().xy().unwrap_or_default();
        cmE_x.to_sponge_field_elements(dest);
        cmE_y.to_sponge_field_elements(dest);
        cmW_x.to_sponge_field_elements(dest);
        cmW_y.to_sponge_field_elements(dest);
    }
}

impl<C: Curve> AbsorbNonNativeGadget<C::BaseField> for CycleFoldCommittedInstanceVar<C> {
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

impl<C: Curve> CycleFoldCommittedInstance<C> {
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

impl<C: Curve> CycleFoldCommittedInstanceVar<C> {
    /// hash implements the committed instance hash compatible with the native
    /// implementation `CycleFoldCommittedInstance::hash_cyclefold`.
    /// Returns `H(U_i)`, where `U` is a `CycleFoldCommittedInstanceVar`.
    ///
    /// Additionally it returns the vector of the field elements from the self
    /// parameters, so they can be reused in other gadgets without recalculating
    /// (reconstraining) them.
    #[allow(clippy::type_complexity)]
    pub fn hash<S: CryptographicSponge, T: TranscriptVar<CF2<C>, S>>(
        &self,
        sponge: &T,
        pp_hash: FpVar<CF2<C>>, // public params hash
    ) -> Result<(FpVar<CF2<C>>, Vec<FpVar<CF2<C>>>), SynthesisError> {
        let mut sponge = sponge.clone();
        let U_vec = self.to_native_sponge_field_elements()?;
        sponge.absorb(&pp_hash)?;
        sponge.absorb(&U_vec)?;
        Ok((
            // `unwrap` is safe because the sponge is guaranteed to return a single element
            sponge.squeeze_field_elements(1)?.pop().unwrap(),
            U_vec,
        ))
    }
}

/// In-circuit representation of the Witness associated to the CommittedInstance, but with
/// non-native representation, since it is used to represent the CycleFold witness. This struct is
/// used in the Decider circuit.
#[derive(Debug, Clone)]
pub struct CycleFoldWitnessVar<C: Curve> {
    pub E: Vec<NonNativeUintVar<CF2<C>>>,
    pub rE: NonNativeUintVar<CF2<C>>,
    pub W: Vec<NonNativeUintVar<CF2<C>>>,
    pub rW: NonNativeUintVar<CF2<C>>,
}

impl<C: Curve> AllocVar<CycleFoldWitness<C>, CF2<C>> for CycleFoldWitnessVar<C> {
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
pub struct NIFSFullGadget<C: Curve> {
    _c: PhantomData<C>,
}

impl<C: Curve> NIFSFullGadget<C> {
    pub fn fold_committed_instance(
        r_bits: Vec<Boolean<CF2<C>>>,
        cmT: C::Var,
        ci1: CycleFoldCommittedInstanceVar<C>,
        // ci2 is assumed to be always with cmE=0, u=1 (checks done previous to this method)
        ci2: CycleFoldCommittedInstanceVar<C>,
    ) -> Result<CycleFoldCommittedInstanceVar<C>, SynthesisError> {
        // r_nonnat is equal to r_bits just that in a different format
        let r_nonnat = {
            let mut bits = r_bits.clone();
            bits.resize(CF1::<C>::MODULUS_BIT_SIZE as usize, Boolean::FALSE);
            NonNativeUintVar::from(&bits)
        };
        Ok(CycleFoldCommittedInstanceVar {
            cmE: cmT.scalar_mul_le(r_bits.iter())? + ci1.cmE,
            cmW: ci1.cmW + ci2.cmW.scalar_mul_le(r_bits.iter())?,
            u: ci1.u.add_no_align(&r_nonnat)?.modulo::<CF1<C>>()?,
            x: ci1
                .x
                .iter()
                .zip(ci2.x)
                .map(|(a, b)| {
                    a.add_no_align(&r_nonnat.mul_no_align(&b)?)?
                        .modulo::<CF1<C>>()
                })
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    pub fn verify(
        // assumes that r_bits is equal to r_nonnat just that in a different format
        r_bits: Vec<Boolean<CF2<C>>>,
        cmT: C::Var,
        ci1: CycleFoldCommittedInstanceVar<C>,
        // ci2 is assumed to be always with cmE=0, u=1 (checks done previous to this method)
        ci2: CycleFoldCommittedInstanceVar<C>,
        ci3: CycleFoldCommittedInstanceVar<C>,
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

impl<C: Curve> ArithRelationGadget<CycleFoldWitnessVar<C>, CycleFoldCommittedInstanceVar<C>>
    for R1CSMatricesVar<CF1<C>, NonNativeUintVar<CF2<C>>>
{
    type Evaluation = (Vec<NonNativeUintVar<CF2<C>>>, Vec<NonNativeUintVar<CF2<C>>>);

    fn eval_relation(
        &self,
        w: &CycleFoldWitnessVar<C>,
        u: &CycleFoldCommittedInstanceVar<C>,
    ) -> Result<Self::Evaluation, SynthesisError> {
        self.eval_at_z(&[&[u.u.clone()][..], &u.x, &w.W].concat())
    }

    fn enforce_evaluation(
        w: &CycleFoldWitnessVar<C>,
        _u: &CycleFoldCommittedInstanceVar<C>,
        (AzBz, uCz): Self::Evaluation,
    ) -> Result<(), SynthesisError> {
        EquivalenceGadget::<CF1<C>>::enforce_equivalent(&AzBz[..], &uCz.add(&w.E)?[..])
    }
}

/// CycleFoldChallengeGadget computes the RO challenge used for the CycleFold instances NIFS, it contains a
/// rust-native and a in-circuit compatible versions.
pub struct CycleFoldChallengeGadget<C: Curve> {
    _c: PhantomData<C>, // Nova's Curve2, the one used for the CycleFold circuit
}
impl<C: Curve> CycleFoldChallengeGadget<C> {
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
        u_i: CycleFoldCommittedInstanceVar<C>,
        cmT: C::Var,
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

    type C: Curve;
}

/// CycleFoldCircuit contains the constraints that check the correct fold of the committed
/// instances from Curve1. Namely, it checks the random linear combinations of the elliptic curve
/// (Curve1) points of u_i, U_i leading to U_{i+1}
#[derive(Debug, Clone)]
pub struct CycleFoldCircuit<CFG: CycleFoldConfig> {
    /// r_bits is the bit representation of the r whose powers are used in the
    /// random-linear-combination inside the CycleFoldCircuit
    pub r_bits: Option<Vec<bool>>,
    /// points to be folded in the CycleFoldCircuit
    pub points: Option<Vec<CFG::C>>,
}

impl<CFG: CycleFoldConfig> CycleFoldCircuit<CFG> {
    /// n_points indicates the number of points being folded in the CycleFoldCircuit
    pub fn empty() -> Self {
        Self {
            r_bits: None,
            points: None,
        }
    }
}

impl<CFG: CycleFoldConfig> ConstraintSynthesizer<CF2<CFG::C>> for CycleFoldCircuit<CFG> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<CF2<CFG::C>>,
    ) -> Result<(), SynthesisError> {
        let r_bits = Vec::<Boolean<CF2<CFG::C>>>::new_witness(cs.clone(), || {
            Ok(self
                .r_bits
                .unwrap_or(vec![false; CFG::RANDOMNESS_BIT_LENGTH]))
        })?;
        let points = Vec::<<CFG::C as Curve>::Var>::new_witness(cs.clone(), || {
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
        let mut p_folded = points[CFG::N_INPUT_POINTS - 1].clone();
        for i in (0..CFG::N_INPUT_POINTS - 1).rev() {
            p_folded = p_folded.scalar_mul_le(r_bits.iter())? + points[i].clone();
        }

        // Check that the points coordinates are placed as the public input x:
        // In Nova, this is: x == [r, p1, p2, p3] (wheere p3 is the p_folded).
        // In multifolding schemes such as HyperNova, this is:
        // computed_x = [r, p_0, p_1, p_2, ..., p_n, p_folded],
        // where each p_i is in fact p_i.to_constraint_field()
        let r_fp = r_bits
            .chunks(CF2::<CFG::C>::MODULUS_BIT_SIZE as usize - 1)
            .map(Boolean::le_bits_to_fp)
            .collect::<Result<Vec<_>, _>>()?;
        let points_aux = points
            .iter()
            .map(|p_i| Ok(p_i.to_constraint_field()?[..2].to_vec()))
            .collect::<Result<Vec<_>, SynthesisError>>()?
            .into_iter()
            .flatten()
            .collect();

        let x = [
            r_fp,
            points_aux,
            p_folded.to_constraint_field()?[..2].to_vec(),
        ]
        .concat();
        #[cfg(test)]
        assert_eq!(x.len(), CFG::IO_LEN); // non-constrained sanity check

        // This line "converts" `x` from a witness to a public input.
        // Instead of directly modifying the constraint system, we explicitly
        // allocate a public input and enforce that its value is indeed `x`.
        // While comparing `x` with itself seems redundant, this is necessary
        // because:
        // - `.value()` allows an honest prover to extract public inputs without
        //   computing them outside the circuit.
        // - `.enforce_equal()` prevents a malicious prover from claiming wrong
        //   public inputs that are not the honest `x` computed in-circuit.
        Vec::new_input(cs.clone(), || x.value())?.enforce_equal(&x)?;

        Ok(())
    }
}

/// CycleFoldNIFS is a wrapper on top of Nova's NIFS, which just replaces the `prove` and `verify`
/// methods to use a different ChallengeGadget, but internally reuses the other Nova's NIFS
/// methods.
/// It is a custom implementation that does not follow the NIFSTrait because it needs to work over
/// different fields than the main NIFS impls (Nova, Mova, Ova). Could be abstracted, but it's a
/// tradeoff between overcomplexity at the NIFSTrait and the (not much) need of generalization at
/// the CycleFoldNIFS.
pub struct CycleFoldNIFS<C2: Curve, CS2: CommitmentScheme<C2, H>, const H: bool = false> {
    _c2: PhantomData<C2>,
    _cs: PhantomData<CS2>,
}
impl<C2: Curve, CS2: CommitmentScheme<C2, H>, const H: bool> CycleFoldNIFS<C2, CS2, H> {
    fn prove(
        cf_r_Fq: C2::ScalarField, // C2::Fr==C1::Fq
        cf_W_i: &CycleFoldWitness<C2>,
        cf_U_i: &CycleFoldCommittedInstance<C2>,
        cf_w_i: &CycleFoldWitness<C2>,
        cf_u_i: &CycleFoldCommittedInstance<C2>,
        aux_p: &[C2::ScalarField], // = cf_T
        aux_v: C2,                 // = cf_cmT
    ) -> Result<(CycleFoldWitness<C2>, CycleFoldCommittedInstance<C2>), Error> {
        let w = NIFS::<C2, CS2, PoseidonSponge<C2::ScalarField>, H>::fold_witness(
            cf_r_Fq,
            cf_W_i,
            cf_w_i,
            &aux_p.to_vec(),
        )?;
        let ci = Self::verify(cf_r_Fq, cf_U_i, cf_u_i, &aux_v)?;
        Ok((w, ci))
    }
    fn verify(
        r: C2::ScalarField,
        U_i: &CycleFoldCommittedInstance<C2>,
        u_i: &CycleFoldCommittedInstance<C2>,
        cmT: &C2, // VerifierAux
    ) -> Result<CycleFoldCommittedInstance<C2>, Error> {
        Ok(
            NIFS::<C2, CS2, PoseidonSponge<C2::ScalarField>, H>::fold_committed_instances(
                r, U_i, u_i, cmT,
            ),
        )
    }
}

/// Folds the given cyclefold circuit and its instances. This method is abstracted from any folding
/// scheme struct because it is used both by Nova & HyperNova's CycleFold.
#[allow(clippy::type_complexity)]
#[allow(clippy::too_many_arguments)]
pub fn fold_cyclefold_circuit<CFG, C2, CS2, const H: bool>(
    transcript: &mut impl Transcript<CF2<C2>>,
    cf_r1cs: R1CS<C2::ScalarField>,
    cf_cs_params: CS2::ProverParams,
    pp_hash: CF2<C2>,                       // public params hash
    cf_W_i: CycleFoldWitness<C2>,           // witness of the running instance
    cf_U_i: CycleFoldCommittedInstance<C2>, // running instance
    cf_circuit: CycleFoldCircuit<CFG>,
    mut rng: impl RngCore,
) -> Result<
    (
        CycleFoldCommittedInstance<C2>, // u_i
        CycleFoldWitness<C2>,           // W_i1
        CycleFoldCommittedInstance<C2>, // U_i1
        C2,                             // cmT
    ),
    Error,
>
where
    CFG: CycleFoldConfig,
    C2: Curve<ScalarField = CF2<CFG::C>, BaseField = CF1<CFG::C>>,
    CS2: CommitmentScheme<C2, H>,
{
    let cs2 = ConstraintSystem::new_ref();
    cf_circuit.generate_constraints(cs2.clone())?;

    let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
    let (cf_w_i, cf_x_i) = extract_w_x(&cs2);

    #[cfg(test)]
    assert_eq!(cf_x_i.len(), CFG::IO_LEN);

    // fold cyclefold instances
    let cf_w_i =
        CycleFoldWitness::<C2>::new::<H>(cf_w_i.clone(), cf_r1cs.n_constraints(), &mut rng);
    let cf_u_i = cf_w_i.commit::<CS2, H>(&cf_cs_params, cf_x_i.clone())?;

    // compute T* and cmT* for CycleFoldCircuit
    let (cf_T, cf_cmT) = NIFS::<C2, CS2, PoseidonSponge<CF1<C2>>, H>::compute_cyclefold_cmT(
        &cf_cs_params,
        &cf_r1cs,
        &cf_w_i,
        &cf_u_i,
        &cf_W_i,
        &cf_U_i,
    )?;

    let cf_r_bits = CycleFoldChallengeGadget::get_challenge_native(
        transcript,
        pp_hash,
        cf_U_i.clone(),
        cf_u_i.clone(),
        cf_cmT,
    );
    let cf_r_Fq = CF1::<C2>::from_bigint(BigInteger::from_bits_le(&cf_r_bits))
        .expect("cf_r_bits out of bounds");

    let (cf_W_i1, cf_U_i1) = CycleFoldNIFS::<C2, CS2, H>::prove(
        cf_r_Fq, &cf_W_i, &cf_U_i, &cf_w_i, &cf_u_i, &cf_T, cf_cmT,
    )?;

    #[cfg(test)]
    {
        use crate::{arith::ArithRelation, folding::traits::CommittedInstanceOps};
        cf_u_i.check_incoming()?;
        cf_r1cs.check_relation(&cf_w_i, &cf_u_i)?;
        cf_r1cs.check_relation(&cf_W_i1, &cf_U_i1)?;
    }

    Ok((cf_u_i, cf_W_i1, cf_U_i1, cf_cmT))
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

    struct TestCycleFoldConfig<C: Curve, const N: usize> {
        _c: PhantomData<C>,
    }

    impl<C: Curve, const N: usize> CycleFoldConfig for TestCycleFoldConfig<C, N> {
        const RANDOMNESS_BIT_LENGTH: usize = NOVA_N_BITS_RO;
        const N_INPUT_POINTS: usize = N;
        type C = C;
    }

    #[test]
    fn test_CycleFoldCircuit_n_points_constraints() -> Result<(), Error> {
        const n: usize = 16;
        let mut rng = ark_std::test_rng();

        // points to random-linear-combine
        let points: Vec<Projective> = std::iter::repeat_with(|| Projective::rand(&mut rng))
            .take(n)
            .collect();

        use std::ops::Mul;
        let rho_raw = Fq::rand(&mut rng);
        let rho_bits = rho_raw.into_bigint().to_bits_le()[..NOVA_N_BITS_RO].to_vec();
        let rho_Fq =
            Fq::from_bigint(BigInteger::from_bits_le(&rho_bits)).ok_or(Error::OutOfBounds)?;
        let rho_Fr =
            Fr::from_bigint(BigInteger::from_bits_le(&rho_bits)).ok_or(Error::OutOfBounds)?;
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
        let cf_circuit = CycleFoldCircuit::<TestCycleFoldConfig<Projective, n>> {
            r_bits: Some(rho_bits),
            points: Some(points),
        };
        cf_circuit.generate_constraints(cs.clone())?;
        assert!(cs.is_satisfied()?);
        // `instance_assignment[0]` is the constant term 1
        assert_eq!(&cs.borrow().unwrap().instance_assignment[1..], &x);
        Ok(())
    }

    #[test]
    fn test_nifs_full_gadget() -> Result<(), Error> {
        let mut rng = ark_std::test_rng();

        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript_v = PoseidonSponge::<Fr>::new(&poseidon_config);
        let pp_hash = Fr::rand(&mut rng);

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

        let cmT = Projective::rand(&mut rng); // random only for testing
        let (ci3, r_bits) = NIFS::<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>::verify(
            &mut transcript_v,
            pp_hash,
            &ci1,
            &ci2,
            &cmT,
        )?;

        let cs = ConstraintSystem::<Fq>::new_ref();
        let r_bitsVar = Vec::<Boolean<Fq>>::new_witness(cs.clone(), || Ok(r_bits))?;
        let ci1Var = CycleFoldCommittedInstanceVar::<Projective>::new_witness(cs.clone(), || {
            Ok(ci1.clone())
        })?;
        let ci2Var = CycleFoldCommittedInstanceVar::<Projective>::new_witness(cs.clone(), || {
            Ok(ci2.clone())
        })?;
        let ci3Var = CycleFoldCommittedInstanceVar::<Projective>::new_witness(cs.clone(), || {
            Ok(ci3.clone())
        })?;
        let cmTVar = GVar::new_witness(cs.clone(), || Ok(cmT))?;

        NIFSFullGadget::<Projective>::verify(r_bitsVar, cmTVar, ci1Var, ci2Var, ci3Var)?;
        assert!(cs.is_satisfied()?);
        Ok(())
    }

    #[test]
    fn test_cyclefold_challenge_gadget() -> Result<(), Error> {
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
        let cmT = Projective::rand(&mut rng); // random only for testing

        // compute the challenge natively
        let pp_hash = Fq::from(42u32); // only for test
        let r_bits = CycleFoldChallengeGadget::<Projective>::get_challenge_native(
            &mut transcript,
            pp_hash,
            U_i.clone(),
            u_i.clone(),
            cmT,
        );

        let cs = ConstraintSystem::<Fq>::new_ref();
        let u_iVar = CycleFoldCommittedInstanceVar::<Projective>::new_witness(cs.clone(), || {
            Ok(u_i.clone())
        })?;
        let U_iVar = CycleFoldCommittedInstanceVar::<Projective>::new_witness(cs.clone(), || {
            Ok(U_i.clone())
        })?;
        let cmTVar = GVar::new_witness(cs.clone(), || Ok(cmT))?;
        let mut transcript_var =
            PoseidonSpongeVar::<Fq>::new(ConstraintSystem::<Fq>::new_ref(), &poseidon_config);

        let pp_hashVar = FpVar::<Fq>::new_witness(cs.clone(), || Ok(pp_hash))?;
        let r_bitsVar = CycleFoldChallengeGadget::<Projective>::get_challenge_gadget(
            &mut transcript_var,
            pp_hashVar,
            U_iVar.to_native_sponge_field_elements()?,
            u_iVar,
            cmTVar,
        )?;
        assert!(cs.is_satisfied()?);

        // check that the natively computed and in-circuit computed hashes match
        let rVar = Boolean::le_bits_to_fp(&r_bitsVar)?;
        let r = Fq::from_bigint(BigInteger::from_bits_le(&r_bits)).ok_or(Error::OutOfBounds)?;
        assert_eq!(rVar.value()?, r);
        assert_eq!(r_bitsVar.value()?, r_bits);
        Ok(())
    }

    #[test]
    fn test_cyclefold_hash_gadget() -> Result<(), Error> {
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
        let U_iVar = CycleFoldCommittedInstanceVar::<Projective>::new_witness(cs.clone(), || {
            Ok(U_i.clone())
        })?;
        let pp_hashVar = FpVar::<Fq>::new_witness(cs.clone(), || Ok(pp_hash))?;
        let (hVar, _) = U_iVar.hash(
            &PoseidonSpongeVar::new(cs.clone(), &poseidon_config),
            pp_hashVar,
        )?;
        hVar.enforce_equal(&FpVar::new_witness(cs.clone(), || Ok(h))?)?;
        assert!(cs.is_satisfied()?);
        Ok(())
    }
}
