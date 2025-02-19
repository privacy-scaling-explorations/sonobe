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
use ark_std::{borrow::Borrow, fmt::Debug, marker::PhantomData, rand::RngCore, One};

use super::{
    nonnative::{affine::NonNativeAffineVar, uint::NonNativeUintVar},
    CF1, CF2,
};
use crate::arith::{
    r1cs::{circuits::R1CSMatricesVar, extract_w_x, R1CS},
    ArithRelationGadget,
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

impl<C2: Curve> CycleFoldCommittedInstanceVar<C2> {
    /// Creates a new `CycleFoldCommittedInstanceVar` from the given components.
    pub fn new_incoming_from_components<C1: Curve<ScalarField = C2::BaseField>>(
        cmW: C2::Var,
        r_bits: &[Boolean<CF2<C2>>],
        points: Vec<NonNativeAffineVar<C1>>,
    ) -> Result<Self, SynthesisError> {
        // Construct the public inputs `x` from `r_bits` and `points`.
        // Note that the underlying field can only safely store
        // `CF1::<C2>::MODULUS_BIT_SIZE - 1` bits, but `r_bits` may be longer
        // than that.
        // Thus, we need to chunk `r_bits` into pieces and convert each piece
        // to a `NonNativeUintVar`.
        let x = r_bits
            .chunks(CF1::<C2>::MODULUS_BIT_SIZE as usize - 1)
            .map(|bits| {
                let mut bits = bits.to_vec();
                bits.resize(CF1::<C2>::MODULUS_BIT_SIZE as usize, Boolean::FALSE);
                NonNativeUintVar::from(&bits)
            })
            .chain(points.into_iter().flat_map(|p| [p.x, p.y]))
            .collect::<Vec<_>>();
        Ok(Self {
            // `cmE` is always zero for incoming instances
            cmE: C2::Var::zero(),
            // `u` is always one for incoming instances
            u: NonNativeUintVar::new_constant(ConstraintSystemRef::None, CF1::<C2>::one())?,
            cmW,
            x,
        })
    }
}

impl<C: Curve> CycleFoldCommittedInstance<C> {
    /// hash_cyclefold implements the committed instance hash compatible with the
    /// in-circuit implementation `CycleFoldCommittedInstanceVar::hash`.
    /// Returns `H(U_i)`, where `U_i` is a `CycleFoldCommittedInstance`.
    pub fn hash_cyclefold<T: Transcript<C::BaseField>>(&self, sponge: &T) -> C::BaseField {
        let mut sponge = sponge.clone();
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
    ) -> Result<(FpVar<CF2<C>>, Vec<FpVar<CF2<C>>>), SynthesisError> {
        let mut sponge = sponge.clone();
        let U_vec = self.to_native_sponge_field_elements()?;
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
        U_i: &CycleFoldCommittedInstance<C>,
        u_i: &CycleFoldCommittedInstance<C>,
        cmT: C,
    ) -> Vec<bool> {
        transcript.absorb_nonnative(U_i);
        transcript.absorb_nonnative(u_i);
        transcript.absorb_point(&cmT);
        transcript.squeeze_bits(NOVA_N_BITS_RO)
    }

    // compatible with the native get_challenge_native
    pub fn get_challenge_gadget<S: CryptographicSponge, T: TranscriptVar<C::BaseField, S>>(
        transcript: &mut T,
        U_i_vec: &[FpVar<C::BaseField>],
        u_i: &CycleFoldCommittedInstanceVar<C>,
        cmT: &C::Var,
    ) -> Result<Vec<Boolean<C::BaseField>>, SynthesisError> {
        transcript.absorb(&U_i_vec)?;
        transcript.absorb_nonnative(u_i)?;
        transcript.absorb_point(cmT)?;
        transcript.squeeze_bits(NOVA_N_BITS_RO)
    }
}

/// [`CycleFoldConfig`] controls the behavior of [`CycleFoldCircuit`].
///
/// Looking ahead, the circuit computes the random linear combination of points,
/// which is essentially done by iteratively computing `P = (P + p_i) * r_i`,
/// where `P` is the folded point, `p_i` is the input point, and `r_i` is the
/// randomness.
pub trait CycleFoldConfig<C: Curve>: Sized + Default {
    /// `N_INPUT_POINTS` specifies the number of input points that are folded in
    /// [`CycleFoldCircuit`] via random linear combinations.
    const N_INPUT_POINTS: usize;
    /// `N_UNIQUE_RANDOMNESSES` specifies the number of *unique* randomnesses
    /// allocated in [`CycleFoldCircuit`]. Although the linear combination in
    /// general consists of multiple randomnesses, some folding schemes (such as
    /// Nova and HyperNova) only need a single one. Thus, by setting this value,
    /// the circuit can learn how many randomnesses are used and how long the
    /// public inputs vector should be.
    const N_UNIQUE_RANDOMNESSES: usize;
    /// `RANDOMNESS_BIT_LENGTH` is the maximum bit length of a randomness `r_i`.
    const RANDOMNESS_BIT_LENGTH: usize;
    /// `FIELD_CAPACITY` is the maximum number of bits that can be stored in a
    /// field element.
    ///
    /// By default, `FIELD_CAPACITY` is set to `MODULUS_BIT_SIZE - 1`.
    ///
    /// Given a randomness `r_i` with `RANDOMNESS_BIT_LENGTH` bits, we need
    /// `RANDOMNESS_BIT_LENGTH / FIELD_CAPACITY` field elements to represent it
    /// *compactly* in-circuit.
    const FIELD_CAPACITY: usize = CF2::<C>::MODULUS_BIT_SIZE as usize - 1;

    /// Public inputs length for the [`CycleFoldCircuit`], which depends on the
    /// above constants defined by the concrete folding scheme. For example:
    /// * In Nova, this is `|r| + |p_1| + |p_2| + |P|`
    /// * In HyperNova, this is `|r| + |p_i| * n_points + |P|`.
    /// * In ProtoGalaxy, this is `|[..., r_i, ...]| + |p_i| * n_points + |P|`.
    ///
    /// As explained above, `|r|` (i.e., the length of a single randomness) is
    /// `RANDOMNESS_BIT_LENGTH / FIELD_CAPACITY`.
    /// When there are multiple randomnesses, the length of `|[..., r_i, ...]|`
    /// is `RANDOMNESS_BIT_LENGTH * N_UNIQUE_RANDOMNESSES / FIELD_CAPACITY`, as
    /// the bits of all randomnesses are concatenated before being packed into
    /// field elements.
    /// The length of a point `p_i` when treated as public inputs is 2, as we
    /// only need the `x` and `y` coordinates of the point.
    ///
    /// Thus, `IO_LEN` is `RANDOMNESS_BIT_LENGTH * N_UNIQUE_RANDOMNESSES / FIELD_CAPACITY + 2 * (N_INPUT_POINTS + 1)`.
    const IO_LEN: usize = {
        (Self::RANDOMNESS_BIT_LENGTH * Self::N_UNIQUE_RANDOMNESSES).div_ceil(Self::FIELD_CAPACITY)
            + 2 * (Self::N_INPUT_POINTS + 1)
    };

    /// `alloc_points` allocates the points that are going to be folded in the
    /// [`CycleFoldCircuit`] via random linear combinations.
    ///
    /// The implementation must allocate the points as *witness* variables (i.e.
    /// by calling [`AllocVar::new_witness`]) first, then mark them as public
    /// inputs by calling [`CycleFoldConfig::mark_point_as_public`], and finally
    /// return the allocated witness variables.
    ///
    /// While it is possible to allocate the points as public inputs directly,
    /// we do not use this approach because this will create a longer vector of
    /// public inputs, which is not ideal for the augmented step circuit on the
    /// primary curve.
    fn alloc_points(&self, cs: ConstraintSystemRef<CF2<C>>) -> Result<Vec<C::Var>, SynthesisError>;

    /// `alloc_randomnesses` allocates the randomnesses used as coefficients of
    /// the random linear combinations in the `CycleFoldCircuit`.
    ///
    /// The implementation must allocate the randomnesses as *witness* variables
    /// (i.e. by calling [`AllocVar::new_witness`]) first, then mark them as
    /// public inputs by calling [`CycleFoldConfig::mark_point_as_public`], and
    /// finally return the allocated witness variables.
    ///
    /// See [`CycleFoldConfig::alloc_points`] for the reason why they need to be
    /// allocated as witness variables first and converted to public later.
    ///
    /// In addition, because the circuit computes `P = (P + p_i) * r_i` for each
    /// `i` from `N_INPUT_POINTS - 1` down to `0`, the actual linear combination
    /// is `P = r_0 * p_0 + (r_0 r_1) * p_1 + (r_0 r_1 r_2) * p_2 + ...`. Thus,
    /// to compute `P = R_0 p_0 + R_1 p_1 + R_2 p_2 + ...`, the implementation
    /// should return `r_0 = R_0, r_1 = R_1 / R_0, ..., r_i = R_i / R_{i - 1}`.
    /// A special case is `R_i = R^i`, where the allocated randomnesses become
    /// `r_0 = 1, r_1 = r_2 = ... = R`.
    fn alloc_randomnesses(
        &self,
        cs: ConstraintSystemRef<CF2<C>>,
    ) -> Result<Vec<Vec<Boolean<CF2<C>>>>, SynthesisError>;

    /// `mark_point_as_public` marks a point as public.
    ///
    /// The final vector of public inputs is shorter than the result of calling
    /// [`AllocVar::new_input`], because we only need the x and y coordinates of
    /// the point, but the `infinity` flag is not necessary.
    fn mark_point_as_public(point: &C::Var) -> Result<(), SynthesisError> {
        for x in &point.to_constraint_field()?[..2] {
            // This line "converts" `x` from a witness to a public input.
            // Instead of directly modifying the constraint system, we explicitly
            // allocate a public input and enforce that its value is indeed `x`.
            // While comparing `x` with itself seems redundant, this is necessary
            // because:
            // - `.value()` allows an honest prover to extract public inputs without
            //   computing them outside the circuit.
            // - `.enforce_equal()` prevents a malicious prover from claiming wrong
            //   public inputs that are not the honest `x` computed in-circuit.
            FpVar::new_input(x.cs().clone(), || x.value())?.enforce_equal(x)?;
        }
        Ok(())
    }

    /// `mark_randomness_as_public` marks randomness as public.
    ///
    /// The final vector of public inputs is shorter than the result of calling
    /// [`AllocVar::new_input`], because we pack the bits of randomness into
    /// a compact field elements.
    fn mark_randomness_as_public(r: &[Boolean<CF2<C>>]) -> Result<(), SynthesisError> {
        for bits in r.chunks(Self::FIELD_CAPACITY) {
            let x = Boolean::le_bits_to_fp(bits)?;
            FpVar::new_input(x.cs().clone(), || x.value())?.enforce_equal(&x)?;
        }
        Ok(())
    }

    /// `build_circuit` creates a new [`CycleFoldCircuit`] with `self` as the
    /// configuration.
    fn build_circuit(self) -> CycleFoldCircuit<C, Self> {
        CycleFoldCircuit {
            _c: PhantomData,
            cfg: self,
        }
    }
}

#[derive(Debug, Clone)]
pub struct CycleFoldCircuit<C: Curve, CFG: CycleFoldConfig<C>> {
    _c: PhantomData<C>,
    cfg: CFG,
}

impl<C: Curve, CFG: CycleFoldConfig<C>> Default for CycleFoldCircuit<C, CFG> {
    fn default() -> Self {
        CFG::default().build_circuit()
    }
}

impl<C: Curve, CFG: CycleFoldConfig<C>> ConstraintSynthesizer<CF2<C>> for CycleFoldCircuit<C, CFG> {
    fn generate_constraints(self, cs: ConstraintSystemRef<CF2<C>>) -> Result<(), SynthesisError> {
        let rs = self.cfg.alloc_randomnesses(cs.clone())?;
        let points = self.cfg.alloc_points(cs.clone())?;

        #[cfg(test)]
        {
            assert_eq!(CFG::N_INPUT_POINTS, points.len());
            assert_eq!(CFG::N_INPUT_POINTS, rs.len());
            for r in &rs {
                assert_eq!(CFG::RANDOMNESS_BIT_LENGTH, r.len());
            }
        }

        // A slightly optimized version of `scalar_mul_le`.
        fn point_mul<C: Curve>(
            point: &C::Var,
            r: &[Boolean<CF2<C>>],
        ) -> Result<C::Var, SynthesisError> {
            if r.is_constant() {
                let r = CF1::<C>::from(<CF1<C> as PrimeField>::BigInt::from_bits_le(&r.value()?));
                if r.is_one() {
                    return Ok(point.clone());
                }
            }
            point.scalar_mul_le(r.iter())
        }

        // Given a vector of points (over the primary curve) that are obtained
        // from the instances of the folding scheme, we fold them *natively* in
        // the CycleFold circuit (over the secondary curve).
        // * In Nova, we need to compute P = p_0 + R * p_1.
        //   - for the cmW we're computing: U_i1.cmW = U_i.cmW + R * u_i.cmW
        //   - for the cmE we're computing: U_i1.cmE = U_i.cmE + R * cmT + R^2 * u_i.cmE, where u_i.cmE
        //     is assumed to be 0, so, U_i1.cmE = U_i.cmE + R * cmT
        // * In HyperNova, we need to compute P = p_0 + R * p_1 + R^2 * p_2 + ... + R^{n-1} * p_{n-1}.
        // * In ProtoGalaxy, we need to compute P = R_0 * p_0 + R_1 * p_1 + R_2 * p_2 + ... + R_{n-1} * p_{n-1}.
        //
        // To handle HyperNova more efficiently (with less constraints), we do
        // P = ((((p_{n-1} * R) + p_{n-2}) * R + p_{n-3}) * R + ...) * R + p_0.
        // This can be done iteratively by computing P = (P + p_i) * R.
        //
        // We further generalize this to support ProtoGalaxy, which now becomes
        // P = (((((p_{n-1} * r_{n-1}) + p_{n-2}) * r_{n-2} + p_{n-3}) * r_{n-3} + ...) * r_1 + p_0) * r_0
        //
        // Here, r_0 = 1, r_1 = r_2 = ... = r_{n-1} = R for Nova and HyperNova,
        // and r_i = R_i / R_{i - 1} for ProtoGalaxy.
        let mut p_folded = point_mul::<C>(
            &points[CFG::N_INPUT_POINTS - 1],
            &rs[CFG::N_INPUT_POINTS - 1],
        )?;
        for i in (0..CFG::N_INPUT_POINTS - 1).rev() {
            p_folded = point_mul::<C>(&(p_folded + &points[i]), &rs[i])?;
        }

        CFG::mark_point_as_public(&p_folded)?;

        Ok(())
    }
}

impl<C1: Curve, CFG: CycleFoldConfig<C1>> CycleFoldCircuit<C1, CFG> {
    /// Generates a pair of incoming instance and witness for the CycleFold
    /// circuit.
    pub fn generate_incoming_instance_witness<
        C2: Curve<ScalarField = CF2<C1>, BaseField = CF1<C1>>,
        CS2: CommitmentScheme<C2, H>,
        const H: bool,
    >(
        self,
        cf_cs_params: &CS2::ProverParams,
        mut rng: impl RngCore,
    ) -> Result<(CycleFoldWitness<C2>, CycleFoldCommittedInstance<C2>), Error> {
        let cs2 = ConstraintSystem::new_ref();
        self.generate_constraints(cs2.clone())?;

        let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let (cf_w_i, cf_x_i) = extract_w_x(&cs2);

        #[cfg(test)]
        assert_eq!(cf_x_i.len(), CFG::IO_LEN);

        // generate cyclefold instances
        let cf_w_i = CycleFoldWitness::<C2>::new::<H>(cf_w_i, cs2.num_constraints, &mut rng);
        let cf_u_i = cf_w_i.commit::<CS2, H>(cf_cs_params, cf_x_i)?;

        Ok((cf_w_i, cf_u_i))
    }
}

/// [`CycleFoldAugmentationGadget`] implements methods for folding multiple
/// CycleFold instances, both natively and in the augmented step circuit.
pub struct CycleFoldAugmentationGadget;

impl CycleFoldAugmentationGadget {
    #[allow(clippy::too_many_arguments, clippy::type_complexity)]
    pub fn fold_native<C: Curve, CS: CommitmentScheme<C, H>, const H: bool>(
        transcript: &mut impl Transcript<CF2<C>>,
        cf_r1cs: &R1CS<C::ScalarField>,
        cf_cs_params: &CS::ProverParams,
        mut cf_W: CycleFoldWitness<C>, // witness of the running instance
        mut cf_U: CycleFoldCommittedInstance<C>, // running instance
        cf_ws: Vec<CycleFoldWitness<C>>, // witnesses of the incoming instances
        cf_us: Vec<CycleFoldCommittedInstance<C>>, // incoming instances
    ) -> Result<
        (
            CycleFoldWitness<C>,           // W_i1
            CycleFoldCommittedInstance<C>, // U_i1
            Vec<C>,                        // cmT
        ),
        Error,
    > {
        assert_eq!(cf_ws.len(), cf_us.len());
        let mut cf_cmTs = vec![];

        for (cf_w, cf_u) in cf_ws.into_iter().zip(cf_us) {
            // compute T* and cmT* for CycleFoldCircuit
            let (cf_T, cf_cmT) = NIFS::<C, CS, PoseidonSponge<CF1<C>>, H>::compute_cyclefold_cmT(
                cf_cs_params,
                cf_r1cs,
                &cf_w,
                &cf_u,
                &cf_W,
                &cf_U,
            )?;
            cf_cmTs.push(cf_cmT);

            let cf_r_bits =
                CycleFoldChallengeGadget::get_challenge_native(transcript, &cf_U, &cf_u, cf_cmT);
            let cf_r_Fq = CF1::<C>::from(<CF1<C> as PrimeField>::BigInt::from_bits_le(&cf_r_bits));

            (cf_W, cf_U) = CycleFoldNIFS::<C, CS, H>::prove(
                cf_r_Fq, &cf_W, &cf_U, &cf_w, &cf_u, &cf_T, cf_cmT,
            )?;

            #[cfg(test)]
            {
                use crate::{arith::ArithRelation, folding::traits::CommittedInstanceOps};
                cf_u.check_incoming()?;
                cf_r1cs.check_relation(&cf_w, &cf_u)?;
                cf_r1cs.check_relation(&cf_W, &cf_U)?;
            }
        }

        Ok((cf_W, cf_U, cf_cmTs))
    }

    pub fn fold_gadget<C2: Curve, S: CryptographicSponge>(
        transcript: &mut impl TranscriptVar<CF2<C2>, S>,
        mut cf_U: CycleFoldCommittedInstanceVar<C2>,
        cf_us: Vec<CycleFoldCommittedInstanceVar<C2>>,
        cf_cmTs: Vec<C2::Var>,
    ) -> Result<CycleFoldCommittedInstanceVar<C2>, SynthesisError> {
        assert_eq!(cf_us.len(), cf_cmTs.len());

        // Fold the incoming CycleFold instances into the running CycleFold
        // instance in a iterative way, since `NIFSFullGadget` only supports
        // folding one incoming instance at a time.
        for (cf_u, cmT) in cf_us.into_iter().zip(cf_cmTs) {
            let cf_r_bits = CycleFoldChallengeGadget::get_challenge_gadget(
                transcript,
                &cf_U.to_native_sponge_field_elements()?,
                &cf_u,
                &cmT,
            )?;
            // Fold the current incoming CycleFold instance `cf_u` into the
            // running CycleFold instance `cf_U`.
            cf_U = NIFSFullGadget::fold_committed_instance(cf_r_bits, cmT, cf_U, cf_u)?;
        }

        Ok(cf_U)
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

#[cfg(test)]
pub mod tests {
    use ark_bn254::{constraints::GVar, Fq, Fr, G1Projective as Projective};
    use ark_crypto_primitives::sponge::poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge};
    use ark_r1cs_std::R1CSVar;
    use ark_std::{One, UniformRand, Zero};

    use super::*;
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::CommittedInstance;
    use crate::transcript::poseidon::poseidon_canonical_config;
    use crate::utils::get_cm_coordinates;

    struct TestCycleFoldConfig<C: Curve, const N: usize> {
        r: CF1<C>,
        points: Vec<C>,
    }

    impl<C: Curve, const N: usize> Default for TestCycleFoldConfig<C, N> {
        fn default() -> Self {
            let r = CF1::<C>::zero();
            let points = vec![C::zero(); N];
            Self { r, points }
        }
    }

    impl<C: Curve, const N: usize> CycleFoldConfig<C> for TestCycleFoldConfig<C, N> {
        const RANDOMNESS_BIT_LENGTH: usize = NOVA_N_BITS_RO;
        const N_INPUT_POINTS: usize = N;
        const N_UNIQUE_RANDOMNESSES: usize = 1;

        fn alloc_points(
            &self,
            cs: ConstraintSystemRef<CF2<C>>,
        ) -> Result<Vec<C::Var>, SynthesisError> {
            let points = Vec::new_witness(cs.clone(), || Ok(self.points.clone()))?;
            for point in &points {
                Self::mark_point_as_public(point)?;
            }
            Ok(points)
        }

        fn alloc_randomnesses(
            &self,
            cs: ConstraintSystemRef<CF2<C>>,
        ) -> Result<Vec<Vec<Boolean<CF2<C>>>>, SynthesisError> {
            let one = &CF1::<C>::one().into_bigint().to_bits_le()[..NOVA_N_BITS_RO];
            let r = &self.r.into_bigint().to_bits_le()[..NOVA_N_BITS_RO];
            let one_var = Vec::new_constant(cs.clone(), one)?;
            let r_var = Vec::new_witness(cs.clone(), || Ok(r))?;
            Self::mark_randomness_as_public(&r_var)?;
            Ok([vec![one_var], vec![r_var; N - 1]].concat())
        }
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
        let cf_circuit = TestCycleFoldConfig::<Projective, n> { r: rho_Fr, points }.build_circuit();
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
        let pp_hash = Fr::rand(&mut rng);
        let mut transcript_v = PoseidonSponge::<Fr>::new_with_pp_hash(&poseidon_config, pp_hash);

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
        let pp_hash = Fq::from(42u32); // only for test
        let mut transcript = PoseidonSponge::<Fq>::new_with_pp_hash(&poseidon_config, pp_hash);

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
        let r_bits = CycleFoldChallengeGadget::<Projective>::get_challenge_native(
            &mut transcript,
            &U_i,
            &u_i,
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
        let pp_hashVar = FpVar::<Fq>::new_witness(cs.clone(), || Ok(pp_hash))?;
        let mut transcript_var =
            PoseidonSpongeVar::<Fq>::new_with_pp_hash(&poseidon_config, &pp_hashVar)?;

        let r_bitsVar = CycleFoldChallengeGadget::<Projective>::get_challenge_gadget(
            &mut transcript_var,
            &U_iVar.to_native_sponge_field_elements()?,
            &u_iVar,
            &cmTVar,
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
        let pp_hash = Fq::from(42u32); // only for test
        let sponge = PoseidonSponge::<Fq>::new_with_pp_hash(&poseidon_config, pp_hash);

        let U_i = CycleFoldCommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: std::iter::repeat_with(|| Fr::rand(&mut rng))
                .take(TestCycleFoldConfig::<Projective, 2>::IO_LEN)
                .collect(),
        };
        let h = U_i.hash_cyclefold(&sponge);

        let cs = ConstraintSystem::<Fq>::new_ref();
        let U_iVar = CycleFoldCommittedInstanceVar::<Projective>::new_witness(cs.clone(), || {
            Ok(U_i.clone())
        })?;
        let pp_hashVar = FpVar::<Fq>::new_witness(cs.clone(), || Ok(pp_hash))?;
        let (hVar, _) = U_iVar.hash(&PoseidonSpongeVar::new_with_pp_hash(
            &poseidon_config,
            &pp_hashVar,
        )?)?;
        hVar.enforce_equal(&FpVar::new_witness(cs.clone(), || Ok(h))?)?;
        assert!(cs.is_satisfied()?);
        Ok(())
    }
}
