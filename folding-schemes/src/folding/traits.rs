use ark_crypto_primitives::sponge::{
    constraints::{AbsorbGadget, CryptographicSpongeVar},
    poseidon::constraints::PoseidonSpongeVar,
    Absorb,
};
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar};
use ark_relations::r1cs::SynthesisError;

use crate::{
    transcript::{AbsorbNonNativeGadget, Transcript},
    Curve, Error,
};

use super::circuits::CF1;

pub trait CommittedInstanceOps<C: Curve>: Inputize<CF1<C>> {
    /// The in-circuit representation of the committed instance.
    type Var: AllocVar<Self, CF1<C>> + CommittedInstanceVarOps<C>;
    /// `hash` implements the committed instance hash compatible with the
    /// in-circuit implementation from `CommittedInstanceVarOps::hash`.
    ///
    /// Returns `H(i, z_0, z_i, U_i)`, where `i` can be `i` but also `i+1`, and
    /// `U_i` is the committed instance `self`.
    fn hash<T: Transcript<CF1<C>>>(
        &self,
        sponge: &T,
        i: CF1<C>,
        z_0: &[CF1<C>],
        z_i: &[CF1<C>],
    ) -> CF1<C>
    where
        Self: Sized + Absorb,
    {
        let mut sponge = sponge.clone();
        sponge.absorb(&i);
        sponge.absorb(&z_0);
        sponge.absorb(&z_i);
        sponge.absorb(&self);
        sponge.squeeze_field_elements(1)[0]
    }

    /// Returns the commitments contained in the committed instance.
    fn get_commitments(&self) -> Vec<C>;

    /// Returns `true` if the committed instance is an incoming instance, and
    /// `false` if it is a running instance.
    fn is_incoming(&self) -> bool;

    /// Checks if the committed instance is an incoming instance.
    fn check_incoming(&self) -> Result<(), Error> {
        self.is_incoming()
            .then_some(())
            .ok_or(Error::NotIncomingCommittedInstance)
    }
}

pub trait CommittedInstanceVarOps<C: Curve> {
    type PointVar: AbsorbNonNativeGadget<CF1<C>>;
    /// `hash` implements the in-circuit committed instance hash compatible with
    /// the native implementation from `CommittedInstanceOps::hash`.
    /// Returns `H(i, z_0, z_i, U_i)`, where `i` can be `i` but also `i+1`, and
    /// `U_i` is the committed instance `self`.
    ///
    /// Additionally it returns the in-circuit representation of the committed
    /// instance `self` as a vector of field elements, so they can be reused in
    /// other gadgets avoiding recalculating (reconstraining) them.
    #[allow(clippy::type_complexity)]
    fn hash(
        &self,
        sponge: &PoseidonSpongeVar<CF1<C>>,
        i: &FpVar<CF1<C>>,
        z_0: &[FpVar<CF1<C>>],
        z_i: &[FpVar<CF1<C>>],
    ) -> Result<(FpVar<CF1<C>>, Vec<FpVar<CF1<C>>>), SynthesisError>
    where
        Self: AbsorbGadget<CF1<C>>,
    {
        let mut sponge = sponge.clone();
        let U_vec = self.to_sponge_field_elements()?;
        sponge.absorb(&i)?;
        sponge.absorb(&z_0)?;
        sponge.absorb(&z_i)?;
        sponge.absorb(&U_vec)?;
        Ok((
            // `unwrap` is safe because the sponge is guaranteed to return a single element
            sponge.squeeze_field_elements(1)?.pop().unwrap(),
            U_vec,
        ))
    }

    /// Returns the commitments contained in the committed instance.
    fn get_commitments(&self) -> Vec<Self::PointVar>;

    /// Returns the public inputs contained in the committed instance.
    fn get_public_inputs(&self) -> &[FpVar<CF1<C>>];

    /// Generates constraints to enforce that the committed instance is an
    /// incoming instance.
    fn enforce_incoming(&self) -> Result<(), SynthesisError>;

    /// Generates constraints to enforce that the committed instance `self` is
    /// partially equal to another committed instance `other`.
    /// Here, only field elements are compared, while commitments (points) are
    /// not.
    fn enforce_partial_equal(&self, other: &Self) -> Result<(), SynthesisError>;
}

pub trait WitnessOps<F: PrimeField> {
    /// The in-circuit representation of the witness.
    type Var: AllocVar<Self, F> + WitnessVarOps<F>;

    /// Returns the openings (i.e., the values being committed to and the
    /// randomness) contained in the witness.
    fn get_openings(&self) -> Vec<(&[F], F)>;
}

pub trait WitnessVarOps<F: PrimeField> {
    /// Returns the openings (i.e., the values being committed to and the
    /// randomness) contained in the witness.
    fn get_openings(&self) -> Vec<(&[FpVar<F>], FpVar<F>)>;
}

pub trait Dummy<Cfg> {
    fn dummy(cfg: Cfg) -> Self;
}

impl<T: Default + Clone> Dummy<usize> for Vec<T> {
    fn dummy(cfg: usize) -> Self {
        vec![Default::default(); cfg]
    }
}

impl<T: Default> Dummy<()> for T {
    fn dummy(_: ()) -> Self {
        Default::default()
    }
}

/// Converts a value `self` into a vector of field elements, ordered in the same
/// way as how a variable of type `Var` would be represented *natively* in the
/// circuit.
///
/// This is useful for the verifier to compute the public inputs.
pub trait Inputize<F> {
    fn inputize(&self) -> Vec<F>;
}

/// Converts a value `self` into a vector of field elements, ordered in the same
/// way as how a variable of type `Var` would be represented *non-natively* in
/// the circuit.
///
/// This is useful for the verifier to compute the public inputs.
///
/// Note that we require this trait because we need to distinguish between some
/// data types that are represented both natively and non-natively in-circuit
/// (e.g., field elements can have type `FpVar` and `NonNativeUintVar`).
pub trait InputizeNonNative<F> {
    fn inputize_nonnative(&self) -> Vec<F>;
}

impl<F, T: Inputize<F>> Inputize<F> for [T] {
    fn inputize(&self) -> Vec<F> {
        self.iter().flat_map(Inputize::<F>::inputize).collect()
    }
}

impl<F, T: InputizeNonNative<F>> InputizeNonNative<F> for [T] {
    fn inputize_nonnative(&self) -> Vec<F> {
        self.iter()
            .flat_map(InputizeNonNative::<F>::inputize_nonnative)
            .collect()
    }
}
