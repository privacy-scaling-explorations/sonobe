/// Implements the scheme described in [ProtoGalaxy](https://eprint.iacr.org/2023/1106.pdf)
use ark_crypto_primitives::sponge::{
    constraints::{AbsorbGadget, CryptographicSpongeVar},
    poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    fields::fp::FpVar,
    R1CSVar,
};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::{borrow::Borrow, marker::PhantomData, Zero};
use thiserror::Error;

use crate::commitment::CommitmentScheme;

use super::circuits::{
    cyclefold::{CycleFoldCircuit, CycleFoldConfig},
    nonnative::affine::NonNativeAffineVar,
    CF1,
};

pub mod circuits;
pub mod folding;
pub mod traits;
pub(crate) mod utils;

struct ProtoGalaxyCycleFoldConfig<C: CurveGroup> {
    _c: PhantomData<C>,
}

impl<C: CurveGroup> CycleFoldConfig for ProtoGalaxyCycleFoldConfig<C> {
    const RANDOMNESS_BIT_LENGTH: usize = C::ScalarField::MODULUS_BIT_SIZE as usize;
    const N_INPUT_POINTS: usize = 2;
    type C = C;
    type F = C::BaseField;
}

type ProtoGalaxyCycleFoldCircuit<C, GC> = CycleFoldCircuit<ProtoGalaxyCycleFoldConfig<C>, GC>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommittedInstance<C: CurveGroup> {
    phi: C,
    betas: Vec<C::ScalarField>,
    e: C::ScalarField,
    x: Vec<C::ScalarField>,
}

impl<C: CurveGroup> CommittedInstance<C> {
    pub fn dummy_running(io_len: usize, t: usize) -> Self {
        Self {
            phi: C::zero(),
            betas: vec![C::ScalarField::zero(); t],
            e: C::ScalarField::zero(),
            x: vec![C::ScalarField::zero(); io_len],
        }
    }

    pub fn dummy_incoming(io_len: usize) -> Self {
        Self::dummy_running(io_len, 0)
    }
}

impl<C: CurveGroup> CommittedInstance<C>
where
    C::ScalarField: Absorb,
    C::BaseField: PrimeField,
{
    /// hash implements the committed instance hash compatible with the gadget implemented in
    /// CommittedInstanceVar.hash.
    /// Returns `H(i, z_0, z_i, U_i)`, where `i` can be `i` but also `i+1`, and `U_i` is the
    /// `CommittedInstance`.
    pub fn hash(
        &self,
        sponge: &PoseidonSponge<C::ScalarField>,
        pp_hash: C::ScalarField,
        i: C::ScalarField,
        z_0: Vec<C::ScalarField>,
        z_i: Vec<C::ScalarField>,
    ) -> C::ScalarField {
        let mut sponge = sponge.clone();
        sponge.absorb(&pp_hash);
        sponge.absorb(&i);
        sponge.absorb(&z_0);
        sponge.absorb(&z_i);
        sponge.absorb(&self);
        sponge.squeeze_field_elements(1)[0]
    }
}

#[derive(Clone, Debug)]
pub struct CommittedInstanceVar<C: CurveGroup> {
    phi: NonNativeAffineVar<C>,
    betas: Vec<FpVar<C::ScalarField>>,
    e: FpVar<C::ScalarField>,
    x: Vec<FpVar<C::ScalarField>>,
}

impl<C: CurveGroup> AllocVar<CommittedInstance<C>, C::ScalarField> for CommittedInstanceVar<C> {
    fn new_variable<T: Borrow<CommittedInstance<C>>>(
        cs: impl Into<Namespace<C::ScalarField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|u| {
            let cs = cs.into();

            let u = u.borrow();

            Ok(Self {
                phi: NonNativeAffineVar::new_variable(cs.clone(), || Ok(u.phi), mode)?,
                betas: Vec::new_variable(cs.clone(), || Ok(u.betas.clone()), mode)?,
                e: FpVar::new_variable(cs.clone(), || Ok(u.e), mode)?,
                x: Vec::new_variable(cs.clone(), || Ok(u.x.clone()), mode)?,
            })
        })
    }
}

impl<C: CurveGroup> R1CSVar<C::ScalarField> for CommittedInstanceVar<C> {
    type Value = CommittedInstance<C>;

    fn cs(&self) -> ConstraintSystemRef<C::ScalarField> {
        self.phi
            .cs()
            .or(self.betas.cs())
            .or(self.e.cs())
            .or(self.x.cs())
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        Ok(CommittedInstance {
            phi: self.phi.value()?,
            betas: self
                .betas
                .iter()
                .map(|v| v.value())
                .collect::<Result<_, _>>()?,
            e: self.e.value()?,
            x: self.x.iter().map(|v| v.value()).collect::<Result<_, _>>()?,
        })
    }
}

impl<C: CurveGroup<ScalarField: Absorb, BaseField: PrimeField>> CommittedInstanceVar<C> {
    /// hash implements the committed instance hash compatible with the native implementation from
    /// CommittedInstance.hash.
    /// Returns `H(i, z_0, z_i, U_i)`, where `i` can be `i` but also `i+1`, and `U` is the
    /// `CommittedInstance`.
    /// Additionally it returns the vector of the field elements from the self parameters, so they
    /// can be reused in other gadgets avoiding recalculating (reconstraining) them.
    #[allow(clippy::type_complexity)]
    pub fn hash(
        self,
        sponge: &PoseidonSpongeVar<CF1<C>>,
        pp_hash: FpVar<CF1<C>>,
        i: FpVar<CF1<C>>,
        z_0: Vec<FpVar<CF1<C>>>,
        z_i: Vec<FpVar<CF1<C>>>,
    ) -> Result<(FpVar<CF1<C>>, Vec<FpVar<CF1<C>>>), SynthesisError> {
        let mut sponge = sponge.clone();
        let U_vec = self.to_sponge_field_elements()?;
        sponge.absorb(&pp_hash)?;
        sponge.absorb(&i)?;
        sponge.absorb(&z_0)?;
        sponge.absorb(&z_i)?;
        sponge.absorb(&U_vec)?;
        Ok((sponge.squeeze_field_elements(1)?.pop().unwrap(), U_vec))
    }
}

#[derive(Clone, Debug)]
pub struct Witness<F: PrimeField> {
    w: Vec<F>,
    r_w: F,
}

impl<F: PrimeField> Witness<F> {
    pub fn new(w: Vec<F>) -> Self {
        // note: at the current version, we don't use the blinding factors and we set them to 0
        // always.
        Self { w, r_w: F::zero() }
    }

    pub fn commit<CS: CommitmentScheme<C>, C: CurveGroup<ScalarField = F>>(
        &self,
        params: &CS::ProverParams,
        x: Vec<F>,
    ) -> Result<CommittedInstance<C>, crate::Error> {
        let phi = CS::commit(params, &self.w, &self.r_w)?;
        Ok(CommittedInstance {
            phi,
            x,
            e: F::zero(),
            betas: vec![],
        })
    }
}

#[derive(Debug, Error, PartialEq)]
pub enum ProtoGalaxyError {
    #[error("The remainder from G(X)-F(α)*L_0(X)) / Z(X) should be zero")]
    RemainderNotZero,
    #[error("Could not divide by vanishing polynomial")]
    CouldNotDivideByVanishing,
    #[error("The number of incoming instances + 1 should be a power of two, current number of instances: {0}")]
    WrongNumInstances(usize),
    #[error("The number of incoming items should be a power of two, current number of coefficients: {0}")]
    BTreeNotFull(usize),
    #[error("The lengths of β and δ do not equal: |β| = {0}, |δ|={0}")]
    WrongLenBetas(usize, usize),
}
