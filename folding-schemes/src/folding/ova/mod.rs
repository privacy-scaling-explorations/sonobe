/// Implements the scheme described in [Nova](https://eprint.iacr.org/2021/370.pdf) and
/// [CycleFold](https://eprint.iacr.org/2023/1192.pdf).
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::fmt::Debug;
use ark_std::rand::RngCore;
use ark_std::{One, UniformRand, Zero};

use crate::arith::r1cs::R1CS;
use crate::commitment::CommitmentScheme;
use crate::folding::{circuits::CF1, traits::Dummy};
use crate::transcript::AbsorbNonNative;
use crate::Error;

pub mod circuits;
pub mod nifs;

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommittedInstance<C: CurveGroup> {
    pub mu: C::ScalarField,
    pub x: Vec<C::ScalarField>,
    pub cmWE: C,
}

impl<C: CurveGroup> Absorb for CommittedInstance<C>
where
    C::ScalarField: Absorb,
{
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        C::ScalarField::batch_to_sponge_bytes(&self.to_sponge_field_elements_as_vec(), dest);
    }

    fn to_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        self.mu.to_sponge_field_elements(dest);
        self.x.to_sponge_field_elements(dest);
        // We cannot call `to_native_sponge_field_elements(dest)` directly, as
        // `to_native_sponge_field_elements` needs `F` to be `C::ScalarField`,
        // but here `F` is a generic `PrimeField`.
        self.cmWE
            .to_native_sponge_field_elements_as_vec()
            .to_sponge_field_elements(dest);
    }
}

#[derive(Debug, Clone)]
pub(crate) struct TestingWitness<C: CurveGroup> {
    pub(crate) w: Vec<C::ScalarField>,
    pub(crate) e: Vec<C::ScalarField>,
    pub(crate) rW: C::ScalarField,
}

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Witness<C: CurveGroup> {
    pub w: Vec<C::ScalarField>,
    pub rW: C::ScalarField,
}

impl<C: CurveGroup> Witness<C> {
    pub fn new<const H: bool>(w: Vec<C::ScalarField>, mut rng: impl RngCore) -> Self {
        Self {
            w,
            rW: if H {
                C::ScalarField::rand(&mut rng)
            } else {
                C::ScalarField::zero()
            },
        }
    }

    pub fn commit<CS: CommitmentScheme<C, HC>, const HC: bool>(
        &self,
        params: &CS::ProverParams,
        t_or_e: Vec<C::ScalarField>,
        x: Vec<C::ScalarField>,
    ) -> Result<CommittedInstance<C>, Error> {
        let cmWE = CS::commit(params, &[self.w.clone(), t_or_e].concat(), &self.rW)?;
        Ok(CommittedInstance {
            mu: C::ScalarField::one(),
            cmWE,
            x,
        })
    }
}

impl<C: CurveGroup> Dummy<&R1CS<CF1<C>>> for Witness<C> {
    fn dummy(r1cs: &R1CS<CF1<C>>) -> Self {
        Self {
            w: vec![C::ScalarField::zero(); r1cs.A.n_cols - 1 - r1cs.l],
            rW: C::ScalarField::zero(),
        }
    }
}
