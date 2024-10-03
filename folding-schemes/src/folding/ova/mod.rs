use std::marker::PhantomData;

/// Implements the scheme described in [Ova](https://hackmd.io/V4838nnlRKal9ZiTHiGYzw?view).
/// Ova is a slight modification to Nova that shaves off 1 group operation and a few hashes.
/// The key idea is that we can commit to $T$ and $W$ in one commitment.
///
/// This slightly breaks the abstraction between the IVC scheme and the accumulation scheme.
/// We assume that the accumulation prover receives $\vec{w}$ as input which proves the current step
/// of the computation and that the *previous* accumulation was performed correctly.
/// Note that $\vec{w}$ can be generated without being aware of $\vec{t}$ or $\alpha$.
/// Alternatively the accumulation prover can receive the commitment to $\vec{w}$ as input
/// and add to it the commitment to $\vec{t}$.
///
/// This yields a commitment to the concatenated vector $\vec{w}||\vec{t}$.
/// This works because both $W$ and $T$ are multiplied by the same challenge $\alpha$ in Nova.
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::fmt::Debug;
use ark_std::rand::RngCore;
use ark_std::{One, UniformRand, Zero};

use crate::arith::r1cs::R1CS;
use crate::commitment::CommitmentScheme;
use crate::constants::NOVA_N_BITS_RO;
use crate::folding::{circuits::CF1, traits::Dummy};
use crate::transcript::{AbsorbNonNative, Transcript};
use crate::Error;

pub mod nifs;

/// A CommittedInstance in [Ova](https://hackmd.io/V4838nnlRKal9ZiTHiGYzw?view) is represented by `W` or `W'`.
/// It is the result of the commitment to a vector that contains the witness `w` concatenated
/// with `t` or `e` + the public inputs `x` and a relaxation factor `mu`.
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

// Clippy flag needed for now.
#[allow(dead_code)]
/// A Witness in [Ova](https://hackmd.io/V4838nnlRKal9ZiTHiGYzw?view) is represented by `w`.
/// It also contains a blinder which can or not be used when committing to the witness itself.
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Witness<C: CurveGroup> {
    pub w: Vec<C::ScalarField>,
    pub rW: C::ScalarField,
}

impl<C: CurveGroup> Witness<C> {
    /// Generates a new `Witness` instance from a given witness vector.
    /// If `H = true`, then we assume we want to blind it at commitment time,
    /// hence sampling `rW` from the randomness passed.
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

    /// Computes the `W` or `W'` commitment (The accumulated-instance W' or the incoming-instance W)
    /// as specified in Ova. See: <https://hackmd.io/V4838nnlRKal9ZiTHiGYzw?view#Construction>.
    ///
    /// This is the result of concatenating the accumulated-instance `w` vector with
    /// `e` or `t`.
    /// Generates a [`CommittedInstance`] as a result which will or not be blinded depending on how the
    /// const generic `HC` is set up.
    ///
    /// This is the exact trick that allows Ova to save up 1 commitment with respect to Nova.
    /// At the cost of loosing the PCD property and only maintaining the IVC one.
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

pub struct ChallengeGadget<C: CurveGroup> {
    _c: PhantomData<C>,
}
impl<C: CurveGroup> ChallengeGadget<C>
where
    C: CurveGroup,
    <C as CurveGroup>::BaseField: PrimeField,
    <C as Group>::ScalarField: Absorb,
{
    pub fn get_challenge_native<T: Transcript<C::ScalarField>>(
        transcript: &mut T,
        pp_hash: C::ScalarField, // public params hash
        // Running instance
        U_i: CommittedInstance<C>,
        // Incoming instance
        u_i: CommittedInstance<C>,
    ) -> Vec<bool> {
        // NOTICE: This isn't following the order of the HackMD.
        // As long as we match it. We should not have any issues.
        transcript.absorb(&pp_hash);
        transcript.absorb(&U_i);
        transcript.absorb(&u_i);
        transcript.squeeze_bits(NOVA_N_BITS_RO)
    }
}

// Simple auxiliary structure mainly used to help pass a witness for which we can check
// easily an R1CS relation.
// Notice that checking it requires us to have `E` as per [`Arith`] trait definition.
// But since we don't hold `E` nor `e` within the NIFS, we create this structure to pass
// `e` such that the check can be done.
#[derive(Debug, Clone)]
pub(crate) struct TestingWitness<C: CurveGroup> {
    pub(crate) w: Vec<C::ScalarField>,
    pub(crate) e: Vec<C::ScalarField>,
}
