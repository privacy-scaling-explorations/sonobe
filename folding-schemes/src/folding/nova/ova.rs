/// This module contains the implementation the NIFSTrait for the
/// [Ova](https://hackmd.io/V4838nnlRKal9ZiTHiGYzw) NIFS (Non-Interactive Folding Scheme) as
/// outlined in the protocol description doc:
/// <https://hackmd.io/V4838nnlRKal9ZiTHiGYzw#Construction> authored by Benedikt Bünz.
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::fmt::Debug;
use ark_std::rand::RngCore;
use ark_std::{One, UniformRand, Zero};
use std::marker::PhantomData;

use super::{circuits::ChallengeGadget, traits::NIFSTrait};
use crate::arith::r1cs::R1CS;
use crate::commitment::CommitmentScheme;
use crate::folding::{circuits::CF1, traits::Dummy};
use crate::transcript::{AbsorbNonNative, Transcript};
use crate::utils::vec::{hadamard, mat_vec_mul, vec_scalar_mul, vec_sub};
use crate::Error;

/// A CommittedInstance in [Ova](https://hackmd.io/V4838nnlRKal9ZiTHiGYzw) is represented by `W` or
/// `W'`. It is the result of the commitment to a vector that contains the witness `w` concatenated
/// with `t` or `e` + the public inputs `x` and a relaxation factor `u`. (Notice that in the Ova
/// document `u` is denoted as `mu`, in this implementation we use `u` so it follows the original
/// Nova notation, so code is easier to follow).
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommittedInstance<C: CurveGroup> {
    pub u: C::ScalarField, // in the Ova document is denoted as `mu`
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
        self.u.to_sponge_field_elements(dest);
        self.x.to_sponge_field_elements(dest);
        // We cannot call `to_native_sponge_field_elements(dest)` directly, as
        // `to_native_sponge_field_elements` needs `F` to be `C::ScalarField`,
        // but here `F` is a generic `PrimeField`.
        self.cmWE
            .to_native_sponge_field_elements_as_vec()
            .to_sponge_field_elements(dest);
    }
}

// #[allow(dead_code)] // Clippy flag needed for now.
/// A Witness in Ova is represented by `w`. It also contains a blinder which can or not be used
/// when committing to the witness itself.
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

    /// Given `x` (public inputs) and `t` or `e` (which we always concatenate in Ova) and the
    /// public inputs `x`, generates a [`CommittedInstance`] as a result which will or not be
    /// blinded depending on how the const generic `HC` is set up.
    pub fn commit<CS: CommitmentScheme<C, HC>, const HC: bool>(
        &self,
        params: &CS::ProverParams,
        x: Vec<C::ScalarField>,
        t_or_e: Vec<C::ScalarField>,
    ) -> Result<CommittedInstance<C>, Error> {
        let cmWE = CS::commit(params, &[self.w.clone(), t_or_e].concat(), &self.rW)?;
        Ok(CommittedInstance {
            u: C::ScalarField::one(),
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

/// Implements the NIFS (Non-Interactive Folding Scheme) trait for Ova.
pub struct NIFS<C: CurveGroup, CS: CommitmentScheme<C, H>, const H: bool = false> {
    _c: PhantomData<C>,
    _cp: PhantomData<CS>,
}

impl<C: CurveGroup, CS: CommitmentScheme<C, H>, const H: bool> NIFSTrait<C, CS, H>
    for NIFS<C, CS, H>
where
    <C as Group>::ScalarField: Absorb,
    <C as CurveGroup>::BaseField: PrimeField,
{
    type CommittedInstance = CommittedInstance<C>;
    type Witness = Witness<C>;
    type ProverAux = ();
    type VerifierAux = ();

    fn new_witness(w: Vec<C::ScalarField>, _e_len: usize, rng: impl RngCore) -> Self::Witness {
        Witness::new::<H>(w, rng)
    }

    fn new_instance(
        W: &Self::Witness,
        params: &CS::ProverParams,
        x: Vec<C::ScalarField>,
        aux: Vec<C::ScalarField>, // t_or_e
    ) -> Result<Self::CommittedInstance, Error> {
        W.commit::<CS, H>(params, x, aux)
    }

    fn fold_witness(
        r: C::ScalarField, // in Ova's hackmd denoted as `alpha`
        W_i: &Self::Witness,
        w_i: &Self::Witness,
        _aux: &Self::ProverAux,
    ) -> Result<Self::Witness, Error> {
        let w: Vec<C::ScalarField> = W_i
            .w
            .iter()
            .zip(&w_i.w)
            .map(|(a, b)| *a + (r * b))
            .collect();

        let rW = W_i.rW + r * w_i.rW;
        Ok(Self::Witness { w, rW })
    }

    fn compute_aux(
        _cs_prover_params: &CS::ProverParams,
        _r1cs: &R1CS<C::ScalarField>,
        _W_i: &Self::Witness,
        _U_i: &Self::CommittedInstance,
        _w_i: &Self::Witness,
        _u_i: &Self::CommittedInstance,
    ) -> Result<(Self::ProverAux, Self::VerifierAux), Error> {
        Ok(((), ()))
    }

    fn get_challenge<T: Transcript<C::ScalarField>>(
        transcript: &mut T,
        pp_hash: C::ScalarField, // public params hash
        U_i: &Self::CommittedInstance,
        u_i: &Self::CommittedInstance,
        _aux: &Self::VerifierAux,
    ) -> Vec<bool> {
        // reuse Nova's get_challenge method
        ChallengeGadget::<C, Self::CommittedInstance>::get_challenge_native(
            transcript, pp_hash, U_i, u_i, None, // empty in Ova's case
        )
    }

    // Notice: `prove` method is implemented at the trait level.

    fn verify(
        // r comes from the transcript, and is a n-bit (N_BITS_CHALLENGE) element
        r: C::ScalarField,
        U_i: &Self::CommittedInstance,
        u_i: &Self::CommittedInstance,
        _aux: &Self::VerifierAux,
    ) -> Self::CommittedInstance {
        // recall that r <==> alpha, and u <==> mu between Nova and Ova respectively
        let u = U_i.u + r; // u_i.u is always 1 IN ova as we just can do sequential IVC.
        let cmWE = U_i.cmWE + u_i.cmWE.mul(r);
        let x = U_i
            .x
            .iter()
            .zip(&u_i.x)
            .map(|(a, b)| *a + (r * b))
            .collect::<Vec<C::ScalarField>>();

        Self::CommittedInstance { cmWE, u, x }
    }
}

/// Computes the E parameter (error terms) for the given R1CS and the instance's z and u. This
/// method is used by the verifier to obtain E in order to check the RelaxedR1CS relation.
pub fn compute_E<C: CurveGroup>(
    r1cs: &R1CS<C::ScalarField>,
    z: &[C::ScalarField],
    u: C::ScalarField,
) -> Result<Vec<C::ScalarField>, Error> {
    let (A, B, C) = (r1cs.A.clone(), r1cs.B.clone(), r1cs.C.clone());

    // this is parallelizable (for the future)
    let Az = mat_vec_mul(&A, z)?;
    let Bz = mat_vec_mul(&B, z)?;
    let Cz = mat_vec_mul(&C, z)?;

    let Az_Bz = hadamard(&Az, &Bz)?;
    let uCz = vec_scalar_mul(&Cz, &u);

    vec_sub(&Az_Bz, &uCz)
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_pallas::{Fr, Projective};

    use crate::arith::{r1cs::tests::get_test_r1cs, Arith};
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::nifs::tests::test_nifs_opt;

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
    impl<C: CurveGroup> Arith<TestingWitness<C>, CommittedInstance<C>> for R1CS<CF1<C>> {
        type Evaluation = Vec<CF1<C>>;

        fn eval_relation(
            &self,
            w: &TestingWitness<C>,
            u: &CommittedInstance<C>,
        ) -> Result<Self::Evaluation, Error> {
            self.eval_at_z(&[&[u.u], u.x.as_slice(), &w.w].concat())
        }

        fn check_evaluation(
            w: &TestingWitness<C>,
            _u: &CommittedInstance<C>,
            e: Self::Evaluation,
        ) -> Result<(), Error> {
            (w.e == e).then_some(()).ok_or(Error::NotSatisfied)
        }
    }

    #[test]
    fn test_nifs_ova() {
        let (W, U) = test_nifs_opt::<NIFS<Projective, Pedersen<Projective>>>();

        // check the last folded instance relation
        let r1cs = get_test_r1cs();
        let z: Vec<Fr> = [&[U.u][..], &U.x, &W.w].concat();
        let e = compute_E::<Projective>(&r1cs, &z, U.u).unwrap();
        r1cs.check_relation(&TestingWitness::<Projective> { e, w: W.w.clone() }, &U)
            .unwrap();
    }
}
