/// This module contains the implementation the NIFSTrait for the
/// [Ova](https://hackmd.io/V4838nnlRKal9ZiTHiGYzw) NIFS (Non-Interactive Folding Scheme).
use ark_crypto_primitives::sponge::Absorb;
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::fmt::Debug;
use ark_std::rand::RngCore;
use ark_std::{One, UniformRand, Zero};
use std::marker::PhantomData;

use super::nova::ChallengeGadget;
use super::ova_circuits::CommittedInstanceVar;
use super::NIFSTrait;
use crate::arith::{r1cs::R1CS, Arith};
use crate::commitment::CommitmentScheme;
use crate::folding::traits::{CommittedInstanceOps, Inputize};
use crate::folding::{circuits::CF1, traits::Dummy};
use crate::transcript::Transcript;
use crate::utils::vec::{hadamard, mat_vec_mul, vec_scalar_mul, vec_sub};
use crate::{Curve, Error};

/// A CommittedInstance in [Ova](https://hackmd.io/V4838nnlRKal9ZiTHiGYzw) is represented by `W` or
/// `W'`. It is the result of the commitment to a vector that contains the witness `w` concatenated
/// with `t` or `e` + the public inputs `x` and a relaxation factor `u`. (Notice that in the Ova
/// document `u` is denoted as `mu`, in this implementation we use `u` so it follows the original
/// Nova notation, so code is easier to follow).
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommittedInstance<C: Curve> {
    pub u: C::ScalarField, // in the Ova document is denoted as `mu`
    pub x: Vec<C::ScalarField>,
    pub cmWE: C,
}

impl<C: Curve> Absorb for CommittedInstance<C> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        C::ScalarField::batch_to_sponge_bytes(&self.to_sponge_field_elements_as_vec(), dest);
    }

    fn to_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        self.u.to_sponge_field_elements(dest);
        self.x.to_sponge_field_elements(dest);
        self.cmWE.to_native_sponge_field_elements(dest);
    }
}

impl<C: Curve> CommittedInstanceOps<C> for CommittedInstance<C> {
    type Var = CommittedInstanceVar<C>;

    fn get_commitments(&self) -> Vec<C> {
        vec![self.cmWE]
    }

    fn is_incoming(&self) -> bool {
        self.u == One::one()
    }
}

impl<C: Curve> Inputize<CF1<C>> for CommittedInstance<C> {
    /// Returns the internal representation in the same order as how the value
    /// is allocated in `CommittedInstanceVar::new_input`.
    fn inputize(&self) -> Vec<CF1<C>> {
        [&[self.u][..], &self.x, &self.cmWE.inputize_nonnative()].concat()
    }
}

/// A Witness in Ova is represented by `w`. It also contains a blinder which can or not be used
/// when committing to the witness itself.
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Witness<C: Curve> {
    pub w: Vec<C::ScalarField>,
    pub rW: C::ScalarField,
}

impl<C: Curve> Witness<C> {
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

impl<C: Curve> Dummy<&R1CS<CF1<C>>> for Witness<C> {
    fn dummy(r1cs: &R1CS<CF1<C>>) -> Self {
        Self {
            w: vec![C::ScalarField::zero(); r1cs.n_witnesses()],
            rW: C::ScalarField::zero(),
        }
    }
}

/// Implements the NIFS (Non-Interactive Folding Scheme) trait for Ova.
pub struct NIFS<
    C: Curve,
    CS: CommitmentScheme<C, H>,
    T: Transcript<C::ScalarField>,
    const H: bool = false,
> {
    _c: PhantomData<C>,
    _cp: PhantomData<CS>,
    _t: PhantomData<T>,
}

impl<C: Curve, CS: CommitmentScheme<C, H>, T: Transcript<C::ScalarField>, const H: bool>
    NIFSTrait<C, CS, T, H> for NIFS<C, CS, T, H>
{
    type CommittedInstance = CommittedInstance<C>;
    type Witness = Witness<C>;
    type ProverAux = ();
    // Proof is unused, but set to C::ScalarField so that the NIFSGadgetTrait abstraction can
    // define the ProofsVar implementing the AllocVar from Proof
    type Proof = C::ScalarField;

    fn new_witness(w: Vec<C::ScalarField>, _e_len: usize, rng: impl RngCore) -> Self::Witness {
        Witness::new::<H>(w, rng)
    }

    fn new_instance(
        _rng: impl RngCore,
        params: &CS::ProverParams,
        W: &Self::Witness,
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

    fn prove(
        _cs_prover_params: &CS::ProverParams,
        _r1cs: &R1CS<C::ScalarField>,
        transcript: &mut T,
        W_i: &Self::Witness,
        U_i: &Self::CommittedInstance,
        w_i: &Self::Witness,
        u_i: &Self::CommittedInstance,
    ) -> Result<
        (
            Self::Witness,
            Self::CommittedInstance,
            Self::Proof,
            Vec<bool>,
        ),
        Error,
    > {
        let mut transcript_v = transcript.clone();

        let r_bits = ChallengeGadget::<C, Self::CommittedInstance>::get_challenge_native(
            transcript, U_i, u_i, None, // cmT not used in Ova
        );
        let r_Fr = C::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits))
            .ok_or(Error::OutOfBounds)?;

        let w = Self::fold_witness(r_Fr, W_i, w_i, &())?;

        let proof = C::ScalarField::zero();
        let (ci, _r_bits_v) = Self::verify(&mut transcript_v, U_i, u_i, &proof)?;
        #[cfg(test)]
        assert_eq!(_r_bits_v, r_bits);

        Ok((w, ci, proof, r_bits))
    }

    fn verify(
        transcript: &mut T,
        U_i: &Self::CommittedInstance,
        u_i: &Self::CommittedInstance,
        _proof: &Self::Proof, // unused in Ova
    ) -> Result<(Self::CommittedInstance, Vec<bool>), Error> {
        let r_bits = ChallengeGadget::<C, Self::CommittedInstance>::get_challenge_native(
            transcript, U_i, u_i, None, // cmT not used in Ova
        );
        let r = C::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits))
            .ok_or(Error::OutOfBounds)?;

        // recall that r=alpha, and u=mu between Nova and Ova respectively
        let u = U_i.u + r; // u_i.u is always 1 in Ova as we just can do IVC (not PCD).
        let cmWE = U_i.cmWE + u_i.cmWE.mul(r);
        let x = U_i
            .x
            .iter()
            .zip(&u_i.x)
            .map(|(a, b)| *a + (r * b))
            .collect::<Vec<C::ScalarField>>();

        Ok((Self::CommittedInstance { cmWE, u, x }, r_bits))
    }
}

/// Computes the E parameter (error terms) for the given R1CS and the instance's z and u. This
/// method is used by the verifier to obtain E in order to check the RelaxedR1CS relation.
pub fn compute_E<C: Curve>(
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

    use crate::arith::{r1cs::tests::get_test_r1cs, ArithRelation};
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::nifs::tests::test_nifs_opt;
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;

    // Simple auxiliary structure mainly used to help pass a witness for which we can check
    // easily an R1CS relation.
    // Notice that checking it requires us to have `E` as per [`ArithRelation`] trait definition.
    // But since we don't hold `E` nor `e` within the NIFS, we create this structure to pass
    // `e` such that the check can be done.
    #[derive(Debug, Clone)]
    pub(crate) struct TestingWitness<C: Curve> {
        pub(crate) w: Vec<C::ScalarField>,
        pub(crate) e: Vec<C::ScalarField>,
    }
    impl<C: Curve> ArithRelation<TestingWitness<C>, CommittedInstance<C>> for R1CS<CF1<C>> {
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
    fn test_nifs_ova() -> Result<(), Error> {
        let (W, U) = test_nifs_opt::<NIFS<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>>()?;

        // check the last folded instance relation
        let r1cs = get_test_r1cs();
        let z: Vec<Fr> = [&[U.u][..], &U.x, &W.w].concat();
        let e = compute_E::<Projective>(&r1cs, &z, U.u)?;
        r1cs.check_relation(&TestingWitness::<Projective> { e, w: W.w.clone() }, &U)?;
        Ok(())
    }
}
