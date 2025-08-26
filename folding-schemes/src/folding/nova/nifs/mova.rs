/// This module contains the implementation the NIFSTrait for the
/// [Mova](https://eprint.iacr.org/2024/1220.pdf) NIFS (Non-Interactive Folding Scheme).
use ark_crypto_primitives::sponge::Absorb;
use ark_ff::PrimeField;
use ark_poly::Polynomial;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{log2, marker::PhantomData, rand::RngCore, One, UniformRand, Zero};

use super::{
    nova::NIFS as NovaNIFS,
    pointvsline::{PointVsLine, PointVsLineProof, PointvsLineEvaluationClaim},
    NIFSTrait,
};
use crate::arith::{r1cs::R1CS, Arith, ArithRelation};
use crate::commitment::CommitmentScheme;
use crate::folding::circuits::CF1;
use crate::folding::traits::Dummy;
use crate::transcript::Transcript;
use crate::utils::{
    mle::dense_vec_to_dense_mle,
    vec::{is_zero_vec, vec_add, vec_scalar_mul},
};
use crate::{Curve, Error};

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommittedInstance<C: Curve> {
    // Random evaluation point for the E
    pub rE: Vec<C::ScalarField>,
    // mleE is the evaluation of the MLE of E at r_E
    pub mleE: C::ScalarField,
    pub u: C::ScalarField,
    pub cmW: C,
    pub x: Vec<C::ScalarField>,
}

impl<C: Curve> Absorb for CommittedInstance<C> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        C::ScalarField::batch_to_sponge_bytes(&self.to_sponge_field_elements_as_vec(), dest);
    }

    fn to_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        self.u.to_sponge_field_elements(dest);
        self.x.to_sponge_field_elements(dest);
        self.rE.to_sponge_field_elements(dest);
        self.mleE.to_sponge_field_elements(dest);
        self.cmW.to_native_sponge_field_elements(dest);
    }
}

impl<C: Curve> Dummy<usize> for CommittedInstance<C> {
    fn dummy(io_len: usize) -> Self {
        Self {
            rE: vec![C::ScalarField::zero(); io_len],
            mleE: C::ScalarField::zero(),
            u: C::ScalarField::zero(),
            cmW: C::zero(),
            x: vec![C::ScalarField::zero(); io_len],
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Witness<C: Curve> {
    pub E: Vec<C::ScalarField>,
    pub W: Vec<C::ScalarField>,
    pub rW: C::ScalarField,
}

impl<C: Curve> Dummy<&R1CS<C::ScalarField>> for Witness<C> {
    fn dummy(r1cs: &R1CS<C::ScalarField>) -> Self {
        Self {
            E: vec![C::ScalarField::zero(); r1cs.n_constraints()],
            W: vec![C::ScalarField::zero(); r1cs.n_witnesses()],
            rW: C::ScalarField::zero(),
        }
    }
}

impl<C: Curve> Witness<C> {
    pub fn new<const H: bool>(w: Vec<C::ScalarField>, e_len: usize, mut rng: impl RngCore) -> Self {
        let rW = if H {
            C::ScalarField::rand(&mut rng)
        } else {
            C::ScalarField::zero()
        };

        Self {
            E: vec![C::ScalarField::zero(); e_len],
            W: w,
            rW,
        }
    }

    pub fn commit<CS: CommitmentScheme<C, H>, const H: bool>(
        &self,
        params: &CS::ProverParams,
        x: Vec<C::ScalarField>,
        rE: Vec<C::ScalarField>,
    ) -> Result<CommittedInstance<C>, Error> {
        let mut mleE = C::ScalarField::zero();
        if !is_zero_vec::<C::ScalarField>(&self.E) {
            let E = dense_vec_to_dense_mle(log2(self.E.len()) as usize, &self.E);
            mleE = E.evaluate(&rE);
        }
        let cmW = CS::commit(params, &self.W, &self.rW)?;
        Ok(CommittedInstance {
            rE,
            mleE,
            u: C::ScalarField::one(),
            cmW,
            x,
        })
    }
}

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<C: Curve> {
    pub h_proof: PointVsLineProof<C>,
    pub mleE1_prime: C::ScalarField,
    pub mleE2_prime: C::ScalarField,
    pub mleT: C::ScalarField,
    pub rE_prime: Vec<C::ScalarField>,
}

/// Implements the Non-Interactive Folding Scheme described in section 4 of
/// [Mova](https://eprint.iacr.org/2024/1220.pdf).
/// `H` specifies whether the NIFS will use a blinding factor
pub struct NIFS<
    C: Curve,
    CS: CommitmentScheme<C, H>,
    T: Transcript<C::ScalarField>,
    const H: bool = false,
> {
    _c: PhantomData<C>,
    _cp: PhantomData<CS>,
    _ct: PhantomData<T>,
}

impl<C: Curve, CS: CommitmentScheme<C, H>, T: Transcript<C::ScalarField>, const H: bool>
    NIFSTrait<C, CS, T, H> for NIFS<C, CS, T, H>
{
    type CommittedInstance = CommittedInstance<C>;
    type Witness = Witness<C>;
    type ProverAux = Vec<C::ScalarField>; // T in Mova's notation
    type Proof = Proof<C>;

    fn new_witness(w: Vec<C::ScalarField>, e_len: usize, rng: impl RngCore) -> Self::Witness {
        Witness::new::<H>(w, e_len, rng)
    }

    fn new_instance(
        mut rng: impl RngCore,
        params: &CS::ProverParams,
        W: &Self::Witness,
        x: Vec<C::ScalarField>,
        aux: Vec<C::ScalarField>, // = r_E
    ) -> Result<Self::CommittedInstance, Error> {
        let mut rE = aux.clone();
        if is_zero_vec(&rE) {
            // means that we're in a fresh instance, so generate random value
            rE = (0..log2(W.E.len()))
                .map(|_| C::ScalarField::rand(&mut rng))
                .collect();
        }

        W.commit::<CS, H>(params, x, rE)
    }

    // Protocol 7 - point 3 (16)
    fn fold_witness(
        a: C::ScalarField,
        W_i: &Witness<C>,
        w_i: &Witness<C>,
        aux: &Vec<C::ScalarField>, // T in Mova's notation
    ) -> Result<Witness<C>, Error> {
        let a2 = a * a;
        let E: Vec<C::ScalarField> = vec_add(
            &vec_add(&W_i.E, &vec_scalar_mul(aux, &a))?,
            &vec_scalar_mul(&w_i.E, &a2),
        )?;
        let W: Vec<C::ScalarField> = W_i
            .W
            .iter()
            .zip(&w_i.W)
            .map(|(i1, i2)| *i1 + (a * i2))
            .collect();

        let rW = W_i.rW + a * w_i.rW;
        Ok(Witness::<C> { E, W, rW })
    }

    /// [Mova](https://eprint.iacr.org/2024/1220.pdf)'s section 4. Protocol 8
    /// Returns a proof for the pt-vs-line operations along with the folded committed instance
    /// instances and witness
    #[allow(clippy::type_complexity)]
    fn prove(
        _cs_prover_params: &CS::ProverParams, // not used in Mova since we don't commit to T
        r1cs: &R1CS<C::ScalarField>,
        transcript: &mut T,
        W_i: &Witness<C>,
        U_i: &CommittedInstance<C>,
        w_i: &Witness<C>,
        u_i: &CommittedInstance<C>,
    ) -> Result<
        (
            Self::Witness,
            Self::CommittedInstance,
            Self::Proof,
            Vec<bool>,
        ),
        Error,
    > {
        // Protocol 5 is pre-processing
        transcript.absorb(U_i);
        transcript.absorb(u_i);

        // Protocol 6
        let (
            h_proof,
            PointvsLineEvaluationClaim {
                mleE1_prime,
                mleE2_prime,
                rE_prime,
            },
        ) = PointVsLine::<C, T>::prove(transcript, U_i, u_i, W_i, w_i)?;

        // Protocol 7

        transcript.absorb(&mleE1_prime);
        transcript.absorb(&mleE2_prime);

        // compute the cross terms
        let z1: Vec<C::ScalarField> = [vec![U_i.u], U_i.x.to_vec(), W_i.W.to_vec()].concat();
        let z2: Vec<C::ScalarField> = [vec![u_i.u], u_i.x.to_vec(), w_i.W.to_vec()].concat();
        let T = NovaNIFS::<C, CS, T, H>::compute_T(r1cs, U_i.u, u_i.u, &z1, &z2, &W_i.E, &w_i.E)?;

        let n_vars: usize = log2(W_i.E.len()) as usize;
        if log2(T.len()) as usize != n_vars {
            return Err(Error::NotExpectedLength(T.len(), n_vars));
        }

        let mleT = dense_vec_to_dense_mle(n_vars, &T);
        let mleT_evaluated = mleT.evaluate(&rE_prime);

        transcript.absorb(&mleT_evaluated);

        let alpha: C::ScalarField = transcript.get_challenge();

        let ci = Self::fold_committed_instance(
            alpha,
            U_i,
            u_i,
            &rE_prime,
            &mleE1_prime,
            &mleE2_prime,
            &mleT_evaluated,
        )?;
        let w = Self::fold_witness(alpha, W_i, w_i, &T)?;

        let proof = Self::Proof {
            h_proof,
            mleE1_prime,
            mleE2_prime,
            mleT: mleT_evaluated,
            rE_prime,
        };
        Ok((
            w,
            ci,
            proof,
            vec![], // r_bits, returned to be passed as inputs to the circuit, not used at the
                    // current impl status
        ))
    }

    /// [Mova](https://eprint.iacr.org/2024/1220.pdf)'s section 4. It verifies the results from the proof
    /// Both the folding and the pt-vs-line proof
    /// returns the folded committed instance
    fn verify(
        transcript: &mut T,
        U_i: &CommittedInstance<C>,
        u_i: &CommittedInstance<C>,
        proof: &Proof<C>,
    ) -> Result<(Self::CommittedInstance, Vec<bool>), Error> {
        transcript.absorb(U_i);
        transcript.absorb(u_i);
        let rE_prime = PointVsLine::<C, T>::verify(
            transcript,
            U_i,
            u_i,
            &proof.h_proof,
            &proof.mleE1_prime,
            &proof.mleE2_prime,
            &proof.rE_prime,
        )?;

        transcript.absorb(&proof.mleE1_prime);
        transcript.absorb(&proof.mleE2_prime);
        transcript.absorb(&proof.mleT);

        let alpha: C::ScalarField = transcript.get_challenge();

        Ok((
            Self::fold_committed_instance(
                alpha,
                U_i,
                u_i,
                &rE_prime,
                &proof.mleE1_prime,
                &proof.mleE2_prime,
                &proof.mleT,
            )?,
            vec![],
        ))
    }
}

impl<C: Curve, CS: CommitmentScheme<C, H>, T: Transcript<C::ScalarField>, const H: bool>
    NIFS<C, CS, T, H>
{
    // Protocol 7 - point 3 (15)
    fn fold_committed_instance(
        a: C::ScalarField,
        U_i: &CommittedInstance<C>,
        u_i: &CommittedInstance<C>,
        rE_prime: &[C::ScalarField],
        mleE1_prime: &C::ScalarField,
        mleE2_prime: &C::ScalarField,
        mleT: &C::ScalarField,
    ) -> Result<CommittedInstance<C>, Error> {
        let a2 = a * a;
        let mleE = *mleE1_prime + a * mleT + a2 * mleE2_prime;
        let u = U_i.u + a * u_i.u;
        let cmW = U_i.cmW + u_i.cmW.mul(a);
        let x = U_i
            .x
            .iter()
            .zip(&u_i.x)
            .map(|(i1, i2)| *i1 + (a * i2))
            .collect::<Vec<C::ScalarField>>();

        Ok(CommittedInstance::<C> {
            rE: rE_prime.to_vec(),
            mleE,
            u,
            cmW,
            x,
        })
    }
}

impl<C: Curve> ArithRelation<Witness<C>, CommittedInstance<C>> for R1CS<CF1<C>> {
    type Evaluation = Vec<CF1<C>>;

    fn eval_relation(
        &self,
        w: &Witness<C>,
        u: &CommittedInstance<C>,
    ) -> Result<Self::Evaluation, Error> {
        self.eval_at_z(&[&[u.u][..], &u.x, &w.W].concat())
    }

    fn check_evaluation(
        w: &Witness<C>,
        _u: &CommittedInstance<C>,
        e: Self::Evaluation,
    ) -> Result<(), Error> {
        (w.E == e).then_some(()).ok_or(Error::NotSatisfied)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use ark_pallas::{Fr, Projective};

    use crate::arith::{r1cs::tests::get_test_r1cs, ArithRelation};
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::nifs::tests::test_nifs_opt;

    #[test]
    fn test_nifs_mova() -> Result<(), Error> {
        let (W, U) = test_nifs_opt::<NIFS<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>>()?;

        // check the last folded instance relation
        let r1cs = get_test_r1cs();
        r1cs.check_relation(&W, &U)?;
        Ok(())
    }
}
