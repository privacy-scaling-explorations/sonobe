use std::marker::PhantomData;
use ark_crypto_primitives::sponge::Absorb;
use ark_ff::PrimeField;
use ark_poly::Polynomial;
/// Mova-like folding for matrix multiplications as desbribed in !todo(add reference to paper if public)
// !todo(Add blinding factor to suport hiding property).

use ark_serialize::CanonicalSerialize;
use ark_std::log2;
use ark_std::rand::RngCore;
use crate::commitment::CommitmentScheme;
use crate::{Curve, Error};
use crate::arith::r1cs::R1CS;
use crate::folding::nova::nifs::NIFSTrait;
use crate::folding::nova::nifs::pointvsline::{PointVsLine, PointVsLineProof, PointvsLineEvaluationClaim};
use crate::folding::traits::Dummy;
use crate::transcript::Transcript;
use crate::utils::mle::dense_vec_to_dense_mle;

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize)]
pub struct RelaxedCommitedRelation<C: Curve> {
    com_a: C,
    com_b: C,
    com_c: C,
    u: C::ScalarField,
    v: C::ScalarField,
    r: Vec<C::ScalarField>,
}

impl<C: Curve> Absorb for RelaxedCommitedRelation<C> {
    fn to_sponge_bytes(&self, _dest: &mut Vec<u8>) {
        // This is never called
        unimplemented!()
    }

    fn to_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        self.com_a.to_native_sponge_field_elements(dest);
        self.com_b.to_native_sponge_field_elements(dest);
        self.com_c.to_native_sponge_field_elements(dest);
        self.u.to_sponge_field_elements(dest);
        self.v.to_sponge_field_elements(dest);
        self.r.to_sponge_field_elements(dest);
    }
}

impl<C: Curve> Dummy<usize> for RelaxedCommitedRelation<C> {
    fn dummy(log_n: usize) -> Self {
        Self {
            com_a: C::zero(),
            com_b: C::zero(),
            com_c: C::zero(),
            u: C::ScalarField::zero(),
            v: C::ScalarField::zero(),
            r: vec![C::ScalarField::zero(); 2 * log_n],
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Witness<C: Curve> {
    pub A: Vec<C::ScalarField>,
    pub B: Vec<C::ScalarField>,
    pub C: Vec<C::ScalarField>,
    pub E: Vec<C::ScalarField>,
}

impl<C: Curve> Witness<C> {
    pub fn new<const H: bool>(a: Vec<C::ScalarField>, b: Vec<C::ScalarField>, c: Vec<C::ScalarField>, e: Vec<C::ScalarField>) -> Self {
        Self {
            A: a,
            B: b,
            C: c,
            E: e
        }
    }

    pub fn commit<CS: CommitmentScheme<C, H>, const H: bool>(
        &self,
        params: &CS::ProverParams,
        log_n: usize,
    ) -> Result<RelaxedCommitedRelation<C>, Error> {
        // todo!("Right now we are ignoring the hiding property")
        let com_a = CS::commit(params, &self.A, &C::ScalarField::zero())?;
        let com_b = CS::commit(params, &self.B, &C::ScalarField::zero())?;
        let com_c = CS::commit(params, &self.C, &C::ScalarField::zero())?;

        // todo!("Check if this is the right place for generating r");
        Ok(RelaxedCommitedRelation {
            com_a,
            com_b,
            com_c,
            u: C::ScalarField::one(),
            v: C::ScalarField::one(),
            r: vec![C::ScalarField::zero(); 2 * log_n],
        })
    }
}

// todo!("Review and update proof fields")
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Proof<C: Curve> {
    pub h_proof: PointVsLineProof<C>,
    pub mleE2_prime: C::ScalarField,
    pub mleT: C::ScalarField,
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
    type CommittedInstance = RelaxedCommitedRelation<C>;
    type Witness = Witness<C>;
    type ProverAux = Vec<C::ScalarField>; // T in Mova's notation
    type Proof = Proof<C>;

    // Right now we are packing the 4 matrices in a single vector to achieve compatibility with NIFStrait.
    fn new_witness(abce: Vec<C::ScalarField>, e_len: usize, rng: impl RngCore) -> Self::Witness {
        assert_eq!(abce.len() % 4, 0); // Check for proper length.
        let chunk_size = e_len / 4;
        let mut iter = abce.into_iter();

        let a: Vec<C::ScalarField> = iter.by_ref().take(chunk_size).collect();
        let b: Vec<C::ScalarField> = iter.by_ref().take(chunk_size).collect();
        let c: Vec<C::ScalarField> = iter.by_ref().take(chunk_size).collect();
        let e: Vec<C::ScalarField> = iter.collect();
        Witness::new::<H>(a, b, c, e)
    }

    fn new_instance(
        mut rng: impl RngCore,
        params: &CS::ProverParams,
        W: &Self::Witness,
        x: Vec<C::ScalarField>,
        aux: Vec<C::ScalarField>, // = r_E
    ) -> Result<Self::CommittedInstance, Error> {
        todo!("To be implemented");
    }

    // Protocol 5 - point 8 (Page 25)
    fn fold_witness(
        alpha: C::ScalarField,
        sparse_wit: &Witness<C>,
        acc_wit: &Witness<C>,
        aux: &Vec<C::ScalarField>, // T in Mova's notation
    ) -> Result<Witness<C>, Error> {
        let a_acc = alpha * &sparse_wit.A + &acc_wit.A;
        let b_acc = alpha * &sparse_wit.B + &acc_wit.B;
        let c_acc = alpha * &sparse_wit.C + &acc_wit.C;
        let e_acc = &acc_wit.E + alpha * aux;

        Ok(Witness::<C> {
            A: a_acc,
            B: b_acc,
            C: c_acc,
            E: e_acc
        })
    }

    /// [Mova](https://eprint.iacr.org/2024/1220.pdf)'s section 4. Protocol 8
    /// Returns a proof for the pt-vs-line operations along with the folded committed instance
    /// instances and witness
    #[allow(clippy::type_complexity)]
    fn prove(
        _cs_prover_params: &CS::ProverParams, // not used in Mova since we don't commit to T
        r1cs: &R1CS<C::ScalarField>,
        transcript: &mut T,
        pp_hash: C::ScalarField,
        W_i: &Witness<C>,
        U_i: &RelaxedCommitedRelation<C>,
        w_i: &Witness<C>,
        u_i: &RelaxedCommitedRelation<C>,
    ) -> Result<
        (
            Self::Witness,
            Self::CommittedInstance,
            Self::Proof,
            Vec<bool>,
        ),
        Error,
    > {
        todo!("To be updated");

        /*
        transcript.absorb(&pp_hash);
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
        };
        Ok((
            w,
            ci,
            proof,
            vec![], // r_bits, returned to be passed as inputs to the circuit, not used at the
            // current impl status
        ))*/
    }

    /// [Mova](https://eprint.iacr.org/2024/1220.pdf)'s section 4. It verifies the results from the proof
    /// Both the folding and the pt-vs-line proof
    /// returns the folded committed instance
    fn verify(
        transcript: &mut T,
        pp_hash: C::ScalarField,
        U_i: &RelaxedCommitedRelation<C>,
        u_i: &RelaxedCommitedRelation<C>,
        proof: &Proof<C>,
    ) -> Result<(Self::CommittedInstance, Vec<bool>), Error> {
        transcript.absorb(&pp_hash);
        transcript.absorb(U_i);
        transcript.absorb(u_i);
        let rE_prime = PointVsLine::<C, T>::verify(
            transcript,
            U_i,
            u_i,
            &proof.h_proof,
            &proof.mleE2_prime, // todo!("Update verify method")
            &proof.mleE2_prime,
        )?;

        transcript.absorb(&proof.mleE2_prime);
        transcript.absorb(&proof.mleT);

        let alpha: C::ScalarField = transcript.get_challenge();

        Ok((
            Self::fold_committed_instance(
                alpha,
                U_i,
                u_i,
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
    // Protocol 5 - Step 7 (page 25)
    // todo!("Make sure sparse multiplications are optimized")
    fn fold_committed_instance(
        alpha: C::ScalarField,
        sparse_instance: &RelaxedCommitedRelation<C>,
        acc_instance: &RelaxedCommitedRelation<C>,
        mleE2_prime: &C::ScalarField, // v' in Protocol 5
        mleT: &C::ScalarField,
    ) -> Result<RelaxedCommitedRelation<C>, Error> {
        // Step 7
        // Accumulate commitments
        let com_a_acc = alpha * sparse_instance.com_a + acc_instance.com_a;
        let com_b_acc = alpha * sparse_instance.com_b + acc_instance.com_b;
        let com_c_acc = alpha * sparse_instance.com_c + acc_instance.com_c;

        // Update scalars
        let u_acc = alpha + acc_instance.u;
        let v_acc = mleE2_prime + alpha * mleT;


        Ok(RelaxedCommitedRelation::<C> {
            com_a: com_a_acc,
            com_b: com_b_acc,
            com_c: com_c_acc,
            u: u_acc,
            v: v_acc,
            r: acc_instance.r.clone(), // todo!("Check is this is correct. I believe we can get rid off r from the relation def.")
        })
    }
}