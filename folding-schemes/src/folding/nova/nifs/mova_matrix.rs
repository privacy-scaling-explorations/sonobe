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
use crate::utils::vec::{is_zero_vec, mat_vec_mul, mat_vec_mul_dense};
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize)]
pub struct RelaxedCommitedRelation<C: Curve> {
    com_a: C,
    com_b: C,
    com_c: C,
    u: C::ScalarField,
    v: C::ScalarField,
    r: Vec<C::ScalarField>,
    mleE: C::ScalarField,
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
        self.mleE.to_sponge_field_elements(dest);
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
            mleE: C::ScalarField::zero(),
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
        rE: Vec<C::ScalarField>,
    ) -> Result<RelaxedCommitedRelation<C>, Error> {
        let mut mleE = C::ScalarField::zero();
        if !is_zero_vec::<C::ScalarField>(&self.E) {
            let E = dense_vec_to_dense_mle(log2(self.E.len()) as usize, &self.E);
            mleE = E.evaluate(&rE);
        }

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
            r: rE,
            mleE,
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
        witness: &Self::Witness,
        x: Vec<C::ScalarField>,
        aux: Vec<C::ScalarField>, // = r_E
    ) -> Result<Self::CommittedInstance, Error> {
        let mut rE = aux.clone();
        if is_zero_vec(&rE) {
            // means that we're in a fresh instance, so generate random value
            rE = (0..2 * log2(witness.E.len()))
                .map(|_| C::ScalarField::rand(&mut rng))
                .collect();
        }
        witness.commit(params, rE)

    }

    // Protocol 5 - point 8 (Page 25)
    fn fold_witness(
        alpha: C::ScalarField,
        simple_wit: &Witness<C>,
        acc_wit: &Witness<C>,
        aux: &Vec<C::ScalarField>, // T in Mova's notation
    ) -> Result<Witness<C>, Error> {
        let a_acc = alpha * &simple_wit.A + &acc_wit.A;
        let b_acc = alpha * &simple_wit.B + &acc_wit.B;
        let c_acc = alpha * &simple_wit.C + &acc_wit.C;
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
        simple_witness: &Witness<C>,
        simple_instance: &RelaxedCommitedRelation<C>,
        acc_witness: &Witness<C>,
        acc_instance: &RelaxedCommitedRelation<C>,
    ) -> Result<
        (
            Self::Witness,
            Self::CommittedInstance,
            Self::Proof,
            Vec<bool>,
        ),
        Error,
    > {

        transcript.absorb(&pp_hash);
        transcript.absorb(simple_instance);
        transcript.absorb(acc_instance);

        // Protocol 5 - Steps 2-3
        let (
            h_proof,
            PointvsLineEvaluationClaim {
                mleE1_prime, // todo!("Needs to be removed when the new protocol is done")
                mleE2_prime,
                rE_prime,
            },
        ) = PointVsLine::<C, T>::prove(transcript, simple_instance, acc_instance, simple_witness, acc_witness)?;

        transcript.absorb(&mleE2_prime);

        // compute the Cross Term
        let T: Vec<C::ScalarField> = {
            // todo!("Change to sparse Matrices. Review witness types")
            let a1b2: Vec<C::ScalarField> = mat_vec_mul_dense(&simple_witness.A, &acc_witness.B)?;
            let a2b1: Vec<C::ScalarField> = mat_vec_mul_dense(&acc_witness.A, &simple_witness.B)?;
            let u2c1: Vec<C::ScalarField> = mat_vec_mul_dense(&acc_instance.u, &simple_witness.C)?;
            a1b2 + a2b1 - u2c1 - &acc_witness.C
        };

        // Compute MLE_T
        let n_vars: usize = log2(simple_witness.E.len()) as usize;
        if log2(T.len()) as usize != n_vars {
            return Err(Error::NotExpectedLength(T.len(), n_vars));
        }

        let mleT = dense_vec_to_dense_mle(n_vars, &T);
        let mleT_evaluated = mleT.evaluate(&rE_prime);

        // Derive alpha
        transcript.absorb(&mleT_evaluated);
        let alpha: C::ScalarField = transcript.get_challenge();

        let ci = Self::fold_committed_instance(
            alpha,
            simple_witness,
            acc_instance,
            &rE_prime,
            &mleE2_prime,
            &mleT_evaluated,
        )?;
        let w = Self::fold_witness(alpha, simple_witness, acc_witness, &T)?;

        // todo!(Review when new Pointvsline protocol is ready)
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
        ))
    }

    /// [Mova](https://eprint.iacr.org/2024/1220.pdf)'s section 4. It verifies the results from the proof
    /// Both the folding and the pt-vs-line proof
    /// returns the folded committed instance
    fn verify(
        transcript: &mut T,
        pp_hash: C::ScalarField,
        simple_instance: &RelaxedCommitedRelation<C>,
        acc_instance: &RelaxedCommitedRelation<C>,
        proof: &Proof<C>,
    ) -> Result<(Self::CommittedInstance, Vec<bool>), Error> {

        transcript.absorb(&pp_hash);
        transcript.absorb(simple_instance);
        transcript.absorb(acc_instance);

        // Verify rE_prime
        let rE_prime = PointVsLine::<C, T>::verify(
            transcript,
            simple_instance,
            acc_instance,
            &proof.h_proof,
            &proof.mleE2_prime, // todo!("Update verify method")
            &proof.mleE2_prime,
        )?;

        // Derive alpha
        transcript.absorb(&proof.mleE2_prime);
        transcript.absorb(&proof.mleT);
        let alpha: C::ScalarField = transcript.get_challenge();

        Ok((
            Self::fold_committed_instance(
                alpha,
                simple_instance,
                acc_instance,
                &rE_prime,
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
        simple_instance: &RelaxedCommitedRelation<C>,
        acc_instance: &RelaxedCommitedRelation<C>,
        rE_prime: &[C::ScalarField],
        mleE2_prime: &C::ScalarField, // v' in Protocol 5
        mleT: &C::ScalarField,
    ) -> Result<RelaxedCommitedRelation<C>, Error> {
        // Step 7
        // Accumulate commitments
        let com_a_acc = alpha * simple_instance.com_a + acc_instance.com_a;
        let com_b_acc = alpha * simple_instance.com_b + acc_instance.com_b;
        let com_c_acc = alpha * simple_instance.com_c + acc_instance.com_c;

        // Update scalars
        let u_acc = alpha + acc_instance.u;
        let v_acc = mleE2_prime + alpha * mleT;

        // Fold MLE
        // todo!("Not in the paper, check again later");
        let mlE = mleE2_prime + alpha * mleT;

        Ok(RelaxedCommitedRelation::<C> {
            com_a: com_a_acc,
            com_b: com_b_acc,
            com_c: com_c_acc,
            u: u_acc,
            v: v_acc,
            r: rE_prime.to_vec(),
            mleE: mlE
        })
    }
}