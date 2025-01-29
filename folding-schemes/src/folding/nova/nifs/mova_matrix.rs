use ark_crypto_primitives::sponge::Absorb;
use ark_ff::PrimeField;
use ark_poly::Polynomial;
/// Mova-like folding for matrix multiplications as descbribed in !todo(add reference to paper if public)
// !todo(Add blinding factor to support hiding property).
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{log2, marker::PhantomData, rand::RngCore, One, UniformRand, Zero};

use crate::arith::r1cs::R1CS;
use crate::commitment::CommitmentScheme;
use crate::folding::nova::nifs::pointvsline::{
    PointVsLine, PointVsLineEvaluationClaimMatrix, PointVsLineMatrix, PointVsLineProofMatrix,
};
use crate::folding::nova::nifs::NIFSTrait;
use crate::folding::traits::Dummy;
use crate::transcript::Transcript;
use crate::utils::mle::dense_vec_to_dense_mle;
use crate::utils::vec::{is_zero_vec, mat_mat_mul_dense, vec_add, vec_scalar_mul, vec_sub};
use crate::{Curve, Error};
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize)]
pub struct RelaxedCommittedRelation<C: Curve> {
    pub cmA: C,
    pub cmB: C,
    pub cmC: C,
    pub u: C::ScalarField,
    pub mleE: C::ScalarField, // v in MOVA notation
    pub rE: Vec<C::ScalarField>,
}

impl<C: Curve> Absorb for RelaxedCommittedRelation<C> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        C::ScalarField::batch_to_sponge_bytes(&self.to_sponge_field_elements_as_vec(), dest);
    }

    fn to_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        self.cmA.to_native_sponge_field_elements(dest);
        self.cmB.to_native_sponge_field_elements(dest);
        self.cmC.to_native_sponge_field_elements(dest);
        self.u.to_sponge_field_elements(dest);
        self.mleE.to_sponge_field_elements(dest);
        self.rE.to_sponge_field_elements(dest);
    }
}

impl<C: Curve> Dummy<usize> for RelaxedCommittedRelation<C> {
    fn dummy(size: usize) -> Self {
        Self {
            cmA: C::zero(),
            cmB: C::zero(),
            cmC: C::zero(),
            u: C::ScalarField::zero(),
            mleE: C::ScalarField::zero(),
            rE: vec![C::ScalarField::zero(); 2 * size],
        }
    }
}

impl<C: Curve> RelaxedCommittedRelation<C> {
    fn is_simple(&self) -> bool {
        self.u == C::ScalarField::from(1) && self.mleE == C::ScalarField::zero()
    }

    fn is_accumulated(&self) -> bool {
        self.u != C::ScalarField::from(1) && self.mleE != C::ScalarField::zero()
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Witness<C: Curve> {
    pub A: Vec<C::ScalarField>,
    pub B: Vec<C::ScalarField>,
    pub C: Vec<C::ScalarField>,
    pub E: Vec<C::ScalarField>,
}

impl<C: Curve> Dummy<usize> for Witness<C> {
    fn dummy(size: usize) -> Self {
        Self {
            A: vec![C::ScalarField::zero(); size],
            B: vec![C::ScalarField::zero(); size],
            C: vec![C::ScalarField::zero(); size],
            E: vec![C::ScalarField::zero(); size],
        }
    }
}

impl<C: Curve> Witness<C> {
    pub fn new<const H: bool>(
        a: Vec<C::ScalarField>,
        b: Vec<C::ScalarField>,
        c: Vec<C::ScalarField>,
        e: Vec<C::ScalarField>,
    ) -> Self {
        Self {
            A: a,
            B: b,
            C: c,
            E: e,
        }
    }

    pub fn commit<CS: CommitmentScheme<C, H>, const H: bool>(
        &self,
        params: &CS::ProverParams,
        rE: Vec<C::ScalarField>,
    ) -> Result<RelaxedCommittedRelation<C>, Error> {
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
        Ok(RelaxedCommittedRelation {
            cmA: com_a,
            cmB: com_b,
            cmC: com_c,
            u: C::ScalarField::one(),
            mleE,
            rE,
        })
    }
}

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<C: Curve> {
    pub h_proof: PointVsLineProofMatrix<C>,
    pub mleE2_prime: C::ScalarField,
    pub mleT: C::ScalarField,
    pub rE_prime: Vec<C::ScalarField>,
}

/// Implements the Non-Interactive Folding Scheme described in section 4 of
/// [Mova](https://eprint.iacr.org/2024/1220.pdf).
/// `H` specifies whether the NIFS will use a blinding factor
#[allow(clippy::upper_case_acronyms)]
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
    type CommittedInstance = RelaxedCommittedRelation<C>;
    type Witness = Witness<C>;
    type ProverAux = Vec<C::ScalarField>; // T in Mova's notation
    type Proof = Proof<C>;

    // Right now we are packing the 4 matrices in a single vector to achieve compatibility with NIFStrait.
    fn new_witness(abce: Vec<C::ScalarField>, e_len: usize, _rng: impl RngCore) -> Self::Witness {
        assert_eq!(
            abce.len() % 4,
            0,
            "Input vector length must be a multiple of 4"
        );
        let chunk_size = e_len / 4;

        // Split vector into matrices
        let (a, rest) = abce.split_at(chunk_size);
        let (b, rest) = rest.split_at(chunk_size);
        let (c, e) = rest.split_at(chunk_size);
        Witness::new::<H>(a.to_vec(), b.to_vec(), c.to_vec(), e.to_vec())
    }

    fn new_instance(
        mut rng: impl RngCore,
        params: &CS::ProverParams,
        witness: &Self::Witness,
        _x: Vec<C::ScalarField>,
        aux: Vec<C::ScalarField>, // = rE
    ) -> Result<Self::CommittedInstance, Error> {
        let mut rE = aux.clone();
        if is_zero_vec(&rE) {
            // means that we're in a fresh instance, so generate random value
            rE = (0..2 * log2(witness.E.len()))
                .map(|_| C::ScalarField::rand(&mut rng))
                .collect();
        }
        witness.commit::<CS, H>(params, rE)
    }

    // Protocol 5 - point 8 (Page 25)
    fn fold_witness(
        alpha: C::ScalarField,
        simple_wit: &Witness<C>,
        acc_wit: &Witness<C>,
        aux: &Vec<C::ScalarField>, // T in Mova's notation
    ) -> Result<Witness<C>, Error> {
        let a_acc = vec_add(&vec_scalar_mul(&simple_wit.A, &alpha), &acc_wit.A)?;
        let b_acc = vec_add(&vec_scalar_mul(&simple_wit.B, &alpha), &acc_wit.B)?;
        let c_acc = vec_add(&vec_scalar_mul(&simple_wit.C, &alpha), &acc_wit.C)?;
        let e_acc = vec_add(&vec_scalar_mul(aux, &alpha), &acc_wit.E)?;

        Ok(Witness::<C> {
            A: a_acc,
            B: b_acc,
            C: c_acc,
            E: e_acc,
        })
    }

    /// [Mova](https://eprint.iacr.org/2024/1220.pdf)'s section 4. Protocol 8
    /// Returns a proof for the pt-vs-line operations along with the folded committed instance
    /// instances and witness
    #[allow(clippy::type_complexity)]
    fn prove(
        _cs_prover_params: &CS::ProverParams, // not used in Mova since we don't commit to T
        _r1cs: &R1CS<C::ScalarField>,
        transcript: &mut T,
        pp_hash: C::ScalarField,
        simple_witness: &Witness<C>,
        simple_instance: &RelaxedCommittedRelation<C>,
        acc_witness: &Witness<C>,
        acc_instance: &RelaxedCommittedRelation<C>,
    ) -> Result<
        (
            Self::Witness,
            Self::CommittedInstance,
            Self::Proof,
            Vec<bool>,
        ),
        Error,
    > {
        // Verify instances have the correct form.
        // 2 simple instances can be folded, a simple and an accumulated instance can also be folded. 2 accumulated instances cannot be folded
        if simple_instance.is_accumulated() {
            return if acc_instance.is_simple() {
                Err(Error::Other(String::from(
                    "Parameters were passed in the wrong order. They need to be reordered.",
                )))
            } else {
                Err(Error::Other(String::from(
                    "Cannot fold 2 accumulated instances.",
                )))
            };
        }

        transcript.absorb(&pp_hash);
        transcript.absorb(simple_instance);
        transcript.absorb(acc_instance);

        // Protocol 5 - Steps 1-3
        let (
            h_proof,
            PointVsLineEvaluationClaimMatrix {
                mleE2_prime,
                rE_prime,
            },
        ) = PointVsLineMatrix::<C, T>::prove(
            transcript,
            None,
            acc_instance,
            simple_witness,
            acc_witness,
        )?;

        transcript.absorb(&mleE2_prime);

        // todo!("Change to sparse Matrices. Review witness types")
        // Compute cross term T
        let A1B2 = mat_mat_mul_dense(&simple_witness.A, &acc_witness.B)?;
        let B1A2 = mat_mat_mul_dense(&acc_witness.A, &simple_witness.B)?;
        let A1B2B1A2 = vec_add(&A1B2, &B1A2)?;
        let u2c1: Vec<C::ScalarField> = vec_scalar_mul(&simple_witness.C, &acc_instance.u);
        let T = vec_sub(&vec_sub(&A1B2B1A2, &acc_witness.C)?, &u2c1)?;

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
            simple_instance,
            acc_instance,
            &rE_prime,
            &mleE2_prime,
            &mleT_evaluated,
        )?;
        let w = Self::fold_witness(alpha, simple_witness, acc_witness, &T)?;

        // todo!(Review when new Pointvsline protocol is ready)
        let proof = Self::Proof {
            h_proof,
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
        pp_hash: C::ScalarField,
        simple_instance: &RelaxedCommittedRelation<C>,
        acc_instance: &RelaxedCommittedRelation<C>,
        proof: &Proof<C>,
    ) -> Result<(Self::CommittedInstance, Vec<bool>), Error> {
        transcript.absorb(&pp_hash);
        transcript.absorb(simple_instance);
        transcript.absorb(acc_instance);

        // Verify rE_prime
        let rE_prime = PointVsLineMatrix::<C, T>::verify(
            transcript,
            None,
            acc_instance,
            &proof.h_proof,
            None,
            &proof.mleE2_prime,
            &proof.rE_prime,
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
        simple_instance: &RelaxedCommittedRelation<C>,
        acc_instance: &RelaxedCommittedRelation<C>,
        rE_prime: &[C::ScalarField],
        mleE2_prime: &C::ScalarField, // v' in Protocol 5
        mleT: &C::ScalarField,
    ) -> Result<RelaxedCommittedRelation<C>, Error> {
        // Step 7
        // Accumulate commitments
        let com_a_acc = simple_instance.cmA.mul(alpha) + acc_instance.cmA;
        let com_b_acc = simple_instance.cmB.mul(alpha) + acc_instance.cmB;
        let com_c_acc = simple_instance.cmC.mul(alpha) + acc_instance.cmC;

        // Update scalars
        let u_acc = alpha + acc_instance.u;
        let mlE = *mleE2_prime + alpha * *mleT;

        Ok(RelaxedCommittedRelation::<C> {
            cmA: com_a_acc,
            cmB: com_b_acc,
            cmC: com_c_acc,
            u: u_acc,
            mleE: mlE,
            rE: rE_prime.to_vec(),
        })
    }
}
