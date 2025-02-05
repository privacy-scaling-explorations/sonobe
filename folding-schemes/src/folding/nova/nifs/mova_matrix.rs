/// Mova-like folding for matrix multiplications as described in "Folding and Lookup Arguments for Proving Inference of Deep Learning Models" by Nethermind Research
/// Currently, we are not interested in the hiding properties, so we ignore the hiding factors and focus on the succinctness property.
/// Please note the code could be easily extended so support hiding.
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
use ark_crypto_primitives::sponge::Absorb;
use ark_ff::PrimeField;
use ark_poly::Polynomial;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{log2, marker::PhantomData, rand::RngCore, One, UniformRand, Zero};
use num_integer::Roots;

/// Represents a relaxed committed relation for matrix multiplication folded instances.
/// Where A, B, C are nxn matrices such that:
/// A * B = u * C + E
/// where u is a scalar, and E is the error matrix.
/// When u=1 and E is the zero matrix, we have the simple committed relation in which A * B = C.
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize)]
pub struct RelaxedCommittedRelation<C: Curve> {
    pub cmA: C,                  // Commitment to matrix A. cmA = commitment(A).
    pub cmB: C,                  // Commitment to matrix B. cmB = commitment(B).
    pub cmC: C,                  // Commitment to matrix C. cmC = commitment(C).
    pub u: C::ScalarField,       // Scalar used in the folding.
    pub mleE: C::ScalarField, // v = mle[E](rE) in MOVA notation. Multilinear extension of matrix E evaluated at random point rE.
    pub rE: Vec<C::ScalarField>, // Random point where MLE is evaluated. Size of 2 * log2(n).
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
    // Matrices are expected to be square. size = nxn
    fn dummy(size: usize) -> Self {
        Self {
            cmA: C::zero(),
            cmB: C::zero(),
            cmC: C::zero(),
            u: C::ScalarField::zero(),
            mleE: C::ScalarField::zero(),
            rE: vec![C::ScalarField::zero(); 2 * log2(size.sqrt()) as usize],
        }
    }
}

impl<C: Curve> RelaxedCommittedRelation<C> {
    /// Checks if a Relaxed Committed Relation is simple (has not been folded).
    fn is_simple(&self) -> bool {
        self.u == C::ScalarField::from(1) && self.mleE == C::ScalarField::zero()
    }

    /// Checks if a Relaxed Committed Relation is accumulated (has been folded).
    fn is_accumulated(&self) -> bool {
        self.u != C::ScalarField::from(1) && self.mleE != C::ScalarField::zero()
    }
}
/// Represents the private inputs for the protocol (witness)
/// A, B, C, E are matrices such that A * B = u* C + E
/// Matrices are, for Sonobe compatibility, represented as flattened vectors.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Witness<C: Curve> {
    pub A: Vec<C::ScalarField>, // Matrix A in flattened form
    pub B: Vec<C::ScalarField>, // Matrix B in flattened form
    pub C: Vec<C::ScalarField>, // Matrix C in flattened form
    pub E: Vec<C::ScalarField>, // Error matrix E in flattened form
}

impl<C: Curve> Dummy<usize> for Witness<C> {
    // Matrices are expected to be square. size = nxn
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
    /// Commits to a witness W and produces a RelaxedCommittedRelation
    /// # Parameters
    /// * `self` - Witness instance to be committed.
    /// * `params` - Commitment scheme parameters.
    /// * `rE` - Random evaluation point for the committed instance.
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

        // Right now we are ignoring the hiding property and directly commit to the matrices
        let com_a = CS::commit(params, &self.A, &C::ScalarField::zero())?;
        let com_b = CS::commit(params, &self.B, &C::ScalarField::zero())?;
        let com_c = CS::commit(params, &self.C, &C::ScalarField::zero())?;

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

/// Represents proof of the matrix folding
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<C: Curve> {
    /// Proof of the PointVsLine protocol that reduces the number of MLE evaluations.
    pub h_proof: PointVsLineProofMatrix<C>,
    /// Evaluation of the MLE[h2] in the random challenge beta
    pub mleE2_prime: C::ScalarField,
    /// Evaluation of the cross term T in r_acc = MLE[T](r_acc)
    pub mleT: C::ScalarField,
    /// Evaluation of the h polynomial in the random challenge beta
    pub rE_prime: Vec<C::ScalarField>,
}

/// Implements the Non-Interactive Folding Scheme described in section 3.2 of the previous referenced article.
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
        aux: Vec<C::ScalarField>, // rE in MOVA notation.
    ) -> Result<Self::CommittedInstance, Error> {
        let mut rE = aux;
        if is_zero_vec(&rE) {
            // means that we're in a fresh instance, so generate value of length 2 * log2(n)
            rE = (0..2 * log2(witness.E.len().sqrt()))
                .map(|_| C::ScalarField::rand(&mut rng))
                .collect();
        }
        witness.commit::<CS, H>(params, rE)
    }

    // Protocol 5 - point 8 (Page 25)
    fn fold_witness(
        alpha: C::ScalarField,     // Random challenge
        simple_wit: &Witness<C>,   // Simple witness
        acc_wit: &Witness<C>,      // Accumulated witness
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

    /// Protocol 5 for MOVA-like matrix folding
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

    /// It verifies the results from the proof
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
    /// Folds two committed instances into a single one using the provided parameters
    /// Protocol 5 - Step 7 (page 25) for folding instances
    /// # Parameters
    /// * `alpha` - Random challenge used for folding
    /// * `simple_instance` - The simple (unfolded) instance
    /// * `acc_instance` - The accumulated (previously folded) instance  
    /// * `rE_prime` - New random evaluation point
    /// * `mleE2_prime` - Evaluation of MLE[E2] at rE_prime
    /// * `mleT` - Evaluation of the crossterm T
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
        let mleE = *mleE2_prime + alpha * *mleT;

        Ok(RelaxedCommittedRelation::<C> {
            cmA: com_a_acc,
            cmB: com_b_acc,
            cmC: com_c_acc,
            u: u_acc,
            mleE,
            rE: rE_prime.to_vec(),
        })
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::arith::r1cs::tests::get_test_r1cs;
    use crate::commitment::pedersen::Pedersen;
    use crate::transcript::poseidon::poseidon_canonical_config;
    use ark_crypto_primitives::sponge::{poseidon::PoseidonSponge, CryptographicSponge};
    use ark_pallas::{Fr, Projective};

    // Helper functions
    fn get_instances<C: Curve, CS: CommitmentScheme<C>>(
        num: usize,
        n: usize,
        rng: &mut impl RngCore,
        params: &CS::ProverParams,
    ) -> Vec<(Witness<C>, RelaxedCommittedRelation<C>)> {
        (0..num)
            .map(|_| -> (Witness<C>, RelaxedCommittedRelation<C>) {
                // A matrix
                let a: Vec<C::ScalarField> =
                    (0..n * n).map(|_| C::ScalarField::rand(rng)).collect();
                // B matrix
                let b: Vec<C::ScalarField> =
                    (0..n * n).map(|_| C::ScalarField::rand(rng)).collect();
                // C = A * B matrix
                let c: Vec<C::ScalarField> = mat_mat_mul_dense(&a, &b).unwrap();
                // Error matrix initialized to 0s
                let e: Vec<C::ScalarField> = (0..n * n).map(|_| C::ScalarField::from(0)).collect();
                // Random challenge
                let rE = (0..2 * log2(n))
                    .map(|_| C::ScalarField::rand(rng))
                    .collect();
                // Witness
                let witness = Witness::new::<false>(a, b, c, e);
                let instance = witness.commit::<CS, false>(params, rE).unwrap();
                (witness, instance)
            })
            .collect()
    }
    #[test]
    fn test_nifs_mova_matrix_single_fold() {
        // Set up test instances
        let mut rng = ark_std::test_rng();
        let n_instances = 2;
        let mat_dim = 4; // 4x4 matrices

        // Set up transcript and commitment scheme
        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, mat_dim * mat_dim).unwrap();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript_p = PoseidonSponge::<Fr>::new(&poseidon_config);
        let mut transcript_v = PoseidonSponge::<Fr>::new(&poseidon_config);
        let pp_hash = Fr::rand(&mut rng);

        let instances: Vec<(Witness<Projective>, RelaxedCommittedRelation<Projective>)> =
            get_instances::<Projective, Pedersen<Projective>>(
                n_instances,
                mat_dim,
                &mut rng,
                &pedersen_params,
            );

        let r1cs: R1CS<Fr> = get_test_r1cs();
        for i in 0..instances.len() - 1 {
            // Fold
            let (_wit_acc, instance_acc, proof, _) =
                NIFS::<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>::prove(
                    &pedersen_params,
                    &r1cs,
                    &mut transcript_p,
                    pp_hash,
                    &instances[i].0,
                    &instances[i].1,
                    &instances[i + 1].0,
                    &instances[i + 1].1,
                )
                .unwrap();

            // Verify
            let (ci_verify, _) =
                NIFS::<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>::verify(
                    &mut transcript_v,
                    pp_hash,
                    &instances[i].1,
                    &instances[i + 1].1,
                    &proof,
                )
                .unwrap();

            // Ensure they match
            assert_eq!(instance_acc, ci_verify);
        }
    }

    #[test]
    fn test_nifs_mova_matrix_multiple_folds() {
        // Set up test instances
        let mut rng = ark_std::test_rng();
        let n_folds = 10;
        let n_instances = n_folds + 1;
        let mat_dim = 16; // 16x16 matrices

        // Set up transcript and commitment scheme
        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, mat_dim * mat_dim).unwrap();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript_p = PoseidonSponge::<Fr>::new(&poseidon_config);
        let mut transcript_v = PoseidonSponge::<Fr>::new(&poseidon_config);
        let pp_hash = Fr::rand(&mut rng);

        let mut instances: Vec<(Witness<Projective>, RelaxedCommittedRelation<Projective>)> =
            get_instances::<Projective, Pedersen<Projective>>(
                n_instances,
                mat_dim,
                &mut rng,
                &pedersen_params,
            );

        let r1cs: R1CS<Fr> = get_test_r1cs();

        // Keep track of the accumulated state
        let mut current_acc_wit = instances.remove(0).0;
        let mut current_acc_inst = instances.remove(0).1;

        // Fold through all remaining instances
        for (next_w, next_i) in instances {
            // Fold
            let (wit_acc, inst_acc, proof, _) =
                NIFS::<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>::prove(
                    &pedersen_params,
                    &r1cs,
                    &mut transcript_p,
                    pp_hash,
                    &next_w,
                    &next_i,
                    &current_acc_wit,
                    &current_acc_inst,
                )
                .unwrap();

            // Verify
            let (ci_verify, _) =
                NIFS::<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>::verify(
                    &mut transcript_v,
                    pp_hash,
                    &next_i,
                    &current_acc_inst,
                    &proof,
                )
                .unwrap();

            // Ensure they match
            assert_eq!(inst_acc, ci_verify);

            // Update state for next iteration
            current_acc_wit = wit_acc;
            current_acc_inst = inst_acc;
        }
    }
}
