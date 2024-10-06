use super::{CommittedInstance, InstanceWitness, Witness};
use crate::arith::r1cs::R1CS;
use crate::commitment::CommitmentScheme;
use crate::folding::mova::pointvsline::{
    PointVsLine, PointVsLineProof, PointvsLineEvaluationClaim,
};
use crate::folding::nova::nifs::NIFS as Nova;
use crate::transcript::Transcript;
use crate::utils::mle::dense_vec_to_dense_mle;
use crate::utils::vec::{vec_add, vec_scalar_mul};
use crate::Error;
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_poly::MultilinearExtension;
use ark_std::log2;
use std::marker::PhantomData;

/// Implements the Non-Interactive Folding Scheme described in section 4 of
/// [Mova](https://eprint.iacr.org/2024/1220.pdf)
/// `H` specifies whether the NIFS will use a blinding factor
pub struct NIFS<
    C: CurveGroup,
    CS: CommitmentScheme<C, H>,
    T: Transcript<C::ScalarField>,
    const H: bool = false,
> {
    _c: PhantomData<C>,
    _cp: PhantomData<CS>,
    _ct: PhantomData<T>,
}

pub struct Proof<C: CurveGroup> {
    pub h_proof: PointVsLineProof<C>,
    pub mleE1_prime: C::ScalarField,
    pub mleE2_prime: C::ScalarField,
    pub mleT: C::ScalarField,
}

impl<C: CurveGroup, CS: CommitmentScheme<C, H>, T: Transcript<C::ScalarField>, const H: bool>
    NIFS<C, CS, T, H>
where
    <C as Group>::ScalarField: Absorb,
{
    // Just a wrapper for Nova compute_T (compute cross-terms T) since the process is the same
    pub fn compute_T(
        r1cs: &R1CS<C::ScalarField>,
        u1: C::ScalarField,
        u2: C::ScalarField,
        z1: &[C::ScalarField],
        z2: &[C::ScalarField],
    ) -> Result<Vec<C::ScalarField>, Error> {
        Nova::<C, CS, H>::compute_T(r1cs, u1, u2, z1, z2)
    }

    // Protocol 7 - point 3 (16)
    pub fn fold_witness(
        a: C::ScalarField,
        w1: &Witness<C>,
        w2: &Witness<C>,
        T: &[C::ScalarField],
    ) -> Result<Witness<C>, Error> {
        let a2 = a * a;
        let E: Vec<C::ScalarField> = vec_add(
            &vec_add(&w1.E, &vec_scalar_mul(T, &a))?,
            &vec_scalar_mul(&w2.E, &a2),
        )?;
        let W: Vec<C::ScalarField> =
            w1.W.iter()
                .zip(&w2.W)
                .map(|(i1, i2)| *i1 + (a * i2))
                .collect();

        let rW = w1.rW + a * w2.rW;
        Ok(Witness::<C> { E, W, rW })
    }

    // Protocol 7 - point 3 (15)
    pub fn fold_committed_instance(
        a: C::ScalarField,
        ci1: &CommittedInstance<C>,
        ci2: &CommittedInstance<C>,
        rE_prime: &[C::ScalarField],
        mleE1_prime: &C::ScalarField,
        mleE2_prime: &C::ScalarField,
        mleT: &C::ScalarField,
    ) -> Result<CommittedInstance<C>, Error> {
        let a2 = a * a;
        let mleE = *mleE1_prime + a * mleT + a2 * mleE2_prime;
        let u = ci1.u + a * ci2.u;
        let cmW = ci1.cmW + ci2.cmW.mul(a);
        let x = ci1
            .x
            .iter()
            .zip(&ci2.x)
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

    /// [Mova](https://eprint.iacr.org/2024/1220.pdf)'s section 4. Protocol 8
    /// Returns a proof for the pt-vs-line operations along with the folded committed instance
    /// instances and witness
    #[allow(clippy::type_complexity)]
    pub fn prove(
        r1cs: &R1CS<C::ScalarField>,
        transcript: &mut impl Transcript<C::ScalarField>,
        ci1: &CommittedInstance<C>,
        ci2: &CommittedInstance<C>,
        w1: &Witness<C>,
        w2: &Witness<C>,
    ) -> Result<(Proof<C>, InstanceWitness<C>), Error> {
        // Protocol 5 is pre-processing
        transcript.absorb(ci1);
        transcript.absorb(ci2);

        // Protocol 6
        let (
            h_proof,
            PointvsLineEvaluationClaim {
                mleE1_prime,
                mleE2_prime,
                rE_prime,
            },
        ) = PointVsLine::<C, T>::prove(transcript, ci1, ci2, w1, w2)?;

        // Protocol 7

        transcript.absorb(&mleE1_prime);
        transcript.absorb(&mleE2_prime);

        // Remember Z = (W, x, u)
        let z1: Vec<C::ScalarField> = [vec![ci1.u], ci1.x.to_vec(), w1.W.to_vec()].concat();
        let z2: Vec<C::ScalarField> = [vec![ci2.u], ci2.x.to_vec(), w2.W.to_vec()].concat();

        let T = Self::compute_T(r1cs, ci1.u, ci2.u, &z1, &z2)?;

        let n_vars: usize = log2(w1.E.len()) as usize;
        if log2(T.len()) as usize != n_vars {
            return Err(Error::NotEqual);
        }

        let mleT = dense_vec_to_dense_mle(n_vars, &T);
        let mleT_evaluated = mleT.evaluate(&rE_prime).ok_or(Error::EvaluationFail)?;

        transcript.absorb(&mleT_evaluated);

        let alpha_scalar = C::ScalarField::from_le_bytes_mod_order(b"alpha");
        transcript.absorb(&alpha_scalar);
        let alpha: C::ScalarField = transcript.get_challenge();

        Ok((
            Proof::<C> {
                h_proof,
                mleE1_prime,
                mleE2_prime,
                mleT: mleT_evaluated,
            },
            InstanceWitness {
                ci: Self::fold_committed_instance(
                    alpha,
                    ci1,
                    ci2,
                    &rE_prime,
                    &mleE1_prime,
                    &mleE2_prime,
                    &mleT_evaluated,
                )?,
                w: Self::fold_witness(alpha, w1, w2, &T)?,
            },
        ))
    }

    /// [Mova](https://eprint.iacr.org/2024/1220.pdf)'s section 4. It verifies the results from the proof
    /// Both the folding and the pt-vs-line proof
    /// returns the folded committed instance
    pub fn verify(
        transcript: &mut impl Transcript<C::ScalarField>,
        ci1: &CommittedInstance<C>,
        ci2: &CommittedInstance<C>,
        proof: &Proof<C>,
    ) -> Result<CommittedInstance<C>, Error> {
        transcript.absorb(ci1);
        transcript.absorb(ci2);
        let rE_prime = PointVsLine::<C, T>::verify(
            transcript,
            ci1,
            ci2,
            &proof.h_proof,
            &proof.mleE1_prime,
            &proof.mleE2_prime,
        )?;

        transcript.absorb(&proof.mleE1_prime);
        transcript.absorb(&proof.mleE2_prime);
        transcript.absorb(&proof.mleT);

        let alpha_scalar = C::ScalarField::from_le_bytes_mod_order(b"alpha");
        transcript.absorb(&alpha_scalar);
        let alpha: C::ScalarField = transcript.get_challenge();

        Self::fold_committed_instance(
            alpha,
            ci1,
            ci2,
            &rE_prime,
            &proof.mleE1_prime,
            &proof.mleE2_prime,
            &proof.mleT,
        )
    }
}

#[cfg(test)]
pub mod tests {
    use crate::arith::r1cs::{
        tests::{get_test_r1cs, get_test_z},
        RelaxedR1CS,
    };
    use crate::commitment::pedersen::{Params as PedersenParams, Pedersen};
    use crate::transcript::poseidon::poseidon_canonical_config;
    use ark_crypto_primitives::sponge::{
        poseidon::{PoseidonConfig, PoseidonSponge},
        CryptographicSponge,
    };
    use ark_ff::PrimeField;
    use ark_pallas::{Fr, Projective};
    use ark_std::{test_rng, UniformRand, Zero};

    use super::*;

    #[allow(clippy::type_complexity)]
    fn prepare_simple_fold_inputs<C>() -> (
        PedersenParams<C>,
        PoseidonConfig<C::ScalarField>,
        R1CS<C::ScalarField>,
        Witness<C>,           // w1
        CommittedInstance<C>, // ci1
        Witness<C>,           // w2
        CommittedInstance<C>, // ci2
        Proof<C>,             // pt-vs-line
        InstanceWitness<C>,   // w3, ci3
    )
    where
        C: CurveGroup,
        <C as CurveGroup>::BaseField: PrimeField,
        C::ScalarField: Absorb,
    {
        let r1cs = get_test_r1cs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);
        let (w1, x1) = r1cs.split_z(&z1);
        let (w2, x2) = r1cs.split_z(&z2);

        let mut rng = ark_std::test_rng();

        let w1 = Witness::<C>::new::<false>(w1.clone(), r1cs.A.n_rows, &mut rng);
        let w2 = Witness::<C>::new::<false>(w2.clone(), r1cs.A.n_rows, &mut rng);

        let (pedersen_params, _) = Pedersen::<C>::setup(&mut rng, r1cs.A.n_cols).unwrap();

        // compute committed instances
        let rE_1: Vec<C::ScalarField> = (0..log2(3))
            .map(|_| C::ScalarField::rand(&mut rng))
            .collect();
        let rE_2: Vec<C::ScalarField> = (0..log2(4))
            .map(|_| C::ScalarField::rand(&mut rng))
            .collect();
        let ci1 = w1
            .commit::<Pedersen<C>>(&pedersen_params, x1.clone(), rE_1)
            .unwrap();
        let ci2 = w2
            .commit::<Pedersen<C>>(&pedersen_params, x2.clone(), rE_2)
            .unwrap();

        let poseidon_config = poseidon_canonical_config::<C::ScalarField>();
        let mut transcript_p = PoseidonSponge::<C::ScalarField>::new(&poseidon_config);

        let result = NIFS::<C, Pedersen<C>, PoseidonSponge<C::ScalarField>>::prove(
            &r1cs,
            &mut transcript_p,
            &ci1,
            &ci2,
            &w1,
            &w2,
        )
        .unwrap();
        let (proof, instance) = result;

        (
            pedersen_params,
            poseidon_config,
            r1cs,
            w1,
            ci1,
            w2,
            ci2,
            proof,
            instance,
        )
    }

    // fold 2 dummy instances and check that the folded instance holds the relaxed R1CS relation
    #[test]
    fn test_nifs_fold_dummy() {
        let r1cs = get_test_r1cs::<Fr>();
        let z1 = get_test_z(3);
        let (w1, x1) = r1cs.split_z(&z1);

        let mut rng = ark_std::test_rng();
        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, r1cs.A.n_cols).unwrap();

        // dummy instance, witness and public inputs zeroes
        let w_dummy = Witness::<Projective>::dummy(w1.len(), r1cs.A.n_rows);
        let mut u_dummy = w_dummy
            .commit::<Pedersen<Projective>>(
                &pedersen_params,
                vec![Fr::zero(); x1.len()],
                vec![Fr::zero(); log2(3) as usize],
            )
            .unwrap();
        u_dummy.u = Fr::zero();

        let w_i = w_dummy.clone();
        let u_i = u_dummy.clone();
        let W_i = w_dummy.clone();
        let U_i = u_dummy.clone();

        r1cs.check_relaxed_relation(&w_i, &u_i).unwrap();
        r1cs.check_relaxed_relation(&W_i, &U_i).unwrap();

        let poseidon_config = poseidon_canonical_config::<ark_pallas::Fr>();
        let mut transcript_p: PoseidonSponge<Fr> = PoseidonSponge::<Fr>::new(&poseidon_config);

        let result = NIFS::<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>::prove(
            &r1cs,
            &mut transcript_p,
            &u_i,
            &U_i,
            &w_i,
            &W_i,
        )
        .unwrap();

        let (_proof, instance_witness) = result;
        r1cs.check_relaxed_relation(&instance_witness.w, &instance_witness.ci)
            .unwrap();
    }

    // fold 2 instances into one
    #[test]
    fn test_nifs_one_fold() {
        let (pedersen_params, poseidon_config, r1cs, w1, ci1, w2, ci2, proof, instance) =
            prepare_simple_fold_inputs::<Projective>();

        // NIFS.V
        let mut transcript_v: PoseidonSponge<Fr> = PoseidonSponge::<Fr>::new(&poseidon_config);
        let ci3 = NIFS::<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>::verify(
            &mut transcript_v,
            &ci1,
            &ci2,
            &proof,
        )
        .unwrap();
        assert_eq!(ci3, instance.ci);

        // check that relations hold for the 2 inputted instances and the folded one
        r1cs.check_relaxed_relation(&w1, &ci1).unwrap();
        r1cs.check_relaxed_relation(&w2, &ci2).unwrap();
        r1cs.check_relaxed_relation(&instance.w, &instance.ci)
            .unwrap();

        // check that folded commitments from folded instance (ci) are equal to folding the
        // use folded rE, rW to commit w3
        let ci3_expected = instance
            .w
            .commit::<Pedersen<Projective>>(&pedersen_params, ci3.x.clone(), instance.ci.rE)
            .unwrap();
        assert_eq!(ci3_expected.cmW, instance.ci.cmW);
    }

    #[test]
    fn test_nifs_fold_loop() {
        let r1cs = get_test_r1cs();
        let z = get_test_z(3);
        let (w, x) = r1cs.split_z(&z);

        let mut rng = ark_std::test_rng();
        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, r1cs.A.n_cols).unwrap();

        // prepare the running instance
        let rE: Vec<Fr> = (0..log2(3)).map(|_| Fr::rand(&mut rng)).collect();
        let mut running_instance_w =
            Witness::<Projective>::new::<false>(w.clone(), r1cs.A.n_rows, test_rng());
        let mut running_committed_instance = running_instance_w
            .commit::<Pedersen<Projective>>(&pedersen_params, x, rE)
            .unwrap();

        r1cs.check_relaxed_relation(&running_instance_w, &running_committed_instance)
            .unwrap();

        let num_iters = 10;
        for i in 0..num_iters {
            // prepare the incoming instance
            let incoming_instance_z = get_test_z(i + 4);
            let (w, x) = r1cs.split_z(&incoming_instance_z);
            let incoming_instance_w =
                Witness::<Projective>::new::<false>(w.clone(), r1cs.A.n_rows, test_rng());
            let rE: Vec<Fr> = (0..log2(3)).map(|_| Fr::rand(&mut rng)).collect();
            let incoming_committed_instance = incoming_instance_w
                .commit::<Pedersen<Projective>>(&pedersen_params, x, rE)
                .unwrap();
            r1cs.check_relaxed_relation(&incoming_instance_w, &incoming_committed_instance)
                .unwrap();

            // NIFS.P
            let poseidon_config = poseidon_canonical_config::<Fr>();
            let mut transcript_p = PoseidonSponge::<Fr>::new(&poseidon_config);

            let result = NIFS::<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>::prove(
                &r1cs,
                &mut transcript_p,
                &running_committed_instance,
                &incoming_committed_instance,
                &running_instance_w,
                &incoming_instance_w,
            )
            .unwrap();

            let (proof, instance_witness) = result;

            // NIFS.V
            let mut transcript_v: PoseidonSponge<Fr> = PoseidonSponge::<Fr>::new(&poseidon_config);
            let _ci3 = NIFS::<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>::verify(
                &mut transcript_v,
                &running_committed_instance,
                &incoming_committed_instance,
                &proof,
            )
            .unwrap();

            r1cs.check_relaxed_relation(&instance_witness.w, &instance_witness.ci)
                .unwrap();

            // set running_instance for next loop iteration
            running_instance_w = instance_witness.w;
            running_committed_instance = instance_witness.ci;
        }
    }
}
