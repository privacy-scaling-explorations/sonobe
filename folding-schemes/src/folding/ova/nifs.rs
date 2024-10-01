/// This module contains the implementation of the Ova scheme NIFS (Non-Interactive Folding Scheme) as
/// outlined in the protocol description doc: <https://hackmd.io/V4838nnlRKal9ZiTHiGYzw?both#Construction>
/// authored by Benedikt Bünz.
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_std::One;
use std::marker::PhantomData;

use super::{CommittedInstance, Witness};
use crate::arith::r1cs::R1CS;
use crate::commitment::CommitmentScheme;
use crate::transcript::Transcript;
use crate::utils::vec::{hadamard, mat_vec_mul, vec_scalar_mul, vec_sub};
use crate::Error;

/// Implements all the operations executed by the Non-Interactive Folding Scheme described in the protocol
/// spec by Bünz in the [original HackMD](https://hackmd.io/V4838nnlRKal9ZiTHiGYzw?both#Construction).
/// `H` specifies whether the NIFS will use a blinding factor
pub struct NIFS<C: CurveGroup, CS: CommitmentScheme<C, H>, const H: bool = false> {
    _c: PhantomData<C>,
    _cp: PhantomData<CS>,
}

impl<C: CurveGroup, CS: CommitmentScheme<C, H>, const H: bool> NIFS<C, CS, H>
where
    <C as Group>::ScalarField: Absorb,
{
    /// Computes the T parameter (Cross Terms) as in Nova.
    /// The wrapper is only in place to facilitate the calling as we need
    /// to reconstruct the `z`s being folded in order to compute T.
    pub fn compute_T(
        r1cs: &R1CS<C::ScalarField>,
        w_i: &Witness<C>,
        x_i: &[C::ScalarField],
        W_i: &Witness<C>,
        X_i: &[C::ScalarField],
        mu: C::ScalarField,
    ) -> Result<Vec<C::ScalarField>, Error> {
        crate::folding::nova::nifs::NIFS::<C, CS, H>::compute_T(
            &r1cs,
            C::ScalarField::one(),
            mu,
            &[vec![C::ScalarField::one()], x_i.to_vec(), w_i.w.to_vec()].concat(),
            &[vec![mu], X_i.to_vec(), W_i.w.to_vec()].concat(),
        )
    }

    /// Computes the E parameter (Error Terms) as in Nova.
    /// The wrapper is only in place to facilitate the calling as we need
    /// to reconstruct the `z`s being folded in order to compute E.
    ///
    /// Not only that, but notice that the incoming-instance `mu` parameter is always
    /// equal to 1. Therefore, we can save the some computations.
    pub fn compute_E(
        r1cs: &R1CS<C::ScalarField>,
        w_acc: &Witness<C>,
        x_acc: &[C::ScalarField],
        mu: C::ScalarField,
    ) -> Result<Vec<C::ScalarField>, Error> {
        let (A, B, C) = (r1cs.A.clone(), r1cs.B.clone(), r1cs.C.clone());

        let z_prime = [&[mu], x_acc, &w_acc.w].concat();
        // this is parallelizable (for the future)
        let Az_prime = mat_vec_mul(&A, &z_prime)?;
        let Bz_prime = mat_vec_mul(&B, &z_prime)?;
        let Cz_prime = mat_vec_mul(&C, &z_prime)?;

        let Az_prime_Bz_prime = hadamard(&Az_prime, &Bz_prime)?;
        let muCz_prime = vec_scalar_mul(&Cz_prime, &mu);

        vec_sub(&Az_prime_Bz_prime, &muCz_prime)
    }

    /// Computes the `W` or `W'` commitment. (The accumulated-instance W' or the incoming-instance W).
    /// This is the result of concatenating the accumulated-instance `w` vector with
    /// `e` or `t` and committing to the result.
    ///
    /// This is the exact trick that allows Ova to save up 1 commitment with respect to Nova.
    /// At the cost of loosing the PCD property and only maintaining the IVC one.
    pub fn compute_cmW(
        cs_prover_params: &CS::ProverParams,
        w: Witness<C>,
        t_or_e: Vec<C::ScalarField>,
    ) -> Result<C, Error> {
        let w_concat_t_or_e: Vec<C::ScalarField> = [w.w.to_vec(), t_or_e].concat();

        CS::commit(cs_prover_params, &w_concat_t_or_e, &w.rW)
    }

    /// Folds 2 [`CommittedInstance`]s returning a freshly folded one as is specified
    /// in: <https://hackmd.io/V4838nnlRKal9ZiTHiGYzw?both#Construction>.
    /// Here, alpha is a randomness sampled from a [`Transcript`].
    pub fn fold_committed_instance(
        alpha: C::ScalarField,
        // This is W' (running)
        ci1: &CommittedInstance<C>,
        // This is W (incoming)
        ci2: &CommittedInstance<C>,
    ) -> CommittedInstance<C> {
        let mu = ci1.mu + alpha; // ci2.mu **IS ALWAYS 1 in OVA** as we just can do sequencial IVC.
        let cmWE = ci1.cmWE + ci2.cmWE.mul(alpha);
        let x = ci1
            .x
            .iter()
            .zip(&ci2.x)
            .map(|(a, b)| *a + (alpha * b))
            .collect::<Vec<C::ScalarField>>();

        CommittedInstance::<C> { cmWE, mu, x }
    }

    /// Folds 2 [`Witness`]s returning a freshly folded one as is specified
    /// in: <https://hackmd.io/V4838nnlRKal9ZiTHiGYzw?both#Construction>.
    /// Here, alpha is a randomness sampled from a [`Transcript`].
    pub fn fold_witness(
        alpha: C::ScalarField,
        // runnig instance
        w1: &Witness<C>,
        // incoming instance
        w2: &Witness<C>,
    ) -> Result<Witness<C>, Error> {
        let w: Vec<C::ScalarField> =
            w1.w.iter()
                .zip(&w2.w)
                .map(|(a, b)| *a + (alpha * b))
                .collect();

        let rW = w1.rW + alpha * w2.rW;
        Ok(Witness::<C> { w, rW })
    }

    /// fold_instances is part of the NIFS.P logic described in
    /// [Ova](https://hackmd.io/V4838nnlRKal9ZiTHiGYzw?both#Construction)'s Construction section.
    /// It returns the folded [`CommittedInstance`] and [`Witness`].
    pub fn fold_instances(
        r: C::ScalarField,
        // runnig instance
        w1: &Witness<C>,
        ci1: &CommittedInstance<C>,
        // incoming instance
        w2: &Witness<C>,
        ci2: &CommittedInstance<C>,
    ) -> Result<(Witness<C>, CommittedInstance<C>), Error> {
        // fold witness
        // use r_T=0 since we don't need hiding property for cm(T)
        let w3 = NIFS::<C, CS, H>::fold_witness(r, w1, w2)?;

        // fold committed instances
        let ci3 = NIFS::<C, CS, H>::fold_committed_instance(r, ci1, ci2);

        Ok((w3, ci3))
    }

    /// Implements NIFS.V (accumulation verifier) logic described in [Ova](https://hackmd.io/V4838nnlRKal9ZiTHiGYzw?both#Construction)'s
    /// Construction section.
    /// It returns the folded [`CommittedInstance`].
    pub fn verify(
        // r comes from the transcript, and is a n-bit (N_BITS_CHALLENGE) element
        alpha: C::ScalarField,
        ci1: &CommittedInstance<C>,
        ci2: &CommittedInstance<C>,
    ) -> CommittedInstance<C> {
        NIFS::<C, CS, H>::fold_committed_instance(alpha, ci1, ci2)
    }

    #[cfg(test)]
    /// Verify committed folded instance (ci) relations. Notice that this method does not open the
    /// commitments, but just checks that the given committed instances (ci1, ci2) when folded
    /// result in the folded committed instance (ci3) values.
    pub(crate) fn verify_folded_instance(
        r: C::ScalarField,
        // running instance
        ci1: &CommittedInstance<C>,
        // incoming instance
        ci2: &CommittedInstance<C>,
        // folded instance
        ci3: &CommittedInstance<C>,
    ) -> Result<(), Error> {
        let expected = Self::fold_committed_instance(r, ci1, ci2);
        if ci3.mu != expected.mu || ci3.cmWE != expected.cmWE || ci3.x != expected.x {
            return Err(Error::NotSatisfied);
        }
        Ok(())
    }

    /// Generates a [`CS::Proof`] for the given [`CommittedInstance`] and [`Witness`] pair.
    pub fn prove_commitment(
        r1cs: &R1CS<C::ScalarField>,
        tr: &mut impl Transcript<C::ScalarField>,
        cs_prover_params: &CS::ProverParams,
        w: &Witness<C>,
        ci: &CommittedInstance<C>,
    ) -> Result<CS::Proof, Error> {
        let e = NIFS::<C, CS, H>::compute_E(&r1cs, &w, &ci.x, ci.mu).unwrap();
        let w_concat_e: Vec<C::ScalarField> = [w.w.clone(), e].concat();
        CS::prove(cs_prover_params, tr, &ci.cmWE, &w_concat_e, &w.rW, None)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::folding::ova::ChallengeGadget;
    use crate::transcript::poseidon::poseidon_canonical_config;
    use crate::{
        arith::{
            r1cs::tests::{get_test_r1cs, get_test_z},
            Arith,
        },
        folding::traits::Dummy,
    };
    use crate::{
        commitment::pedersen::{Params as PedersenParams, Pedersen},
        folding::ova::TestingWitness,
    };
    use ark_crypto_primitives::sponge::{
        poseidon::{PoseidonConfig, PoseidonSponge},
        CryptographicSponge,
    };
    use ark_ff::{BigInteger, PrimeField};
    use ark_pallas::{Fr, Projective};
    use ark_std::{test_rng, UniformRand, Zero};

    fn compute_E_check_relation<C: CurveGroup, CS: CommitmentScheme<C, H>, const H: bool>(
        r1cs: &R1CS<C::ScalarField>,
        w: &Witness<C>,
        u: &CommittedInstance<C>,
    ) where
        <C as Group>::ScalarField: Absorb,
    {
        let e = NIFS::<C, CS, H>::compute_E(&r1cs, &w, &u.x, u.mu).unwrap();
        r1cs.check_relation(
            &TestingWitness::<C> {
                e,
                w: w.clone().w,
                rW: w.rW,
            },
            &u,
        )
        .unwrap();
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn prepare_simple_fold_inputs<C>() -> (
        PedersenParams<C>,
        PoseidonConfig<C::ScalarField>,
        R1CS<C::ScalarField>,
        Witness<C>,           // w1
        CommittedInstance<C>, // ci1
        Witness<C>,           // w2
        CommittedInstance<C>, // ci2
        Witness<C>,           // w3
        CommittedInstance<C>, // ci3
        Vec<bool>,            // r_bits
        C::ScalarField,       // r_Fr
    )
    where
        C: CurveGroup,
        <C as CurveGroup>::BaseField: PrimeField,
        C::ScalarField: Absorb,
    {
        // Index 1 represents the incomming instance
        // Index 2 represents the accumulated instance
        let r1cs = get_test_r1cs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);
        let (w1, x1) = r1cs.split_z(&z1);
        let (w2, x2) = r1cs.split_z(&z2);

        let w1 = Witness::<C>::new::<false>(w1.clone(), test_rng());
        let w2 = Witness::<C>::new::<false>(w2.clone(), test_rng());

        let mut rng = ark_std::test_rng();
        let (pedersen_params, _) = Pedersen::<C>::setup(&mut rng, r1cs.A.n_cols).unwrap();

        // In order to be able to compute the committed instances, we need to compute `t` and `e`
        // compute t
        let t = NIFS::<C, Pedersen<C>>::compute_T(&r1cs, &w1, &x1, &w2, &x2, C::ScalarField::one())
            .unwrap();
        // compute e (mu is 1 although is the running instance as we are "crafting it").
        let e = NIFS::<C, Pedersen<C>>::compute_E(&r1cs, &w1, &x1, C::ScalarField::one()).unwrap();
        // compute committed instances
        let W_prime = w1
            .commit::<Pedersen<C>, false>(&pedersen_params, e, x1.clone())
            .unwrap();
        let W = w2
            .commit::<Pedersen<C>, false>(&pedersen_params, t, x2.clone())
            .unwrap();

        let poseidon_config = poseidon_canonical_config::<C::ScalarField>();
        let mut transcript = PoseidonSponge::<C::ScalarField>::new(&poseidon_config);

        let pp_hash = C::ScalarField::from(42u32); // only for test

        let alpha_bits = ChallengeGadget::<C>::get_challenge_native(
            &mut transcript,
            pp_hash,
            W_prime.clone(),
            W.clone(),
        );
        let alpha_Fr = C::ScalarField::from_bigint(BigInteger::from_bits_le(&alpha_bits)).unwrap();

        let (w3, ci3) =
            NIFS::<C, Pedersen<C>>::fold_instances(alpha_Fr, &w1, &W_prime, &w2, &W).unwrap();

        (
            pedersen_params,
            poseidon_config,
            r1cs,
            w1,
            W_prime,
            w2,
            W,
            w3,
            ci3,
            alpha_bits,
            alpha_Fr,
        )
    }

    // fold 2 dummy instances and check that the folded instance holds the relaxed R1CS relation
    #[test]
    fn test_nifs_fold_dummy() {
        let mut rng = ark_std::test_rng();
        let r1cs = get_test_r1cs::<Fr>();

        let w_dummy = Witness::<Projective>::dummy(&r1cs);

        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, r1cs.A.n_cols).unwrap();

        // In order to be able to compute the committed instances, we need to compute `t` and `e`
        // compute t
        let t = NIFS::<Projective, Pedersen<Projective>>::compute_T(
            &r1cs,
            &w_dummy,
            &[Fr::zero()],
            &w_dummy,
            &[Fr::zero()],
            Fr::one(),
        )
        .unwrap();
        // compute e
        let e = NIFS::<Projective, Pedersen<Projective>>::compute_E(
            &r1cs,
            &w_dummy,
            &[Fr::zero()],
            Fr::one(),
        )
        .unwrap();

        // dummy incoming instance, witness and public inputs
        let u_dummy = w_dummy
            .commit::<Pedersen<Projective>, false>(&pedersen_params, t, vec![Fr::zero()])
            .unwrap();

        // dummy accumulated instance, witness and public inputs
        let U_dummy = w_dummy
            .commit::<Pedersen<Projective>, false>(&pedersen_params, e.clone(), vec![Fr::zero()])
            .unwrap();

        let w_i = w_dummy.clone();
        let u_i = u_dummy.clone();
        let W_i = w_dummy.clone();
        let U_i = U_dummy.clone();
        r1cs.check_relation(
            &TestingWitness {
                w: w_i.clone().w,
                e: e.clone(),
                rW: w_i.rW,
            },
            &u_i,
        )
        .unwrap();
        r1cs.check_relation(
            &TestingWitness {
                w: W_i.clone().w,
                e,
                rW: W_i.rW,
            },
            &U_i,
        )
        .unwrap();

        // NIFS.P
        let r_Fr = Fr::from(3_u32);

        let (W_i1, U_i1) =
            NIFS::<Projective, Pedersen<Projective>>::fold_instances(r_Fr, &W_i, &U_i, &w_i, &u_i)
                .unwrap();

        // Compute e for the folded instance to be able to check the relation.
        let folded_e =
            NIFS::<Projective, Pedersen<Projective>>::compute_E(&r1cs, &W_i1, &U_i1.x, U_i1.mu)
                .unwrap();
        r1cs.check_relation(
            &TestingWitness {
                w: W_i1.w,
                e: folded_e,
                rW: W_i1.rW,
            },
            &U_i1,
        )
        .unwrap();
    }

    // fold 2 instances into one
    #[test]
    fn test_nifs_one_fold() {
        let (pedersen_params, poseidon_config, r1cs, w1, ci1, w2, ci2, w3, ci3, _, r) =
            prepare_simple_fold_inputs();

        // NIFS.V
        let ci3_v = NIFS::<Projective, Pedersen<Projective>>::verify(r, &ci1, &ci2);
        assert_eq!(ci3_v, ci3);

        // check that relations hold for the 2 inputted instances and the folded one
        compute_E_check_relation::<Projective, Pedersen<Projective>, false>(&r1cs, &w1, &ci1);
        compute_E_check_relation::<Projective, Pedersen<Projective>, false>(&r1cs, &w2, &ci2);
        compute_E_check_relation::<Projective, Pedersen<Projective>, false>(&r1cs, &w3, &ci3);

        // check that folded commitments from folded instance (ci) are equal to folding the
        // use folded rW to commit w3
        let e = NIFS::<Projective, Pedersen<Projective>>::compute_E(&r1cs, &w3, &ci3.x, ci3.mu)
            .unwrap();
        let mut ci3_expected = w3
            .commit::<Pedersen<Projective>, false>(&pedersen_params, e, ci3.x.clone())
            .unwrap();
        ci3_expected.mu = ci3.mu;

        assert_eq!(ci3_expected.cmWE, ci3.cmWE);

        // NIFS.Verify_Folded_Instance:
        NIFS::<Projective, Pedersen<Projective>>::verify_folded_instance(r, &ci1, &ci2, &ci3)
            .unwrap();

        // init Prover's transcript
        let mut transcript_p = PoseidonSponge::<Fr>::new(&poseidon_config);
        // init Verifier's transcript
        let mut transcript_v = PoseidonSponge::<Fr>::new(&poseidon_config);

        // prove the ci3.cmWE
        let cm_proof = NIFS::<Projective, Pedersen<Projective>>::prove_commitment(
            &r1cs,
            &mut transcript_p,
            &pedersen_params,
            &w3,
            &ci3,
        )
        .unwrap();

        // verify the ci3.cmWE.
        Pedersen::<Projective>::verify(&pedersen_params, &mut transcript_v, &ci3.cmWE, &cm_proof)
            .unwrap();
    }

    #[test]
    fn test_nifs_fold_loop() {
        let r1cs = get_test_r1cs();
        let z = get_test_z(3);
        let (w, x) = r1cs.split_z(&z);

        let mut rng = ark_std::test_rng();
        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, r1cs.A.n_cols).unwrap();

        // prepare the running instance
        let mut running_instance_w = Witness::<Projective>::new::<false>(w.clone(), &mut rng);
        // Compute e
        let e = NIFS::<Projective, Pedersen<Projective>>::compute_E(
            &r1cs,
            &running_instance_w,
            &x,
            Fr::one(),
        )
        .unwrap();
        let mut running_committed_instance = running_instance_w
            .commit::<Pedersen<Projective>, false>(&pedersen_params, e, x)
            .unwrap();

        let num_iters = 10;
        for i in 0..num_iters {
            // prepare the incoming instance
            let incoming_instance_z = get_test_z(i + 4);
            let (w, x) = r1cs.split_z(&incoming_instance_z);
            let incoming_instance_w = Witness::<Projective>::new::<false>(w.clone(), test_rng());
            let t = NIFS::<Projective, Pedersen<Projective>>::compute_T(
                &r1cs,
                &running_instance_w,
                &running_committed_instance.x,
                &incoming_instance_w,
                &x,
                running_committed_instance.mu,
            )
            .unwrap();
            let incoming_committed_instance = incoming_instance_w
                .commit::<Pedersen<Projective>, false>(&pedersen_params, t, x)
                .unwrap();

            compute_E_check_relation::<Projective, Pedersen<Projective>, false>(
                &r1cs,
                &incoming_instance_w,
                &incoming_committed_instance,
            );

            let alpha = Fr::rand(&mut rng); // folding challenge would come from the RO

            // NIFS.P
            let (folded_w, _) = NIFS::<Projective, Pedersen<Projective>>::fold_instances(
                alpha,
                &running_instance_w,
                &running_committed_instance,
                &incoming_instance_w,
                &incoming_committed_instance,
            )
            .unwrap();

            // NIFS.V
            let folded_committed_instance = NIFS::<Projective, Pedersen<Projective>>::verify(
                alpha,
                &running_committed_instance,
                &incoming_committed_instance,
            );

            compute_E_check_relation::<Projective, Pedersen<Projective>, false>(
                &r1cs,
                &folded_w,
                &folded_committed_instance,
            );

            // set running_instance for next loop iteration
            running_instance_w = folded_w;
            running_committed_instance = folded_committed_instance;
        }
    }
}
