// Implements nova's zero-knowledge layer, as described in https://eprint.iacr.org/2023/573.pdf
use crate::folding::nova::traits::NovaR1CS;
use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_ff::{BigInteger, PrimeField};
use ark_std::{One, Zero};

use crate::{
    arith::r1cs::{RelaxedR1CS, R1CS},
    RngCore,
};
use ark_crypto_primitives::sponge::{
    poseidon::{PoseidonConfig, PoseidonSponge},
    Absorb,
};
use ark_ec::{CurveGroup, Group};
use ark_r1cs_std::{
    groups::{CurveVar, GroupOpsBounds},
    ToConstraintFieldGadget,
};

use crate::{commitment::CommitmentScheme, folding::circuits::CF2, frontend::FCircuit, Error};

use super::{circuits::ChallengeGadget, nifs::NIFS, CommittedInstance, Nova, Witness};

// We use the same definition of a folding proof as in https://eprint.iacr.org/2023/969.pdf
// It consists in the commitment to the T term
pub struct FoldingProof<C: CurveGroup> {
    cmT: C,
}

pub struct RandomizedIVCProof<C1: CurveGroup, C2: CurveGroup> {
    pub U_i: CommittedInstance<C1>,
    pub u_i: CommittedInstance<C1>,
    pub U_r: CommittedInstance<C1>,
    pub pi: FoldingProof<C1>,
    pub pi_prime: FoldingProof<C1>,
    pub W_i_prime: Witness<C1>,
    pub cf_U_i: CommittedInstance<C2>,
    pub cf_W_i: Witness<C2>,
}

impl<C1: CurveGroup, C2: CurveGroup> RandomizedIVCProof<C1, C2>
where
    <C1 as Group>::ScalarField: Absorb,
    <C1 as CurveGroup>::BaseField: PrimeField,
{
    /// Computes challenge required before folding instances
    fn get_folding_challenge(
        sponge: &mut PoseidonSponge<C1::ScalarField>,
        pp_hash: C1::ScalarField,
        U_i: CommittedInstance<C1>,
        u_i: CommittedInstance<C1>,
        cmT: C1,
    ) -> Result<C1::ScalarField, Error> {
        let r_bits = ChallengeGadget::<C1>::get_challenge_native(sponge, pp_hash, U_i, u_i, cmT);
        C1::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits)).ok_or(Error::OutOfBounds)
    }

    /// Compute a zero-knowledge proof of a Nova IVC proof
    /// It implements the prover of appendix D.4.in https://eprint.iacr.org/2023/573.pdf
    /// For further details on why folding is hiding, see lemma 9
    pub fn new<
        GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
        GC2: CurveVar<C2, CF2<C2>>,
        FC: FCircuit<C1::ScalarField>,
        CS1: CommitmentScheme<C1, true>,
        CS2: CommitmentScheme<C2, true>,
    >(
        nova: &Nova<C1, GC1, C2, GC2, FC, CS1, CS2, true>,
        mut rng: impl RngCore,
    ) -> Result<RandomizedIVCProof<C1, C2>, Error>
    where
        <C1 as Group>::ScalarField: Absorb,
        <C2 as Group>::ScalarField: Absorb,
        <C2 as Group>::ScalarField: PrimeField,
        <C2 as CurveGroup>::BaseField: PrimeField,
        <C2 as CurveGroup>::BaseField: Absorb,
        for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
        GC2: ToConstraintFieldGadget<<C2 as CurveGroup>::BaseField>,
        C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    {
        let mut challenges_sponge = PoseidonSponge::<C1::ScalarField>::new(&nova.poseidon_config);

        // I. Compute proof for 'regular' instances
        // 1. Fold the instance-witness pairs (U_i, W_i) with (u_i, w_i)
        // a. Compute T
        let (T, cmT) = NIFS::<C1, CS1, true>::compute_cmT(
            &nova.cs_pp,
            &nova.r1cs,
            &nova.w_i,
            &nova.u_i,
            &nova.W_i,
            &nova.U_i,
        )?;

        // b. Compute folding challenge
        let r = RandomizedIVCProof::<C1, C2>::get_folding_challenge(
            &mut challenges_sponge,
            nova.pp_hash,
            nova.U_i.clone(),
            nova.u_i.clone(),
            cmT,
        )?;

        // c. Compute fold
        let (W_f, U_f) = NIFS::<C1, CS1, true>::fold_instances(
            r, &nova.w_i, &nova.u_i, &nova.W_i, &nova.U_i, &T, cmT,
        )?;

        // d. Store folding proof
        let pi = FoldingProof { cmT };

        // 2. Sample a satisfying relaxed R1CS instance-witness pair (U_r, W_r)
        let relaxed_instance = nova.r1cs.clone().relax();
        let (U_r, W_r) = relaxed_instance.sample::<C1, CS1>(&nova.cs_pp, &mut rng)?;

        // 3. Fold the instance-witness pair (U_f, W_f) with (U_r, W_r)
        // a. Compute T
        let (T_i_prime, cmT_i_prime) =
            NIFS::<C1, CS1, true>::compute_cmT(&nova.cs_pp, &nova.r1cs, &W_f, &U_f, &W_r, &U_r)?;

        // b. Compute folding challenge
        let r_2 = RandomizedIVCProof::<C1, C2>::get_folding_challenge(
            &mut challenges_sponge,
            nova.pp_hash,
            U_f.clone(),
            U_r.clone(),
            cmT_i_prime,
        )?;

        // c. Compute fold
        let (W_i_prime, _) = NIFS::<C1, CS1, true>::fold_instances(
            r_2,
            &W_f,
            &U_f,
            &W_r,
            &U_r,
            &T_i_prime,
            cmT_i_prime,
        )?;

        // d. Store folding proof
        let pi_prime = FoldingProof { cmT: cmT_i_prime };

        Ok(RandomizedIVCProof {
            U_i: nova.U_i.clone(),
            u_i: nova.u_i.clone(),
            U_r,
            pi,
            pi_prime,
            W_i_prime,
            cf_U_i: nova.cf_U_i.clone(),
            cf_W_i: nova.cf_W_i.clone(),
        })
    }

    /// Verify a zero-knowledge proof of a Nova IVC proof
    /// It implements the verifier of appendix D.4. in https://eprint.iacr.org/2023/573.pdf
    #[allow(clippy::too_many_arguments)]
    pub fn verify<
        CS1: CommitmentScheme<C1, true>,
        GC2: CurveVar<C2, CF2<C2>>,
        CS2: CommitmentScheme<C2, true>,
    >(
        r1cs: &R1CS<C1::ScalarField>,
        cf_r1cs: &R1CS<C2::ScalarField>,
        pp_hash: C1::ScalarField,
        poseidon_config: &PoseidonConfig<C1::ScalarField>,
        i: C1::ScalarField,
        z_0: Vec<C1::ScalarField>,
        z_i: Vec<C1::ScalarField>,
        proof: &RandomizedIVCProof<C1, C2>,
    ) -> Result<(), Error>
    where
        <C1 as Group>::ScalarField: Absorb,
        <C2 as Group>::ScalarField: Absorb,
        <C2 as CurveGroup>::BaseField: PrimeField,
        <C2 as CurveGroup>::BaseField: Absorb,
        for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
        GC2: ToConstraintFieldGadget<<C2 as CurveGroup>::BaseField>,
        C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    {
        // Handles case where i=0
        if i == C1::ScalarField::zero() {
            if z_0 == z_i {
                return Ok(());
            } else {
                return Err(Error::zkIVCVerificationFail);
            }
        }

        // 1. Check that u_i.x is correct - including the cyclefold running instance
        // a. Check length
        if proof.u_i.x.len() != 2 {
            return Err(Error::IVCVerificationFail);
        }

        // b. Check computed hashes are correct
        let mut sponge = PoseidonSponge::<C1::ScalarField>::new(poseidon_config);
        let expected_u_i_x = proof.U_i.hash(&sponge, pp_hash, i, z_0, z_i);
        if expected_u_i_x != proof.u_i.x[0] {
            return Err(Error::zkIVCVerificationFail);
        }

        let expected_cf_u_i_x = proof.cf_U_i.hash_cyclefold(&sponge, pp_hash);
        if expected_cf_u_i_x != proof.u_i.x[1] {
            return Err(Error::IVCVerificationFail);
        }

        // 2. Check that u_i values are correct
        if !proof.u_i.cmE.is_zero() || proof.u_i.u != C1::ScalarField::one() {
            return Err(Error::zkIVCVerificationFail);
        }

        // 3. Obtain the U_f folded instance
        // a. Compute folding challenge
        let r = RandomizedIVCProof::<C1, C2>::get_folding_challenge(
            &mut sponge,
            pp_hash,
            proof.U_i.clone(),
            proof.u_i.clone(),
            proof.pi.cmT,
        )?;

        // b. Get the U_f instance
        let U_f = NIFS::<C1, CS1, true>::fold_committed_instance(
            r,
            &proof.u_i,
            &proof.U_i,
            &proof.pi.cmT,
        );

        // 4. Obtain the U^{\prime}_i folded instance
        // a. Compute folding challenge
        let r_2 = RandomizedIVCProof::<C1, C2>::get_folding_challenge(
            &mut sponge,
            pp_hash,
            U_f.clone(),
            proof.U_r.clone(),
            proof.pi_prime.cmT,
        )?;

        // b. Compute fold
        let U_i_prime = NIFS::<C1, CS1, true>::fold_committed_instance(
            r_2,
            &U_f,
            &proof.U_r,
            &proof.pi_prime.cmT,
        );

        // 5. Check that W^{\prime}_i is a satisfying witness
        let mut z = vec![U_i_prime.u];
        z.extend(&U_i_prime.x);
        z.extend(&proof.W_i_prime.W);
        let relaxed_r1cs = RelaxedR1CS {
            l: r1cs.l,
            A: r1cs.A.clone(),
            B: r1cs.B.clone(),
            C: r1cs.C.clone(),
            u: U_i_prime.u,
            E: proof.W_i_prime.E.clone(),
        };
        relaxed_r1cs.check_relation(&z)?;

        // 6. Check that the cyclefold instance-witness pair satisfies the cyclefold relaxed r1cs
        cf_r1cs.check_relaxed_instance_relation(&proof.cf_W_i, &proof.cf_U_i)?;

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::tests::test_ivc_opt;
    use crate::frontend::tests::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_canonical_config;
    use ark_bn254::{Fr, G1Projective as Projective};
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
    use rand::rngs::OsRng;

    // Tests zk proof generation and verification for a valid nova IVC proof
    #[test]
    fn test_zk_nova_ivc() {
        let mut rng = OsRng;
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();
        let (_, nova) = test_ivc_opt::<Pedersen<Projective, true>, Pedersen<Projective2, true>, true>(
            poseidon_config.clone(),
            F_circuit,
            3,
        );

        let proof = RandomizedIVCProof::new(&nova, &mut rng).unwrap();
        let verify = RandomizedIVCProof::verify::<
            Pedersen<Projective, true>,
            GVar2,
            Pedersen<Projective2, true>,
        >(
            &nova.r1cs,
            &nova.cf_r1cs,
            nova.pp_hash,
            &nova.poseidon_config,
            nova.i,
            nova.z_0,
            nova.z_i,
            &proof,
        );
        assert!(verify.is_ok());
    }

    #[test]
    fn test_zk_nova_when_i_is_zero() {
        let mut rng = OsRng;
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();
        let (_, nova) = test_ivc_opt::<Pedersen<Projective, true>, Pedersen<Projective2, true>, true>(
            poseidon_config.clone(),
            F_circuit,
            0,
        );

        let proof = RandomizedIVCProof::new(&nova, &mut rng).unwrap();
        let verify = RandomizedIVCProof::verify::<
            Pedersen<Projective, true>,
            GVar2,
            Pedersen<Projective2, true>,
        >(
            &nova.r1cs,
            &nova.cf_r1cs,
            nova.pp_hash,
            &nova.poseidon_config,
            nova.i,
            nova.z_0,
            nova.z_i,
            &proof,
        );
        assert!(verify.is_ok());
    }

    #[test]
    fn test_zk_nova_verification_fails_with_wrong_running_instance() {
        let mut rng = OsRng;
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();
        let (_, nova) = test_ivc_opt::<Pedersen<Projective, true>, Pedersen<Projective2, true>, true>(
            poseidon_config.clone(),
            F_circuit,
            3,
        );
        let (sampled_committed_instance, _) = nova
            .r1cs
            .clone()
            .relax()
            .sample::<Projective, Pedersen<Projective, true>>(&nova.cs_pp, rng)
            .unwrap();

        // proof verification fails with incorrect running instance
        let mut nova_with_incorrect_running_instance = nova.clone();
        nova_with_incorrect_running_instance.U_i = sampled_committed_instance;
        let incorrect_proof =
            RandomizedIVCProof::new(&nova_with_incorrect_running_instance, &mut rng).unwrap();
        let verify = RandomizedIVCProof::verify::<
            Pedersen<Projective, true>,
            GVar2,
            Pedersen<Projective2, true>,
        >(
            &nova_with_incorrect_running_instance.r1cs,
            &nova_with_incorrect_running_instance.cf_r1cs,
            nova_with_incorrect_running_instance.pp_hash,
            &nova_with_incorrect_running_instance.poseidon_config,
            nova_with_incorrect_running_instance.i,
            nova_with_incorrect_running_instance.z_0,
            nova_with_incorrect_running_instance.z_i,
            &incorrect_proof,
        );
        assert!(verify.is_err());
    }

    #[test]
    fn test_zk_nova_verification_fails_with_wrong_running_witness() {
        let mut rng = OsRng;
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();
        let (_, nova) = test_ivc_opt::<Pedersen<Projective, true>, Pedersen<Projective2, true>, true>(
            poseidon_config.clone(),
            F_circuit,
            3,
        );
        let (_, sampled_committed_witness) = nova
            .r1cs
            .clone()
            .relax()
            .sample::<Projective, Pedersen<Projective, true>>(&nova.cs_pp, rng)
            .unwrap();

        // proof generation fails with incorrect running witness
        let mut nova_with_incorrect_running_witness = nova.clone();
        nova_with_incorrect_running_witness.W_i = sampled_committed_witness;
        let incorrect_proof =
            RandomizedIVCProof::new(&nova_with_incorrect_running_witness, &mut rng).unwrap();
        let verify = RandomizedIVCProof::verify::<
            Pedersen<Projective, true>,
            GVar2,
            Pedersen<Projective2, true>,
        >(
            &nova_with_incorrect_running_witness.r1cs,
            &nova_with_incorrect_running_witness.cf_r1cs,
            nova_with_incorrect_running_witness.pp_hash,
            &nova_with_incorrect_running_witness.poseidon_config,
            nova_with_incorrect_running_witness.i,
            nova_with_incorrect_running_witness.z_0,
            nova_with_incorrect_running_witness.z_i,
            &incorrect_proof,
        );
        assert!(verify.is_err());
    }
}
