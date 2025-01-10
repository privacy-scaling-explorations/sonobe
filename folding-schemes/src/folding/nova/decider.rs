/// This file implements the offchain decider. For ethereum use cases, use the
/// DeciderEth from decider_eth.rs file.
/// More details can be found at the documentation page:
/// https://privacy-scaling-explorations.github.io/sonobe-docs/design/nova-decider-offchain.html
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_snark::SNARK;
use ark_std::rand::{CryptoRng, RngCore};
use ark_std::{One, Zero};
use core::marker::PhantomData;

use super::decider_circuits::{DeciderCircuit1, DeciderCircuit2};
use super::decider_eth_circuit::DeciderNovaGadget;
use super::Nova;
use crate::commitment::CommitmentScheme;
use crate::folding::circuits::cyclefold::CycleFoldCommittedInstance;
use crate::folding::circuits::decider::DeciderEnabledNIFS;
use crate::folding::traits::{
    CommittedInstanceOps, Dummy, Inputize, InputizeNonNative, WitnessOps,
};
use crate::frontend::FCircuit;
use crate::transcript::poseidon::poseidon_canonical_config;
use crate::{Curve, Error};
use crate::{Decider as DeciderTrait, FoldingScheme};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Proof<C1, C2, CS1, CS2, S1, S2>
where
    C1: Curve,
    C2: Curve,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
    S1: SNARK<C1::ScalarField>,
    S2: SNARK<C2::ScalarField>,
{
    c1_snark_proof: S1::Proof,
    c2_snark_proof: S2::Proof,
    cs1_proofs: [CS1::Proof; 2],
    cs2_proofs: [CS2::Proof; 2],
    // cmT and r are values for the last fold, U_{i+1}=NIFS.V(r, U_i, u_i, cmT), and they are
    // checked in-circuit
    cmT: C1,
    r: C1::ScalarField,
    // cyclefold committed instance
    cf_U_final: CycleFoldCommittedInstance<C2>,
    // the CS challenges are provided by the prover, but in-circuit they are checked to match the
    // in-circuit computed computed ones.
    cs1_challenges: [C1::ScalarField; 2],
    cs2_challenges: [C2::ScalarField; 2],
}

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProverParam<CS1_ProvingKey, S1_ProvingKey, CS2_ProvingKey, S2_ProvingKey>
where
    CS1_ProvingKey: Clone + CanonicalSerialize + CanonicalDeserialize,
    S1_ProvingKey: Clone + CanonicalSerialize + CanonicalDeserialize,
    CS2_ProvingKey: Clone + CanonicalSerialize + CanonicalDeserialize,
    S2_ProvingKey: Clone + CanonicalSerialize + CanonicalDeserialize,
{
    pub c1_snark_pp: S1_ProvingKey,
    pub c1_cs_pp: CS1_ProvingKey,
    pub c2_snark_pp: S2_ProvingKey,
    pub c2_cs_pp: CS2_ProvingKey,
}

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifierParam<C1, CS1_VerifyingKey, S1_VerifyingKey, CS2_VerifyingKey, S2_VerifyingKey>
where
    C1: Curve,
    CS1_VerifyingKey: Clone + CanonicalSerialize + CanonicalDeserialize,
    S1_VerifyingKey: Clone + CanonicalSerialize + CanonicalDeserialize,
    CS2_VerifyingKey: Clone + CanonicalSerialize + CanonicalDeserialize,
    S2_VerifyingKey: Clone + CanonicalSerialize + CanonicalDeserialize,
{
    pub pp_hash: C1::ScalarField,
    pub c1_snark_vp: S1_VerifyingKey,
    pub c1_cs_vp: CS1_VerifyingKey,
    pub c2_snark_vp: S2_VerifyingKey,
    pub c2_cs_vp: CS2_VerifyingKey,
}

/// Onchain Decider, for ethereum use cases
#[derive(Clone, Debug)]
pub struct Decider<C1, C2, FC, CS1, CS2, S1, S2, FS> {
    _c1: PhantomData<C1>,
    _c2: PhantomData<C2>,
    _fc: PhantomData<FC>,
    _cs1: PhantomData<CS1>,
    _cs2: PhantomData<CS2>,
    _s1: PhantomData<S1>,
    _s2: PhantomData<S2>,
    _fs: PhantomData<FS>,
}

impl<C1, C2, FC, CS1, CS2, S1, S2, FS> DeciderTrait<C1, C2, FC, FS>
    for Decider<C1, C2, FC, CS1, CS2, S1, S2, FS>
where
    C1: Curve<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    C2: Curve,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<
        C1,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = crate::commitment::kzg::Proof<C1>,
    >,
    CS2: CommitmentScheme<
        C2,
        ProverChallenge = C2::ScalarField,
        Challenge = C2::ScalarField,
        Proof = crate::commitment::kzg::Proof<C2>,
    >,
    S1: SNARK<C1::ScalarField>,
    S2: SNARK<C2::ScalarField>,
    FS: FoldingScheme<C1, C2, FC>,
    // constrain FS into Nova, since this is a Decider specifically for Nova
    Nova<C1, C2, FC, CS1, CS2, false>: From<FS>,
    crate::folding::nova::ProverParams<C1, C2, CS1, CS2, false>:
        From<<FS as FoldingScheme<C1, C2, FC>>::ProverParam>,
    crate::folding::nova::VerifierParams<C1, C2, CS1, CS2, false>:
        From<<FS as FoldingScheme<C1, C2, FC>>::VerifierParam>,
{
    type PreprocessorParam = ((FS::ProverParam, FS::VerifierParam), usize);
    type ProverParam =
        ProverParam<CS1::ProverParams, S1::ProvingKey, CS2::ProverParams, S2::ProvingKey>;
    type Proof = Proof<C1, C2, CS1, CS2, S1, S2>;
    type VerifierParam = VerifierParam<
        C1,
        CS1::VerifierParams,
        S1::VerifyingKey,
        CS2::VerifierParams,
        S2::VerifyingKey,
    >;
    type PublicInput = Vec<C1::ScalarField>;
    type CommittedInstance = Vec<C1>;

    fn preprocess(
        mut rng: impl RngCore + CryptoRng,
        ((pp, vp), state_len): Self::PreprocessorParam,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        // get the FoldingScheme prover & verifier params from Nova
        let nova_pp: <Nova<C1, C2, FC, CS1, CS2, false> as FoldingScheme<C1, C2, FC>>::ProverParam =
            pp.into();
        let nova_vp: <Nova<C1, C2, FC, CS1, CS2, false> as FoldingScheme<
            C1,
            C2,
            FC,
        >>::VerifierParam = vp.into();
        let pp_hash = nova_vp.pp_hash()?;

        let circuit1 = DeciderCircuit1::<C1, C2>::dummy((
            nova_vp.r1cs,
            &nova_vp.cf_r1cs,
            nova_vp.poseidon_config,
            (),
            (),
            state_len,
            2, // Nova's running CommittedInstance contains 2 commitments
        ));
        let circuit2 = DeciderCircuit2::<C2>::dummy((
            nova_vp.cf_r1cs,
            poseidon_canonical_config::<C2::ScalarField>(),
            2, // Nova's running CommittedInstance contains 2 commitments
        ));

        // get the Groth16 specific setup for the circuits
        let (c1_g16_pk, c1_g16_vk) = S1::circuit_specific_setup(circuit1, &mut rng)
            .map_err(|e| Error::SNARKSetupFail(e.to_string()))?;
        let (c2_g16_pk, c2_g16_vk) = S2::circuit_specific_setup(circuit2, &mut rng)
            .map_err(|e| Error::SNARKSetupFail(e.to_string()))?;

        let pp = Self::ProverParam {
            c1_snark_pp: c1_g16_pk,
            c1_cs_pp: nova_pp.cs_pp,
            c2_snark_pp: c2_g16_pk,
            c2_cs_pp: nova_pp.cf_cs_pp,
        };
        let vp = Self::VerifierParam {
            pp_hash,
            c1_snark_vp: c1_g16_vk,
            c1_cs_vp: nova_vp.cs_vp,
            c2_snark_vp: c2_g16_vk,
            c2_cs_vp: nova_vp.cf_cs_vp,
        };
        Ok((pp, vp))
    }

    fn prove(
        mut rng: impl RngCore + CryptoRng,
        pp: Self::ProverParam,
        fs: FS,
    ) -> Result<Self::Proof, Error> {
        let circuit1 = DeciderCircuit1::<C1, C2>::try_from(Nova::from(fs.clone()))?;
        let circuit2 = DeciderCircuit2::<C2>::try_from(Nova::from(fs))?;

        let cmT = circuit1.proof;
        let r = circuit1.randomness;
        let cf_U_final = circuit1.cf_U_i.clone();

        let c1_kzg_challenges = circuit1.kzg_challenges.clone();
        let c1_kzg_proofs = circuit1
            .W_i1
            .get_openings()
            .iter()
            .zip(&c1_kzg_challenges)
            .map(|((v, _), &c)| {
                CS1::prove_with_challenge(&pp.c1_cs_pp, c, v, &C1::ScalarField::zero(), None)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let c2_kzg_challenges = circuit2.kzg_challenges.clone();
        let c2_kzg_proofs = circuit2
            .cf_W_i
            .get_openings()
            .iter()
            .zip(&c2_kzg_challenges)
            .map(|((v, _), &c)| {
                CS2::prove_with_challenge(&pp.c2_cs_pp, c, v, &C2::ScalarField::zero(), None)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let c1_snark_proof = S1::prove(&pp.c1_snark_pp, circuit1, &mut rng)
            .map_err(|e| Error::Other(e.to_string()))?;
        let c2_snark_proof = S2::prove(&pp.c2_snark_pp, circuit2, &mut rng)
            .map_err(|e| Error::Other(e.to_string()))?;

        Ok(Self::Proof {
            c1_snark_proof,
            c2_snark_proof,
            cs1_proofs: c1_kzg_proofs
                .try_into()
                .map_err(|e: Vec<_>| Error::NotExpectedLength(e.len(), 2))?,
            cs2_proofs: c2_kzg_proofs
                .try_into()
                .map_err(|e: Vec<_>| Error::NotExpectedLength(e.len(), 2))?,
            cmT,
            r,
            cf_U_final,
            cs1_challenges: c1_kzg_challenges
                .try_into()
                .map_err(|e: Vec<_>| Error::NotExpectedLength(e.len(), 2))?,
            cs2_challenges: c2_kzg_challenges
                .try_into()
                .map_err(|e: Vec<_>| Error::NotExpectedLength(e.len(), 2))?,
        })
    }

    fn verify(
        vp: Self::VerifierParam,
        i: C1::ScalarField,
        z_0: Vec<C1::ScalarField>,
        z_i: Vec<C1::ScalarField>,
        // we don't use the instances at the verifier level, since we check them in-circuit
        running_commitments: &Self::CommittedInstance,
        incoming_commitments: &Self::CommittedInstance,
        proof: &Self::Proof,
    ) -> Result<bool, Error> {
        if i <= C1::ScalarField::one() {
            return Err(Error::NotEnoughSteps);
        }

        // 6.2. Fold the commitments
        let U_final_commitments = DeciderNovaGadget::fold_group_elements_native(
            running_commitments,
            incoming_commitments,
            Some(proof.cmT),
            proof.r,
        )?;
        let cf_U = proof.cf_U_final.clone();

        // snark proof 1
        let c1_public_input = [
            &[vp.pp_hash, i][..],
            &z_0,
            &z_i,
            &U_final_commitments.inputize_nonnative(),
            &cf_U.inputize_nonnative(),
            &proof.cs1_challenges,
            &proof.cs1_proofs.iter().map(|p| p.eval).collect::<Vec<_>>(),
            &proof.cmT.inputize_nonnative(),
        ]
        .concat();

        let c1_snark_v = S1::verify(&vp.c1_snark_vp, &c1_public_input, &proof.c1_snark_proof)
            .map_err(|e| Error::Other(e.to_string()))?;
        if !c1_snark_v {
            return Err(Error::SNARKVerificationFail);
        }

        // snark proof 2
        // migrate pp_hash from C1::Fr to C1::Fq
        let pp_hash_Fq =
            C2::ScalarField::from_le_bytes_mod_order(&vp.pp_hash.into_bigint().to_bytes_le());
        let c2_public_input: Vec<C2::ScalarField> = [
            &[pp_hash_Fq][..],
            &cf_U.inputize(),
            &proof.cs2_challenges,
            &proof.cs2_proofs.iter().map(|p| p.eval).collect::<Vec<_>>(),
        ]
        .concat();

        let c2_snark_v = S2::verify(&vp.c2_snark_vp, &c2_public_input, &proof.c2_snark_proof)
            .map_err(|e| Error::Other(e.to_string()))?;
        if !c2_snark_v {
            return Err(Error::SNARKVerificationFail);
        }

        // 7.3. check C1 commitments (main instance commitments)
        for ((cm, &c), pi) in U_final_commitments
            .iter()
            .zip(&proof.cs1_challenges)
            .zip(&proof.cs1_proofs)
        {
            CS1::verify_with_challenge(&vp.c1_cs_vp, c, cm, pi)?;
        }

        // 4.3. check C2 commitments (CycleFold instance commitments)
        for ((cm, &c), pi) in cf_U
            .get_commitments()
            .iter()
            .zip(&proof.cs2_challenges)
            .zip(&proof.cs2_proofs)
        {
            CS2::verify_with_challenge(&vp.c2_cs_vp, c, cm, pi)?;
        }

        Ok(true)
    }
}

#[cfg(test)]
pub mod tests {
    use ark_groth16::Groth16;

    // Note: do not use the MNTx_298 curves in practice, these are just for tests. Use the MNTx_753
    // curves instead.
    use ark_mnt4_298::{Fr, G1Projective as Projective, MNT4_298 as MNT4};
    use ark_mnt6_298::{G1Projective as Projective2, MNT6_298 as MNT6};
    use std::time::Instant;

    use super::*;
    use crate::commitment::kzg::KZG;
    use crate::folding::nova::PreprocessorParam;
    use crate::frontend::utils::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_canonical_config;

    #[test]
    fn test_decider() -> Result<(), Error> {
        // use Nova as FoldingScheme
        type N = Nova<
            Projective,
            Projective2,
            CubicFCircuit<Fr>,
            KZG<'static, MNT4>,
            KZG<'static, MNT6>,
            false,
        >;
        type D = Decider<
            Projective,
            Projective2,
            CubicFCircuit<Fr>,
            KZG<'static, MNT4>,
            KZG<'static, MNT6>,
            Groth16<MNT4>,
            Groth16<MNT6>,
            N, // here we define the FoldingScheme to use
        >;

        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(())?;
        let z_0 = vec![Fr::from(3_u32)];

        let start = Instant::now();
        let prep_param = PreprocessorParam::new(poseidon_config, F_circuit);
        let nova_params = N::preprocess(&mut rng, &prep_param)?;
        println!("Nova preprocess, {:?}", start.elapsed());

        let start = Instant::now();
        let mut nova = N::init(&nova_params, F_circuit, z_0.clone())?;
        println!("Nova initialized, {:?}", start.elapsed());
        let start = Instant::now();
        nova.prove_step(&mut rng, (), None)?;
        println!("prove_step, {:?}", start.elapsed());
        nova.prove_step(&mut rng, (), None)?; // do a 2nd step

        let mut rng = rand::rngs::OsRng;

        // prepare the Decider prover & verifier params
        let start = Instant::now();
        let (decider_pp, decider_vp) =
            D::preprocess(&mut rng, (nova_params, F_circuit.state_len()))?;
        println!("Decider preprocess, {:?}", start.elapsed());

        // decider proof generation
        let start = Instant::now();
        let proof = D::prove(rng, decider_pp, nova.clone())?;
        println!("Decider prove, {:?}", start.elapsed());

        // decider proof verification
        let start = Instant::now();
        let verified = D::verify(
            decider_vp,
            nova.i,
            nova.z_0,
            nova.z_i,
            &nova.U_i.get_commitments(),
            &nova.u_i.get_commitments(),
            &proof,
        )?;
        assert!(verified);
        println!("Decider verify, {:?}", start.elapsed());
        Ok(())
    }
}
