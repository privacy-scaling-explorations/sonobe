/// This file implements the offchain decider. For ethereum use cases, use the
/// DeciderEth from decider_eth.rs file.
/// More details can be found at the documentation page:
/// https://privacy-scaling-explorations.github.io/sonobe-docs/design/nova-decider-offchain.html
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{AffineRepr, CurveGroup, Group};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{groups::GroupOpsBounds, prelude::CurveVar, ToConstraintFieldGadget};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_snark::SNARK;
use ark_std::rand::{CryptoRng, RngCore};
use ark_std::{One, Zero};
use core::marker::PhantomData;

use super::decider_circuits::{DeciderCircuit1, DeciderCircuit2};
use super::{nifs::NIFS, traits::NIFSTrait, CommittedInstance, Nova};
use crate::commitment::CommitmentScheme;
use crate::folding::circuits::{
    cyclefold::CycleFoldCommittedInstance,
    nonnative::{affine::NonNativeAffineVar, uint::NonNativeUintVar},
    CF2,
};
use crate::frontend::FCircuit;
use crate::Error;
use crate::{Decider as DeciderTrait, FoldingScheme};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Proof<C1, C2, CS1, CS2, S1, S2>
where
    C1: CurveGroup,
    C2: CurveGroup,
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
    cf_U_i: CycleFoldCommittedInstance<C2>,
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
    C1: CurveGroup,
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
pub struct Decider<C1, GC1, C2, GC2, FC, CS1, CS2, S1, S2, FS> {
    _c1: PhantomData<C1>,
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,
    _fc: PhantomData<FC>,
    _cs1: PhantomData<CS1>,
    _cs2: PhantomData<CS2>,
    _s1: PhantomData<S1>,
    _s2: PhantomData<S2>,
    _fs: PhantomData<FS>,
}

impl<C1, GC1, C2, GC2, FC, CS1, CS2, S1, S2, FS> DeciderTrait<C1, C2, FC, FS>
    for Decider<C1, GC1, C2, GC2, FC, CS1, CS2, S1, S2, FS>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
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
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'b> &'b GC1: GroupOpsBounds<'b, C1, GC1>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
    // constrain FS into Nova, since this is a Decider specifically for Nova
    Nova<C1, GC1, C2, GC2, FC, CS1, CS2, false>: From<FS>,
    crate::folding::nova::ProverParams<C1, C2, CS1, CS2, false>:
        From<<FS as FoldingScheme<C1, C2, FC>>::ProverParam>,
    crate::folding::nova::VerifierParams<C1, C2, CS1, CS2, false>:
        From<<FS as FoldingScheme<C1, C2, FC>>::VerifierParam>,
{
    type PreprocessorParam = (FS::ProverParam, FS::VerifierParam);
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
    type CommittedInstance = CommittedInstance<C1>;

    fn preprocess(
        mut rng: impl RngCore + CryptoRng,
        prep_param: Self::PreprocessorParam,
        fs: FS,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        let circuit1 = DeciderCircuit1::<C1, C2, GC2>::from_nova::<GC1, CS1, CS2, false, FC>(
            fs.clone().into(),
        )?;
        let circuit2 =
            DeciderCircuit2::<C1, GC1, C2>::from_nova::<GC2, CS1, CS2, false, FC>(fs.into())?;

        // get the Groth16 specific setup for the circuits
        let (c1_g16_pk, c1_g16_vk) = S1::circuit_specific_setup(circuit1, &mut rng).unwrap();
        let (c2_g16_pk, c2_g16_vk) = S2::circuit_specific_setup(circuit2, &mut rng).unwrap();

        // get the FoldingScheme prover & verifier params from Nova
        #[allow(clippy::type_complexity)]
        let nova_pp: <Nova<C1, GC1, C2, GC2, FC, CS1, CS2, false> as FoldingScheme<
            C1,
            C2,
            FC,
        >>::ProverParam = prep_param.0.clone().into();
        #[allow(clippy::type_complexity)]
        let nova_vp: <Nova<C1, GC1, C2, GC2, FC, CS1, CS2, false> as FoldingScheme<
            C1,
            C2,
            FC,
        >>::VerifierParam = prep_param.1.clone().into();

        let pp_hash = nova_vp.pp_hash()?;
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
        let circuit1 = DeciderCircuit1::<C1, C2, GC2>::from_nova::<GC1, CS1, CS2, false, FC>(
            fs.clone().into(),
        )?;
        let circuit2 =
            DeciderCircuit2::<C1, GC1, C2>::from_nova::<GC2, CS1, CS2, false, FC>(fs.into())?;

        let c1_snark_proof = S1::prove(&pp.c1_snark_pp, circuit1.clone(), &mut rng)
            .map_err(|e| Error::Other(e.to_string()))?;
        let c2_snark_proof = S2::prove(&pp.c2_snark_pp, circuit2.clone(), &mut rng)
            .map_err(|e| Error::Other(e.to_string()))?;

        let cmT = circuit1.cmT.unwrap();
        let r_Fr = circuit1.r.unwrap();
        let W_i1 = circuit1.W_i1.unwrap();
        let cf_W_i = circuit2.cf_W_i.unwrap();

        // get the challenges that have been already computed when preparing the circuits inputs in
        // the above `from_nova` calls
        let challenge_W = circuit1
            .cs_c_W
            .ok_or(Error::MissingValue("cs_c_W".to_string()))?;
        let challenge_E = circuit1
            .cs_c_E
            .ok_or(Error::MissingValue("cs_c_E".to_string()))?;
        let c2_challenge_W = circuit2
            .cs_c_W
            .ok_or(Error::MissingValue("c2's cs_c_W".to_string()))?;
        let c2_challenge_E = circuit2
            .cs_c_E
            .ok_or(Error::MissingValue("c2's cs_c_E".to_string()))?;

        // generate CommitmentScheme proofs for the main instance
        let U_cmW_proof = CS1::prove_with_challenge(
            &pp.c1_cs_pp,
            challenge_W,
            &W_i1.W,
            &C1::ScalarField::zero(),
            None,
        )?;
        let U_cmE_proof = CS1::prove_with_challenge(
            &pp.c1_cs_pp,
            challenge_E,
            &W_i1.E,
            &C1::ScalarField::zero(),
            None,
        )?;
        // CS proofs for the CycleFold instance
        let cf_cmW_proof = CS2::prove_with_challenge(
            &pp.c2_cs_pp,
            c2_challenge_W,
            &cf_W_i.W,
            &C2::ScalarField::zero(),
            None,
        )?;
        let cf_cmE_proof = CS2::prove_with_challenge(
            &pp.c2_cs_pp,
            c2_challenge_E,
            &cf_W_i.E,
            &C2::ScalarField::zero(),
            None,
        )?;

        Ok(Self::Proof {
            c1_snark_proof,
            c2_snark_proof,
            cs1_proofs: [U_cmW_proof, U_cmE_proof],
            cs2_proofs: [cf_cmW_proof, cf_cmE_proof],
            cmT,
            r: r_Fr,
            cf_U_i: circuit1.cf_U_i.unwrap(),
            cs1_challenges: [challenge_W, challenge_E],
            cs2_challenges: [c2_challenge_W, c2_challenge_E],
        })
    }

    fn verify(
        vp: Self::VerifierParam,
        i: C1::ScalarField,
        z_0: Vec<C1::ScalarField>,
        z_i: Vec<C1::ScalarField>,
        running_instance: &Self::CommittedInstance,
        incoming_instance: &Self::CommittedInstance,
        proof: &Self::Proof,
    ) -> Result<bool, Error> {
        if i <= C1::ScalarField::one() {
            return Err(Error::NotEnoughSteps);
        }

        // compute U = U_{d+1}= NIFS.V(U_d, u_d, cmT)
        let U = NIFS::<C1, CS1>::verify(proof.r, running_instance, incoming_instance, &proof.cmT);

        let (cmE_x, cmE_y) = NonNativeAffineVar::inputize(U.cmE)?;
        let (cmW_x, cmW_y) = NonNativeAffineVar::inputize(U.cmW)?;
        let (cmT_x, cmT_y) = NonNativeAffineVar::inputize(proof.cmT)?;

        let zero = (&C2::BaseField::zero(), &C2::BaseField::zero());
        let cmE_affine = proof.cf_U_i.cmE.into_affine();
        let cmW_affine = proof.cf_U_i.cmW.into_affine();
        let (cf_cmE_x, cf_cmE_y) = cmE_affine.xy().unwrap_or(zero);
        let cf_cmE_z = C1::ScalarField::one();
        let (cf_cmW_x, cf_cmW_y) = cmW_affine.xy().unwrap_or(zero);
        let cf_cmW_z = C1::ScalarField::one();

        // snark proof 1
        let c1_public_input: Vec<C1::ScalarField> = [
            vec![vp.pp_hash, i],
            z_0,
            z_i,
            // U_{i+1} values:
            vec![U.u],
            U.x.clone(),
            cmE_x,
            cmE_y,
            cmW_x,
            cmW_y,
            // CS1 values:
            proof.cs1_challenges.to_vec(), // c_W, c_E
            vec![
                proof.cs1_proofs[0].eval, // eval_W
                proof.cs1_proofs[1].eval, // eval_E
            ],
            // cf_U_i values
            NonNativeUintVar::<CF2<C2>>::inputize(proof.cf_U_i.u),
            proof
                .cf_U_i
                .x
                .iter()
                .flat_map(|&x_i| NonNativeUintVar::<CF2<C2>>::inputize(x_i))
                .collect::<Vec<C1::ScalarField>>(),
            vec![
                *cf_cmE_x, *cf_cmE_y, cf_cmE_z, *cf_cmW_x, *cf_cmW_y, cf_cmW_z,
            ],
            // NIFS values:
            cmT_x,
            cmT_y,
            vec![proof.r],
        ]
        .concat();

        let c1_snark_v = S1::verify(&vp.c1_snark_vp, &c1_public_input, &proof.c1_snark_proof)
            .map_err(|e| Error::Other(e.to_string()))?;
        if !c1_snark_v {
            return Err(Error::SNARKVerificationFail);
        }

        let (cf2_cmE_x, cf2_cmE_y) = NonNativeAffineVar::inputize(proof.cf_U_i.cmE)?;
        let (cf2_cmW_x, cf2_cmW_y) = NonNativeAffineVar::inputize(proof.cf_U_i.cmW)?;

        // snark proof 2
        // migrate pp_hash from C1::Fr to C1::Fq
        let pp_hash_Fq =
            C2::ScalarField::from_le_bytes_mod_order(&vp.pp_hash.into_bigint().to_bytes_le());
        let c2_public_input: Vec<C2::ScalarField> = [
            vec![pp_hash_Fq],
            vec![proof.cf_U_i.u],
            proof.cf_U_i.x.clone(),
            cf2_cmE_x,
            cf2_cmE_y,
            cf2_cmW_x,
            cf2_cmW_y,
            proof.cs2_challenges.to_vec(),
            vec![
                proof.cs2_proofs[0].eval, // eval_W
                proof.cs2_proofs[1].eval, // eval_E
            ],
        ]
        .concat();

        let c2_snark_v = S2::verify(&vp.c2_snark_vp, &c2_public_input, &proof.c2_snark_proof)
            .map_err(|e| Error::Other(e.to_string()))?;
        if !c2_snark_v {
            return Err(Error::SNARKVerificationFail);
        }

        // check C1 commitments (main instance commitments)
        CS1::verify_with_challenge(
            &vp.c1_cs_vp,
            proof.cs1_challenges[0],
            &U.cmW,
            &proof.cs1_proofs[0],
        )?;
        CS1::verify_with_challenge(
            &vp.c1_cs_vp,
            proof.cs1_challenges[1],
            &U.cmE,
            &proof.cs1_proofs[1],
        )?;

        // check C2 commitments (CycleFold instance commitments)
        CS2::verify_with_challenge(
            &vp.c2_cs_vp,
            proof.cs2_challenges[0],
            &proof.cf_U_i.cmW,
            &proof.cs2_proofs[0],
        )?;
        CS2::verify_with_challenge(
            &vp.c2_cs_vp,
            proof.cs2_challenges[1],
            &proof.cf_U_i.cmE,
            &proof.cs2_proofs[1],
        )?;

        Ok(true)
    }
}

#[cfg(test)]
pub mod tests {
    use ark_groth16::Groth16;

    // Note: do not use the MNTx_298 curves in practice, these are just for tests. Use the MNTx_753
    // curves instead.
    use ark_mnt4_298::{
        constraints::G1Var as GVar, Fr, G1Projective as Projective, MNT4_298 as MNT4,
    };
    use ark_mnt6_298::{
        constraints::G1Var as GVar2, G1Projective as Projective2, MNT6_298 as MNT6,
    };
    use std::time::Instant;

    use super::*;
    use crate::commitment::kzg::KZG;
    use crate::folding::nova::PreprocessorParam;
    use crate::frontend::utils::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_canonical_config;

    #[test]
    fn test_decider() {
        // use Nova as FoldingScheme
        type N = Nova<
            Projective,
            GVar,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
            KZG<'static, MNT4>,
            KZG<'static, MNT6>,
            false,
        >;
        type D = Decider<
            Projective,
            GVar,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
            KZG<'static, MNT4>,
            KZG<'static, MNT6>,
            Groth16<MNT4>,
            Groth16<MNT6>,
            N, // here we define the FoldingScheme to use
        >;

        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();
        let z_0 = vec![Fr::from(3_u32)];

        let start = Instant::now();
        let prep_param = PreprocessorParam::new(poseidon_config, F_circuit);
        let nova_params = N::preprocess(&mut rng, &prep_param).unwrap();
        println!("Nova preprocess, {:?}", start.elapsed());

        let start = Instant::now();
        let mut nova = N::init(&nova_params, F_circuit, z_0.clone()).unwrap();
        println!("Nova initialized, {:?}", start.elapsed());
        let start = Instant::now();
        nova.prove_step(&mut rng, vec![], None).unwrap();
        println!("prove_step, {:?}", start.elapsed());
        nova.prove_step(&mut rng, vec![], None).unwrap(); // do a 2nd step

        let mut rng = rand::rngs::OsRng;

        // prepare the Decider prover & verifier params
        let start = Instant::now();
        let (decider_pp, decider_vp) = D::preprocess(&mut rng, nova_params, nova.clone()).unwrap();
        println!("Decider preprocess, {:?}", start.elapsed());

        // decider proof generation
        let start = Instant::now();
        let proof = D::prove(rng, decider_pp, nova.clone()).unwrap();
        println!("Decider prove, {:?}", start.elapsed());

        // decider proof verification
        let start = Instant::now();
        let verified = D::verify(
            decider_vp, nova.i, nova.z_0, nova.z_i, &nova.U_i, &nova.u_i, &proof,
        )
        .unwrap();
        assert!(verified);
        println!("Decider verify, {:?}", start.elapsed());
    }
}
