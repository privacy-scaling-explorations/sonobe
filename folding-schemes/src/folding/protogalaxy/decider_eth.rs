/// This file implements the Protogalaxy's onchain (Ethereum's EVM) decider. For non-ethereum use cases,
/// the Decider from decider.rs file will be more efficient.
/// More details can be found at the documentation page:
/// https://privacy-scaling-explorations.github.io/sonobe-docs/design/nova-decider-onchain.html
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_snark::SNARK;
use ark_std::{
    marker::PhantomData,
    rand::{CryptoRng, RngCore},
    One, Zero,
};

pub use super::decider_eth_circuit::DeciderEthCircuit;
use super::decider_eth_circuit::DeciderProtoGalaxyGadget;
use super::ProtoGalaxy;
use crate::folding::circuits::decider::DeciderEnabledNIFS;
use crate::folding::traits::{Inputize, WitnessOps};
use crate::frontend::FCircuit;
use crate::Error;
use crate::{
    commitment::{kzg::Proof as KZGProof, pedersen::Params as PedersenParams, CommitmentScheme},
    SonobeCurve,
};
use crate::{Decider as DeciderTrait, FoldingScheme};

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<C, CS, S>
where
    C: SonobeCurve,
    CS: CommitmentScheme<C, ProverChallenge = C::ScalarField, Challenge = C::ScalarField>,
    S: SNARK<C::ScalarField>,
{
    snark_proof: S::Proof,
    kzg_proofs: [CS::Proof; 1],
    L_X_evals: Vec<C::ScalarField>,
    // the KZG challenges are provided by the prover, but in-circuit they are checked to match
    // the in-circuit computed computed ones.
    kzg_challenges: [C::ScalarField; 1],
}

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifierParam<C1, CS_VerifyingKey, S_VerifyingKey>
where
    C1: SonobeCurve,
    CS_VerifyingKey: Clone + CanonicalSerialize + CanonicalDeserialize,
    S_VerifyingKey: Clone + CanonicalSerialize + CanonicalDeserialize,
{
    pub pp_hash: C1::ScalarField,
    pub snark_vp: S_VerifyingKey,
    pub cs_vp: CS_VerifyingKey,
}

/// Onchain Decider, for ethereum use cases
#[derive(Clone, Debug)]
pub struct Decider<C1, C2, FC, CS1, CS2, S, FS> {
    _c1: PhantomData<C1>,
    _c2: PhantomData<C2>,
    _fc: PhantomData<FC>,
    _cs1: PhantomData<CS1>,
    _cs2: PhantomData<CS2>,
    _s: PhantomData<S>,
    _fs: PhantomData<FS>,
}

impl<C1, C2, FC, CS1, CS2, S, FS> DeciderTrait<C1, C2, FC, FS>
    for Decider<C1, C2, FC, CS1, CS2, S, FS>
where
    C1: SonobeCurve<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    C2: SonobeCurve,
    FC: FCircuit<C1::ScalarField>,
    // CS1 is a KZG commitment, where challenge is C1::Fr elem
    CS1: CommitmentScheme<
        C1,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >,
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS2: CommitmentScheme<C2, ProverParams = PedersenParams<C2>>,
    S: SNARK<C1::ScalarField>,
    FS: FoldingScheme<C1, C2, FC>,
    // constrain FS into ProtoGalaxy, since this is a Decider specifically for ProtoGalaxy
    ProtoGalaxy<C1, C2, FC, CS1, CS2>: From<FS>,
    crate::folding::protogalaxy::ProverParams<C1, C2, CS1, CS2>:
        From<<FS as FoldingScheme<C1, C2, FC>>::ProverParam>,
    crate::folding::protogalaxy::VerifierParams<C1, C2, CS1, CS2>:
        From<<FS as FoldingScheme<C1, C2, FC>>::VerifierParam>,
{
    type PreprocessorParam = (FS::ProverParam, FS::VerifierParam);
    type ProverParam = (S::ProvingKey, CS1::ProverParams);
    type Proof = Proof<C1, CS1, S>;
    type VerifierParam = VerifierParam<C1, CS1::VerifierParams, S::VerifyingKey>;
    type PublicInput = Vec<C1::ScalarField>;
    type CommittedInstance = Vec<C1>;

    fn preprocess(
        mut rng: impl RngCore + CryptoRng,
        prep_param: Self::PreprocessorParam,
        fs: FS,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        let circuit = DeciderEthCircuit::<C1, C2>::try_from(ProtoGalaxy::from(fs))?;

        // get the Groth16 specific setup for the circuit
        let (g16_pk, g16_vk) = S::circuit_specific_setup(circuit, &mut rng)
            .map_err(|e| Error::SNARKSetupFail(e.to_string()))?;

        // get the FoldingScheme prover & verifier params from ProtoGalaxy
        #[allow(clippy::type_complexity)]
        let protogalaxy_pp: <ProtoGalaxy<C1, C2, FC, CS1, CS2> as FoldingScheme<
            C1,
            C2,
            FC,
        >>::ProverParam = prep_param.0.clone().into();
        #[allow(clippy::type_complexity)]
        let protogalaxy_vp: <ProtoGalaxy<C1, C2, FC, CS1, CS2> as FoldingScheme<
            C1,
            C2,
            FC,
        >>::VerifierParam = prep_param.1.clone().into();
        let pp_hash = protogalaxy_vp.pp_hash()?;

        let pp = (g16_pk, protogalaxy_pp.cs_params);
        let vp = Self::VerifierParam {
            pp_hash,
            snark_vp: g16_vk,
            cs_vp: protogalaxy_vp.cs_vp,
        };
        Ok((pp, vp))
    }

    fn prove(
        mut rng: impl RngCore + CryptoRng,
        pp: Self::ProverParam,
        folding_scheme: FS,
    ) -> Result<Self::Proof, Error> {
        let (snark_pk, cs_pk): (S::ProvingKey, CS1::ProverParams) = pp;

        let circuit = DeciderEthCircuit::<C1, C2>::try_from(ProtoGalaxy::from(folding_scheme))?;

        let L_X_evals = circuit.randomness.clone();

        // get the challenges that have been already computed when preparing the circuit inputs in
        // the above `try_from` call
        let kzg_challenges = circuit.kzg_challenges.clone();

        // generate KZG proofs
        let kzg_proofs = circuit
            .W_i1
            .get_openings()
            .iter()
            .zip(&kzg_challenges)
            .map(|((v, _), &c)| {
                CS1::prove_with_challenge(&cs_pk, c, v, &C1::ScalarField::zero(), None)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let snark_proof =
            S::prove(&snark_pk, circuit, &mut rng).map_err(|e| Error::Other(e.to_string()))?;

        Ok(Self::Proof {
            snark_proof,
            L_X_evals,
            kzg_proofs: kzg_proofs.try_into().map_err(|_| {
                Error::ConversionError(
                    "Vec<_>".to_string(),
                    "[_; 1]".to_string(),
                    "variable name: kzg_proofs".to_string(),
                )
            })?,
            kzg_challenges: kzg_challenges.try_into().map_err(|_| {
                Error::ConversionError(
                    "Vec<_>".to_string(),
                    "[_; 1]".to_string(),
                    "variable name: kzg_challenges".to_string(),
                )
            })?,
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

        let Self::VerifierParam {
            pp_hash,
            snark_vp,
            cs_vp,
        } = vp;

        // 6.2. Fold the commitments
        let U_final_commitments = DeciderProtoGalaxyGadget::fold_group_elements_native(
            running_commitments,
            incoming_commitments,
            None,
            proof.L_X_evals.clone(),
        )?;

        let public_input = [
            &[pp_hash, i][..],
            &z_0,
            &z_i,
            &U_final_commitments
                .iter()
                .flat_map(|c| c.inputize())
                .collect::<Vec<_>>(),
            &proof.kzg_challenges,
            &proof.kzg_proofs.iter().map(|p| p.eval).collect::<Vec<_>>(),
            &proof.L_X_evals,
        ]
        .concat();

        let snark_v = S::verify(&snark_vp, &public_input, &proof.snark_proof)
            .map_err(|e| Error::Other(e.to_string()))?;
        if !snark_v {
            return Err(Error::SNARKVerificationFail);
        }

        // 7.3. Verify the KZG proofs
        for ((cm, &c), pi) in U_final_commitments
            .iter()
            .zip(&proof.kzg_challenges)
            .zip(&proof.kzg_proofs)
        {
            // we're at the Ethereum EVM case, so the CS1 is KZG commitments
            CS1::verify_with_challenge(&cs_vp, c, cm, pi)?;
        }

        Ok(true)
    }
}

#[cfg(test)]
pub mod tests {
    use ark_bn254::Bn254;
    use ark_bn254::{Fr, G1Projective as Projective};
    use ark_groth16::Groth16;
    use ark_grumpkin::Projective as Projective2;
    use std::time::Instant;

    use super::*;
    use crate::commitment::kzg::KZG;
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::protogalaxy::ProverParams;
    use crate::folding::traits::CommittedInstanceOps;
    use crate::frontend::utils::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_canonical_config;
    use crate::Error;

    #[test]
    fn test_decider() -> Result<(), Error> {
        // use ProtoGalaxy as FoldingScheme
        type PG = ProtoGalaxy<
            Projective,
            Projective2,
            CubicFCircuit<Fr>,
            KZG<'static, Bn254>,
            Pedersen<Projective2>,
        >;
        type D = Decider<
            Projective,
            Projective2,
            CubicFCircuit<Fr>,
            KZG<'static, Bn254>,
            Pedersen<Projective2>,
            Groth16<Bn254>, // here we define the Snark to use in the decider
            PG,             // here we define the FoldingScheme to use
        >;

        let mut rng = rand::rngs::OsRng;
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(())?;
        let z_0 = vec![Fr::from(3_u32)];

        let preprocessor_param = (poseidon_config, F_circuit);
        let protogalaxy_params = PG::preprocess(&mut rng, &preprocessor_param)?;

        let start = Instant::now();
        let mut protogalaxy = PG::init(&protogalaxy_params, F_circuit, z_0.clone())?;
        println!("ProtoGalaxy initialized, {:?}", start.elapsed());
        protogalaxy.prove_step(&mut rng, vec![], None)?;
        protogalaxy.prove_step(&mut rng, vec![], None)?; // do a 2nd step

        // prepare the Decider prover & verifier params
        let (decider_pp, decider_vp) =
            D::preprocess(&mut rng, protogalaxy_params, protogalaxy.clone())?;

        // decider proof generation
        let start = Instant::now();
        let proof = D::prove(rng, decider_pp, protogalaxy.clone())?;
        println!("Decider prove, {:?}", start.elapsed());

        // decider proof verification
        let start = Instant::now();
        let verified = D::verify(
            decider_vp.clone(),
            protogalaxy.i,
            protogalaxy.z_0.clone(),
            protogalaxy.z_i.clone(),
            &protogalaxy.U_i.get_commitments(),
            &protogalaxy.u_i.get_commitments(),
            &proof,
        )?;
        assert!(verified);
        println!("Decider verify, {:?}", start.elapsed());

        // decider proof verification using the deserialized data
        let verified = D::verify(
            decider_vp,
            protogalaxy.i,
            protogalaxy.z_0,
            protogalaxy.z_i,
            &protogalaxy.U_i.get_commitments(),
            &protogalaxy.u_i.get_commitments(),
            &proof,
        )?;
        assert!(verified);
        Ok(())
    }

    // Test to check the serialization and deserialization of diverse Decider related parameters.
    // This test is the same test as `test_decider` but it serializes values and then uses the
    // deserialized values to continue the checks.
    #[test]
    fn test_decider_serialization() -> Result<(), Error> {
        // use ProtoGalaxy as FoldingScheme
        type PG = ProtoGalaxy<
            Projective,
            Projective2,
            CubicFCircuit<Fr>,
            KZG<'static, Bn254>,
            Pedersen<Projective2>,
        >;
        type D = Decider<
            Projective,
            Projective2,
            CubicFCircuit<Fr>,
            KZG<'static, Bn254>,
            Pedersen<Projective2>,
            Groth16<Bn254>, // here we define the Snark to use in the decider
            PG,             // here we define the FoldingScheme to use
        >;

        let mut rng = rand::rngs::OsRng;
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(())?;
        let z_0 = vec![Fr::from(3_u32)];

        let preprocessor_param = (poseidon_config, F_circuit);
        let protogalaxy_params = PG::preprocess(&mut rng, &preprocessor_param)?;

        let start = Instant::now();
        let mut protogalaxy = PG::init(&protogalaxy_params, F_circuit, z_0.clone())?;
        println!("ProtoGalaxy initialized, {:?}", start.elapsed());
        protogalaxy.prove_step(&mut rng, vec![], None)?;
        protogalaxy.prove_step(&mut rng, vec![], None)?; // do a 2nd step

        // prepare the Decider prover & verifier params
        let (decider_pp, decider_vp) =
            D::preprocess(&mut rng, protogalaxy_params.clone(), protogalaxy.clone())?;

        // serialize the Nova params. These params are the trusted setup of the commitment schemes used
        // (ie. KZG & Pedersen in this case)
        let mut protogalaxy_pp_serialized = vec![];
        protogalaxy_params
            .0
            .serialize_compressed(&mut protogalaxy_pp_serialized)?;
        let mut protogalaxy_vp_serialized = vec![];
        protogalaxy_params
            .1
            .serialize_compressed(&mut protogalaxy_vp_serialized)?;
        // deserialize the Nova params. This would be done by the client reading from a file
        let protogalaxy_pp_deserialized = ProverParams::<
            Projective,
            Projective2,
            KZG<'static, Bn254>,
            Pedersen<Projective2>,
        >::deserialize_compressed(
            &mut protogalaxy_pp_serialized.as_slice()
        )?;
        let protogalaxy_vp_deserialized = <PG as FoldingScheme<
            Projective,
            Projective2,
            CubicFCircuit<Fr>,
        >>::vp_deserialize_with_mode(
            &mut protogalaxy_vp_serialized.as_slice(),
            ark_serialize::Compress::Yes,
            ark_serialize::Validate::Yes,
            (), // fcircuit_params
        )?;

        // initialize protogalaxy again, but from the deserialized parameters
        let protogalaxy_params = (protogalaxy_pp_deserialized, protogalaxy_vp_deserialized);
        let mut protogalaxy = PG::init(&protogalaxy_params, F_circuit, z_0)?;

        let start = Instant::now();
        protogalaxy.prove_step(&mut rng, vec![], None)?;
        println!("prove_step, {:?}", start.elapsed());
        protogalaxy.prove_step(&mut rng, vec![], None)?; // do a 2nd step

        // decider proof generation
        let start = Instant::now();
        let proof = D::prove(rng, decider_pp, protogalaxy.clone())?;
        println!("Decider prove, {:?}", start.elapsed());

        // decider proof verification
        let start = Instant::now();
        let verified = D::verify(
            decider_vp.clone(),
            protogalaxy.i,
            protogalaxy.z_0.clone(),
            protogalaxy.z_i.clone(),
            &protogalaxy.U_i.get_commitments(),
            &protogalaxy.u_i.get_commitments(),
            &proof,
        )?;
        assert!(verified);
        println!("Decider verify, {:?}", start.elapsed());

        // The rest of this test will serialize the data and deserialize it back, and use it to
        // verify the proof:

        // serialize the verifier_params, proof and public inputs
        let mut decider_vp_serialized = vec![];
        decider_vp.serialize_compressed(&mut decider_vp_serialized)?;
        let mut proof_serialized = vec![];
        proof.serialize_compressed(&mut proof_serialized)?;
        // serialize the public inputs in a single packet
        let mut public_inputs_serialized = vec![];
        protogalaxy
            .i
            .serialize_compressed(&mut public_inputs_serialized)?;
        protogalaxy
            .z_0
            .serialize_compressed(&mut public_inputs_serialized)?;
        protogalaxy
            .z_i
            .serialize_compressed(&mut public_inputs_serialized)?;

        // deserialize back the verifier_params, proof and public inputs
        let decider_vp_deserialized =
            VerifierParam::<
                Projective,
                <KZG<'static, Bn254> as CommitmentScheme<Projective>>::VerifierParams,
                <Groth16<Bn254> as SNARK<Fr>>::VerifyingKey,
            >::deserialize_compressed(&mut decider_vp_serialized.as_slice())?;
        let proof_deserialized =
            Proof::<Projective, KZG<'static, Bn254>, Groth16<Bn254>>::deserialize_compressed(
                &mut proof_serialized.as_slice(),
            )?;

        // deserialize the public inputs from the single packet 'public_inputs_serialized'
        let mut reader = public_inputs_serialized.as_slice();
        let i_deserialized = Fr::deserialize_compressed(&mut reader)?;
        let z_0_deserialized = Vec::<Fr>::deserialize_compressed(&mut reader)?;
        let z_i_deserialized = Vec::<Fr>::deserialize_compressed(&mut reader)?;

        // decider proof verification using the deserialized data
        let verified = D::verify(
            decider_vp_deserialized,
            i_deserialized,
            z_0_deserialized,
            z_i_deserialized,
            &protogalaxy.U_i.get_commitments(),
            &protogalaxy.u_i.get_commitments(),
            &proof_deserialized,
        )?;
        assert!(verified);
        Ok(())
    }
}
