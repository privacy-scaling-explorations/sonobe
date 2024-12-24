/// This file implements the HyperNova's onchain (Ethereum's EVM) decider.
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_snark::SNARK;
use ark_std::rand::{CryptoRng, RngCore};
use ark_std::{One, Zero};
use core::marker::PhantomData;

pub use super::decider_eth_circuit::DeciderEthCircuit;
use super::decider_eth_circuit::DeciderHyperNovaGadget;
use super::HyperNova;
use crate::commitment::{
    kzg::Proof as KZGProof, pedersen::Params as PedersenParams, CommitmentScheme,
};
use crate::folding::circuits::decider::DeciderEnabledNIFS;
use crate::folding::nova::decider_eth::VerifierParam;
use crate::folding::traits::WitnessOps;
use crate::frontend::FCircuit;
use crate::{Curve, Error};
use crate::{Decider as DeciderTrait, FoldingScheme};

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<C1, CS1, S>
where
    C1: Curve,
    CS1: CommitmentScheme<C1, ProverChallenge = C1::ScalarField, Challenge = C1::ScalarField>,
    S: SNARK<C1::ScalarField>,
{
    snark_proof: S::Proof,
    kzg_proof: CS1::Proof,
    // rho used at the last fold, U_{i+1}=NIMFS.V(rho, U_i, u_i), it is checked in-circuit
    rho: C1::ScalarField,
    // the KZG challenge is provided by the prover, but in-circuit it is checked to match
    // the in-circuit computed computed one.
    kzg_challenge: C1::ScalarField,
}

/// Onchain Decider, for ethereum use cases
#[derive(Clone, Debug)]
pub struct Decider<C1, C2, FC, CS1, CS2, S, FS, const MU: usize, const NU: usize> {
    _c1: PhantomData<C1>,
    _c2: PhantomData<C2>,
    _fc: PhantomData<FC>,
    _cs1: PhantomData<CS1>,
    _cs2: PhantomData<CS2>,
    _s: PhantomData<S>,
    _fs: PhantomData<FS>,
}

impl<C1, C2, FC, CS1, CS2, S, FS, const MU: usize, const NU: usize> DeciderTrait<C1, C2, FC, FS>
    for Decider<C1, C2, FC, CS1, CS2, S, FS, MU, NU>
where
    C1: Curve<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    C2: Curve,
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
    // constrain FS into HyperNova, since this is a Decider specifically for HyperNova
    HyperNova<C1, C2, FC, CS1, CS2, MU, NU, false>: From<FS>,
    crate::folding::hypernova::ProverParams<C1, C2, CS1, CS2, false>:
        From<<FS as FoldingScheme<C1, C2, FC>>::ProverParam>,
    crate::folding::hypernova::VerifierParams<C1, C2, CS1, CS2, false>:
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
        let circuit = DeciderEthCircuit::<C1, C2>::try_from(HyperNova::from(fs))?;

        // get the Groth16 specific setup for the circuit
        let (g16_pk, g16_vk) = S::circuit_specific_setup(circuit, &mut rng)
            .map_err(|e| Error::SNARKSetupFail(e.to_string()))?;

        // get the FoldingScheme prover & verifier params from HyperNova
        #[allow(clippy::type_complexity)]
        let hypernova_pp: <HyperNova<C1, C2, FC, CS1, CS2, MU, NU, false> as FoldingScheme<
            C1,
            C2,
            FC,
        >>::ProverParam = prep_param.0.into();
        #[allow(clippy::type_complexity)]
        let hypernova_vp: <HyperNova<C1, C2, FC, CS1, CS2, MU, NU, false> as FoldingScheme<
            C1,
            C2,
            FC,
        >>::VerifierParam = prep_param.1.into();
        let pp_hash = hypernova_vp.pp_hash()?;

        let pp = (g16_pk, hypernova_pp.cs_pp);

        let vp = Self::VerifierParam {
            pp_hash,
            snark_vp: g16_vk,
            cs_vp: hypernova_vp.cs_vp,
        };
        Ok((pp, vp))
    }

    fn prove(
        mut rng: impl RngCore + CryptoRng,
        pp: Self::ProverParam,
        folding_scheme: FS,
    ) -> Result<Self::Proof, Error> {
        let (snark_pk, cs_pk): (S::ProvingKey, CS1::ProverParams) = pp;

        let circuit = DeciderEthCircuit::<C1, C2>::try_from(HyperNova::from(folding_scheme))?;

        let rho = circuit.randomness;

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
            rho,
            kzg_proof: (kzg_proofs.len() == 1)
                .then(|| kzg_proofs[0].clone())
                .ok_or(Error::NotExpectedLength(kzg_proofs.len(), 1))?,
            kzg_challenge: (kzg_challenges.len() == 1)
                .then(|| kzg_challenges[0])
                .ok_or(Error::NotExpectedLength(kzg_challenges.len(), 1))?,
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
        let C = DeciderHyperNovaGadget::fold_group_elements_native(
            running_commitments,
            incoming_commitments,
            None,
            proof.rho,
        )?[0];

        // Note: the NIMFS proof is checked inside the DeciderEthCircuit, which ensures that the
        // 'proof.U_i1' is correctly computed
        let public_input: Vec<C1::ScalarField> = [
            &[pp_hash, i][..],
            &z_0,
            &z_i,
            &C.inputize_nonnative(),
            &[proof.kzg_challenge, proof.kzg_proof.eval, proof.rho],
        ]
        .concat();

        let snark_v = S::verify(&snark_vp, &public_input, &proof.snark_proof)
            .map_err(|e| Error::Other(e.to_string()))?;
        if !snark_v {
            return Err(Error::SNARKVerificationFail);
        }

        // 7.3. Verify the KZG proof
        // we're at the Ethereum EVM case, so the CS1 is KZG commitments
        CS1::verify_with_challenge(&cs_vp, proof.kzg_challenge, &C, &proof.kzg_proof)?;

        Ok(true)
    }
}

#[cfg(test)]
pub mod tests {
    use ark_bn254::{Bn254, Fr, G1Projective as Projective};
    use ark_groth16::Groth16;
    use ark_grumpkin::Projective as Projective2;
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};

    use super::*;
    use crate::commitment::{kzg::KZG, pedersen::Pedersen};
    use crate::folding::hypernova::cccs::CCCS;
    use crate::folding::hypernova::lcccs::LCCCS;
    use crate::folding::hypernova::PreprocessorParam;
    use crate::folding::traits::CommittedInstanceOps;
    use crate::frontend::utils::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_canonical_config;

    #[test]
    fn test_decider() -> Result<(), Error> {
        const MU: usize = 1;
        const NU: usize = 1;
        // use HyperNova as FoldingScheme
        type HN = HyperNova<
            Projective,
            Projective2,
            CubicFCircuit<Fr>,
            KZG<'static, Bn254>,
            Pedersen<Projective2>,
            MU,
            NU,
            false,
        >;
        type D = Decider<
            Projective,
            Projective2,
            CubicFCircuit<Fr>,
            KZG<'static, Bn254>,
            Pedersen<Projective2>,
            Groth16<Bn254>, // here we define the Snark to use in the decider
            HN,             // here we define the FoldingScheme to use
            MU,
            NU,
        >;

        let mut rng = rand::rngs::OsRng;
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(())?;
        let z_0 = vec![Fr::from(3_u32)];

        let prep_param = PreprocessorParam::new(poseidon_config, F_circuit);
        let hypernova_params = HN::preprocess(&mut rng, &prep_param)?;

        let mut hypernova = HN::init(&hypernova_params, F_circuit, z_0.clone())?;
        hypernova.prove_step(&mut rng, (), Some((vec![], vec![])))?;
        hypernova.prove_step(&mut rng, (), Some((vec![], vec![])))?; // do a 2nd step

        // prepare the Decider prover & verifier params
        let (decider_pp, decider_vp) =
            D::preprocess(&mut rng, hypernova_params, hypernova.clone())?;

        // decider proof generation
        let proof = D::prove(rng, decider_pp, hypernova.clone())?;

        // decider proof verification
        let verified = D::verify(
            decider_vp,
            hypernova.i,
            hypernova.z_0,
            hypernova.z_i,
            &hypernova.U_i.get_commitments(),
            &hypernova.u_i.get_commitments(),
            &proof,
        )?;
        assert!(verified);
        Ok(())
    }

    #[test]
    fn test_decider_serialization() -> Result<(), Error> {
        const MU: usize = 1;
        const NU: usize = 1;
        // use HyperNova as FoldingScheme
        type HN = HyperNova<
            Projective,
            Projective2,
            CubicFCircuit<Fr>,
            KZG<'static, Bn254>,
            Pedersen<Projective2>,
            MU,
            NU,
            false,
        >;
        type D = Decider<
            Projective,
            Projective2,
            CubicFCircuit<Fr>,
            KZG<'static, Bn254>,
            Pedersen<Projective2>,
            Groth16<Bn254>, // here we define the Snark to use in the decider
            HN,             // here we define the FoldingScheme to use
            MU,
            NU,
        >;

        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(())?;
        let z_0 = vec![Fr::from(3_u32)];

        let prep_param = PreprocessorParam::new(poseidon_config.clone(), F_circuit);
        let hypernova_params = HN::preprocess(&mut rng, &prep_param)?;

        let hypernova = HN::init(&hypernova_params, F_circuit, z_0.clone())?;

        let mut rng = rand::rngs::OsRng;

        // prepare the Decider prover & verifier params
        let (decider_pp, decider_vp) =
            D::preprocess(&mut rng, hypernova_params.clone(), hypernova.clone())?;

        let mut hypernova_pp_serialized = vec![];
        hypernova_params
            .0
            .clone()
            .serialize_compressed(&mut hypernova_pp_serialized)?;
        let mut hypernova_vp_serialized = vec![];
        hypernova_params
            .1
            .clone()
            .serialize_compressed(&mut hypernova_vp_serialized)?;

        let hypernova_pp_deserialized = HN::pp_deserialize_with_mode(
            hypernova_pp_serialized.as_slice(),
            Compress::Yes,
            Validate::No,
            (), // FCircuit's Params
        )?;

        let hypernova_vp_deserialized = HN::vp_deserialize_with_mode(
            hypernova_vp_serialized.as_slice(),
            Compress::Yes,
            Validate::No,
            (), // FCircuit's Params
        )?;

        let hypernova_params = (hypernova_pp_deserialized, hypernova_vp_deserialized);
        let mut hypernova = HN::init(&hypernova_params, F_circuit, z_0.clone())?;

        hypernova.prove_step(&mut rng, (), Some((vec![], vec![])))?;
        hypernova.prove_step(&mut rng, (), Some((vec![], vec![])))?;

        // decider proof generation
        let proof = D::prove(rng, decider_pp, hypernova.clone())?;

        let verified = D::verify(
            decider_vp.clone(),
            hypernova.i,
            hypernova.z_0.clone(),
            hypernova.z_i.clone(),
            &hypernova.U_i.get_commitments(),
            &hypernova.u_i.get_commitments(),
            &proof,
        )?;
        assert!(verified);

        // The rest of this test will serialize the data and deserialize it back, and use it to
        // verify the proof:

        // serialize the verifier_params, proof and public inputs
        let mut decider_vp_serialized = vec![];
        decider_vp.serialize_compressed(&mut decider_vp_serialized)?;
        let mut proof_serialized = vec![];
        proof.serialize_compressed(&mut proof_serialized)?;
        // serialize the public inputs in a single packet
        let mut public_inputs_serialized = vec![];
        hypernova
            .i
            .serialize_compressed(&mut public_inputs_serialized)?;
        hypernova
            .z_0
            .serialize_compressed(&mut public_inputs_serialized)?;
        hypernova
            .z_i
            .serialize_compressed(&mut public_inputs_serialized)?;
        hypernova
            .U_i
            .serialize_compressed(&mut public_inputs_serialized)?;
        hypernova
            .u_i
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

        let mut reader = public_inputs_serialized.as_slice();
        let i_deserialized = Fr::deserialize_compressed(&mut reader)?;
        let z_0_deserialized = Vec::<Fr>::deserialize_compressed(&mut reader)?;
        let z_i_deserialized = Vec::<Fr>::deserialize_compressed(&mut reader)?;
        let _U_i = LCCCS::<Projective>::deserialize_compressed(&mut reader)?;
        let _u_i = CCCS::<Projective>::deserialize_compressed(&mut reader)?;

        let verified = D::verify(
            decider_vp_deserialized,
            i_deserialized,
            z_0_deserialized.clone(),
            z_i_deserialized.clone(),
            &hypernova.U_i.get_commitments(),
            &hypernova.u_i.get_commitments(),
            &proof_deserialized,
        )?;
        assert!(verified);
        Ok(())
    }
}
