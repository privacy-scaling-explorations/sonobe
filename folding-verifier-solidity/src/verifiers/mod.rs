pub mod templates;

#[cfg(test)]
mod tests {
    use crate::evm::test::{save_solidity, Evm};
    use crate::verifiers::templates::{KZG10Verifier, SolidityVerifier};
    use ark_bn254::{Bn254, Fr, G1Projective as G1};
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::{BigInteger, PrimeField};
    use ark_groth16::{Proof, VerifyingKey};
    use ark_poly_commit::kzg10::VerifierKey;
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use ark_std::Zero;
    use ark_std::{test_rng, UniformRand};
    use askama::Template;
    use folding_schemes::{
        commitment::{
            kzg::{KZGProver, KZGSetup, ProverKey},
            CommitmentProver,
        },
        transcript::{
            poseidon::{poseidon_test_config, PoseidonTranscript},
            Transcript,
        },
    };
    use itertools::chain;
    use std::fs::File;

    pub const FUNCTION_SIGNATURE_KZG10_CHECK: [u8; 4] = [0x9e, 0x78, 0xcc, 0xf7];

    fn load_test_data() -> (VerifyingKey<Bn254>, Proof<Bn254>, Fr) {
        let manifest_dir = env!("CARGO_MANIFEST_DIR");

        let file = File::open(format!("{}/assets/G16_test_vk_data", manifest_dir)).unwrap();
        let vk = VerifyingKey::<Bn254>::deserialize_compressed(&file).unwrap();

        let file = File::open(format!("{}/assets/G16_test_proof_data", manifest_dir)).unwrap();
        let proof = Proof::<Bn254>::deserialize_compressed(&file).unwrap();

        (vk, proof, Fr::from(35u64))
    }

    #[test]
    fn test_groth16_verifier_template_renders() {
        let (vk, proof, pi) = load_test_data();
        let template = SolidityVerifier::from(vk);
        let res = template.render().unwrap();
        let mut calldata = vec![];
        pi.serialize_uncompressed(&mut calldata).unwrap();
        proof.serialize_uncompressed(&mut calldata).unwrap();
    }

    #[test]
    fn test_groth16_verifier_template_compiles() {}

    #[test]
    fn test_groth16_verifier_accepts_and_rejects_proofs() {}

    #[test]
    fn test_kzg_verifier_template_renders() {
        let rng = &mut test_rng();
        let n = 10;
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) = KZGSetup::<Bn254>::setup(rng, n);
        let template = KZG10Verifier::from(&pk, &vk);
        let res = template.render().unwrap();
        assert!(res.contains(&vk.g.x.to_string()));
    }

    #[test]
    fn test_kzg_verifier_compiles() {
        let rng = &mut test_rng();
        let n = 10;
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) = KZGSetup::<Bn254>::setup(rng, n);
        let template = KZG10Verifier::from(&pk, &vk);
        let res = template.render().unwrap();
        save_solidity("kzg_10_verifier.sol", &res);
        let kzg_verifier_bytecode = crate::evm::test::compile_solidity(&res);
        let mut evm = Evm::default();
        _ = evm.create(kzg_verifier_bytecode);
    }

    #[test]
    fn test_kzg_verifier_accepts_and_rejects_proofs() {
        let rng = &mut test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();
        let transcript_p = &mut PoseidonTranscript::<G1>::new(&poseidon_config);
        let transcript_v = &mut PoseidonTranscript::<G1>::new(&poseidon_config);

        let n = 10;
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) = KZGSetup::<Bn254>::setup(rng, n);
        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(rng)).take(n).collect();
        let cm = KZGProver::<G1>::commit(&pk, &v, &Fr::zero()).unwrap();
        let (eval, proof) =
            KZGProver::<G1>::prove(&pk, transcript_p, &cm, &v, &Fr::zero()).unwrap();
        let template = KZG10Verifier::from(&pk, &vk);
        let res = template.render().unwrap();
        let kzg_verifier_bytecode = crate::evm::test::compile_solidity(&res);
        let mut evm = Evm::default();
        let verifier_address = evm.create(kzg_verifier_bytecode);

        let (cm_affine, proof_affine) = (cm.into_affine(), proof.into_affine());
        let (x_comm, y_comm) = cm_affine.xy().unwrap();
        let (x_proof, y_proof) = proof_affine.xy().unwrap();
        let y = eval.into_bigint().to_bytes_be();

        transcript_v.absorb_point(&cm).unwrap();
        let x = transcript_v.get_challenge();

        let x = x.into_bigint().to_bytes_be();
        let mut calldata: Vec<u8> = chain![
            FUNCTION_SIGNATURE_KZG10_CHECK,
            x_comm.into_bigint().to_bytes_be(),
            y_comm.into_bigint().to_bytes_be(),
            x_proof.into_bigint().to_bytes_be(),
            y_proof.into_bigint().to_bytes_be(),
            x.clone(),
            y,
        ]
        .collect();

        let (_, output) = evm.call(verifier_address, calldata.clone());
        assert_eq!(*output.last().unwrap(), 1);

        // change calldata to make it invalid
        let last_calldata_element = calldata.last_mut().unwrap();
        *last_calldata_element = 0;
        let (_, output) = evm.call(verifier_address, calldata);
        assert_eq!(*output.last().unwrap(), 0);
    }
}
