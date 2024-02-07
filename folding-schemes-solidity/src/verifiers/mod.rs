pub mod templates;

#[cfg(test)]
mod tests {
    use crate::evm::test::{save_solidity, Evm};
    use crate::verifiers::templates::{Groth16Verifier, KZG10Verifier};
    use ark_bn254::{Bn254, Fr, G1Projective as G1};
    use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::{BigInt, BigInteger, PrimeField};
    use ark_groth16::Groth16;
    use ark_poly_commit::kzg10::VerifierKey;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::eq::EqGadget;
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
    use ark_std::rand::{RngCore, SeedableRng};
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
    use std::marker::PhantomData;

    // Function signatures for proof verification on kzg10 and groth16 contracts
    pub const FUNCTION_SIGNATURE_KZG10_CHECK: [u8; 4] = [0x9e, 0x78, 0xcc, 0xf7];
    pub const FUNCTION_SIGNATURE_GROTH16_VERIFY_PROOF: [u8; 4] = [0x43, 0x75, 0x3b, 0x4d];

    // Pragma statements for verifiers
    pub const PRAGMA_GROTH16_VERIFIER: &str = "pragma solidity >=0.7.0 <0.9.0;"; // from snarkjs, avoid changing
    pub const PRAGMA_KZG10_VERIFIER: &str = "pragma solidity >=0.8.1 <=0.8.4;";

    struct TestAddCircuit<F: PrimeField> {
        _f: PhantomData<F>,
        pub x: u8,
        pub y: u8,
        pub z: u8,
    }

    impl<F: PrimeField> ConstraintSynthesizer<F> for TestAddCircuit<F> {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let x = FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(self.x)))?;
            let y = FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(self.y)))?;
            let z = FpVar::<F>::new_input(cs.clone(), || Ok(F::from(self.z)))?;
            let comp_z = x.clone() + y.clone();
            comp_z.enforce_equal(&z)?;
            Ok(())
        }
    }

    #[test]
    fn test_groth16_kzg10_decider_template_renders() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
        let (x, y, z) = (21, 21, 42);
        let (_, vk) = {
            let c = TestAddCircuit::<Fr> {
                _f: PhantomData,
                x,
                y,
                z,
            };
            Groth16::<Bn254>::setup(c, &mut rng).unwrap()
        };
        let groth16_template = Groth16Verifier::from(vk, None);
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) = KZGSetup::<Bn254>::setup(&mut rng, 5);
        let kzg10_template = KZG10Verifier::from(&vk, &pk.powers_of_g[..5], None, None);
        let decider_template = super::templates::Groth16KZG10DeciderVerifier {
            groth16_verifier: groth16_template,
            kzg10_verifier: kzg10_template,
        };
        save_solidity("decider.sol", &decider_template.render().unwrap());
    }

    #[test]
    fn test_groth16_kzg10_decider_template_compiles() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
        let (x, y, z) = (21, 21, 42);
        let (_, vk) = {
            let c = TestAddCircuit::<Fr> {
                _f: PhantomData,
                x,
                y,
                z,
            };
            Groth16::<Bn254>::setup(c, &mut rng).unwrap()
        };
        // we dont specify any pragma values for both verifiers, the pragma from the decider takes over
        let groth16_template = Groth16Verifier::from(vk, None);
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) = KZGSetup::<Bn254>::setup(&mut rng, 5);
        let kzg10_template = KZG10Verifier::from(&vk, &pk.powers_of_g[..5], None, None);
        let decider_template = super::templates::Groth16KZG10DeciderVerifier {
            groth16_verifier: groth16_template,
            kzg10_verifier: kzg10_template,
        };
        let decider_verifier_bytecode =
            crate::evm::test::compile_solidity(decider_template.render().unwrap(), "NovaDecider");
        let mut evm = Evm::default();
        _ = evm.create(decider_verifier_bytecode);
    }

    #[test]
    fn test_groth16_verifier_template_renders() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
        let (x, y, z) = (21, 21, 42);
        let (_, vk) = {
            let c = TestAddCircuit::<Fr> {
                _f: PhantomData,
                x,
                y,
                z,
            };
            Groth16::<Bn254>::setup(c, &mut rng).unwrap()
        };
        let template = Groth16Verifier::from(vk, Some(PRAGMA_GROTH16_VERIFIER.to_string()));
        save_solidity("groth16_verifier.sol", &template.render().unwrap());
        _ = template.render().unwrap();
    }

    #[test]
    fn test_groth16_verifier_template_compiles() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
        let (x, y, z) = (21, 21, 42);
        let (_, vk) = {
            let c = TestAddCircuit::<Fr> {
                _f: PhantomData,
                x,
                y,
                z,
            };
            Groth16::<Bn254>::setup(c, &mut rng).unwrap()
        };
        let res = Groth16Verifier::from(vk, Some(PRAGMA_GROTH16_VERIFIER.to_string()))
            .render()
            .unwrap();
        let groth16_verifier_bytecode = crate::evm::test::compile_solidity(res, "Verifier");
        let mut evm = Evm::default();
        _ = evm.create(groth16_verifier_bytecode);
    }

    #[test]
    fn test_groth16_verifier_accepts_and_rejects_proofs() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
        let (x, y, z) = (21, 21, 42);
        let (pk, vk) = {
            let c = TestAddCircuit::<Fr> {
                _f: PhantomData,
                x,
                y,
                z,
            };
            Groth16::<Bn254>::setup(c, &mut rng).unwrap()
        };
        let c = TestAddCircuit::<Fr> {
            _f: PhantomData,
            x,
            y,
            z,
        };
        let proof = Groth16::<Bn254>::prove(&pk, c, &mut rng).unwrap();
        let res = Groth16Verifier::from(vk, Some(PRAGMA_GROTH16_VERIFIER.to_string()))
            .render()
            .unwrap();
        save_solidity("groth16_verifier.sol", &res);
        let groth16_verifier_bytecode = crate::evm::test::compile_solidity(&res, "Verifier");
        let mut evm = Evm::default();
        let verifier_address = evm.create(groth16_verifier_bytecode);
        let (a_x, a_y) = proof.a.xy().unwrap();
        let (b_x, b_y) = proof.b.xy().unwrap();
        let (c_x, c_y) = proof.c.xy().unwrap();
        let mut calldata: Vec<u8> = chain![
            FUNCTION_SIGNATURE_GROTH16_VERIFY_PROOF,
            a_x.into_bigint().to_bytes_be(),
            a_y.into_bigint().to_bytes_be(),
            b_x.c1.into_bigint().to_bytes_be(),
            b_x.c0.into_bigint().to_bytes_be(),
            b_y.c1.into_bigint().to_bytes_be(),
            b_y.c0.into_bigint().to_bytes_be(),
            c_x.into_bigint().to_bytes_be(),
            c_y.into_bigint().to_bytes_be(),
            BigInt::from(Fr::from(z)).to_bytes_be(),
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

    #[test]
    fn test_kzg_verifier_template_renders() {
        let rng = &mut test_rng();
        let n = 10;
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) = KZGSetup::<Bn254>::setup(rng, n);
        let template = KZG10Verifier::from(
            &vk,
            &pk.powers_of_g[..5],
            Some(PRAGMA_KZG10_VERIFIER.to_string()),
            None,
        );
        let res = template.render().unwrap();
        assert!(res.contains(&vk.g.x.to_string()));
    }

    #[test]
    fn test_kzg_verifier_compiles() {
        let rng = &mut test_rng();
        let n = 10;
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) = KZGSetup::<Bn254>::setup(rng, n);
        let template = KZG10Verifier::from(
            &vk,
            &pk.powers_of_g[..5],
            Some(PRAGMA_KZG10_VERIFIER.to_string()),
            None,
        );
        let res = template.render().unwrap();
        let kzg_verifier_bytecode = crate::evm::test::compile_solidity(res, "KZG10");
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
        let template = KZG10Verifier::from(
            &vk,
            &pk.powers_of_g[..5],
            Some(PRAGMA_KZG10_VERIFIER.to_string()),
            None,
        );
        let res = template.render().unwrap();
        let kzg_verifier_bytecode = crate::evm::test::compile_solidity(res, "KZG10");
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
