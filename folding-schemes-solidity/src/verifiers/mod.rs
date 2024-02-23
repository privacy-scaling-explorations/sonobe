//! Solidity templates for the verifier contracts.
//! We use askama for templating and define which variables are required for each template.

// Pragma statements for verifiers
pub(crate) const PRAGMA_GROTH16_VERIFIER: &'static str = "pragma solidity >=0.7.0 <0.9.0;"; // from snarkjs, avoid changing
pub(crate) const PRAGMA_KZG10_VERIFIER: &'static str = "pragma solidity >=0.8.1 <=0.8.4;";

/// Default SDPX License identifier
pub(crate) const GPL3_SDPX_IDENTIFIER: &'static str = "// SPDX-License-Identifier: GPL-3.0";
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};

mod g16;
mod kzg;
mod nova_cyclefold;

pub use g16::{Groth16Data, Groth16Verifier};
pub use kzg::{KZG10Verifier, KzgData};
pub use nova_cyclefold::{NovaCyclefoldData, NovaCyclefoldDecider};

pub trait ProtocolData: CanonicalDeserialize + CanonicalSerialize {
    const PROTOCOL_NAME: &'static str;

    fn serialize_name<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        Self::PROTOCOL_NAME
            .as_bytes()
            .serialize_uncompressed(writer)
    }

    fn serialize_protocol_data<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        self.serialize_name(writer)?;
        self.serialize_compressed(writer)
    }
    fn deserialize_protocol_data<R: Read + Copy>(reader: R) -> Result<Self, SerializationError> {
        let name: String = String::deserialize_compressed(reader)?;
        let data = Self::deserialize_compressed(reader)?;

        if name != Self::PROTOCOL_NAME.to_string() {
            return Err(SerializationError::InvalidData);
        }

        Ok(data)
    }

    fn render_as_template(self, pragma: &Option<String>) -> Vec<u8>;
}

#[cfg(test)]
mod tests {
    use super::{PRAGMA_GROTH16_VERIFIER, PRAGMA_KZG10_VERIFIER};
    use crate::evm::{compile_solidity, save_solidity, Evm};
    use crate::utils::HeaderInclusion;
    use crate::{Groth16Data, KzgData, NovaCyclefoldData, ProtocolData};
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

    use super::g16::Groth16Verifier;
    use super::kzg::KZG10Verifier;
    use super::nova_cyclefold::NovaCyclefoldDecider;

    // Function signatures for proof verification on kzg10 and groth16 contracts
    pub const FUNCTION_SIGNATURE_KZG10_CHECK: [u8; 4] = [0x9e, 0x78, 0xcc, 0xf7];
    pub const FUNCTION_SIGNATURE_GROTH16_VERIFY_PROOF: [u8; 4] = [0x43, 0x75, 0x3b, 0x4d];
    pub const FUNCTION_SIGNATURE_NOVA_CYCLEFOLD_CHECK: [u8; 4] = [0x37, 0x98, 0x0b, 0xb6];

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
    fn groth16_data_serde_roundtrip() {
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

        let g16_data = Groth16Data::from(vk);
        let mut bytes = vec![];
        g16_data.serialize_protocol_data(&mut bytes).unwrap();
        let obtained_g16_data = Groth16Data::deserialize_protocol_data(bytes.as_slice()).unwrap();

        assert_eq!(g16_data, obtained_g16_data)
    }

    #[test]
    fn kzg_data_serde_roundtrip() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) = KZGSetup::<Bn254>::setup(&mut rng, 5);

        let kzg_data = KzgData::from((vk, Some(pk.powers_of_g[0..3].to_vec())));
        let mut bytes = vec![];
        kzg_data.serialize_protocol_data(&mut bytes).unwrap();
        let obtained_kzg_data = KzgData::deserialize_protocol_data(bytes.as_slice()).unwrap();

        assert_eq!(kzg_data, obtained_kzg_data)
    }

    #[test]
    fn nova_cyclefold_data_serde_roundtrip() {
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

        let g16_data = Groth16Data::from(vk);

        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) = KZGSetup::<Bn254>::setup(&mut rng, 5);

        let kzg_data = KzgData::from((vk, Some(pk.powers_of_g[0..3].to_vec())));
        let mut bytes = vec![];
        let nova_cyclefold_data = NovaCyclefoldData::from((g16_data, kzg_data));

        nova_cyclefold_data
            .serialize_protocol_data(&mut bytes)
            .unwrap();
        let obtained_nova_cyclefold_data =
            NovaCyclefoldData::deserialize_protocol_data(bytes.as_slice()).unwrap();

        assert_eq!(nova_cyclefold_data, obtained_nova_cyclefold_data)
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
        let groth16_template = Groth16Verifier::new(vk);
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) = KZGSetup::<Bn254>::setup(&mut rng, 5);
        let kzg10_template = KZG10Verifier::new(vk, pk.powers_of_g[..5].to_vec(), None, None);
        let decider_template = NovaCyclefoldDecider {
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
        let groth16_template = Groth16Verifier::new(vk);
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) = KZGSetup::<Bn254>::setup(&mut rng, 5);
        let kzg10_template = KZG10Verifier::new(vk, pk.powers_of_g[..5].to_vec(), None, None);
        let decider_template = NovaCyclefoldDecider {
            groth16_verifier: groth16_template,
            kzg10_verifier: kzg10_template,
        };
        let decider_verifier_bytecode =
            compile_solidity(decider_template.render().unwrap(), "NovaDecider");
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
        let template = Groth16Verifier::new(vk);

        // The template needs to be rendered with header. So we need to add it.
        HeaderInclusion::from((s))
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
        let res = Groth16Verifier::new(vk, Some(PRAGMA_GROTH16_VERIFIER.to_string()))
            .render()
            .unwrap();
        let groth16_verifier_bytecode = compile_solidity(res, "Verifier");
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
        let res = Groth16Verifier::new(vk, Some(PRAGMA_GROTH16_VERIFIER.to_string()))
            .render()
            .unwrap();
        save_solidity("groth16_verifier.sol", &res);
        let groth16_verifier_bytecode = compile_solidity(&res, "Verifier");
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
        let template = KZG10Verifier::new(
            vk.clone(),
            pk.powers_of_g[..5].to_vec(),
            Some(PRAGMA_KZG10_VERIFIER.to_string()),
            None,
        );
        let res = template.render().unwrap();

        // TODO: Unsure what this is testing. If we want to test correct rendering,
        // we should first check that it COMPLETELLY renders to what we expect.
        assert!(res.contains(&vk.g.x.to_string()));
    }

    #[test]
    fn test_kzg_verifier_compiles() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
        let n = 10;
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) = KZGSetup::<Bn254>::setup(&mut rng, n);
        let template = KZG10Verifier::new(
            vk,
            pk.powers_of_g[..5].to_vec(),
            Some(PRAGMA_KZG10_VERIFIER.to_string()),
            None,
        );
        let res = template.render().unwrap();
        let kzg_verifier_bytecode = compile_solidity(res, "KZG10");
        let mut evm = Evm::default();
        _ = evm.create(kzg_verifier_bytecode);
    }

    #[test]
    fn test_kzg_verifier_accepts_and_rejects_proofs() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
        let poseidon_config = poseidon_test_config::<Fr>();
        let transcript_p = &mut PoseidonTranscript::<G1>::new(&poseidon_config);
        let transcript_v = &mut PoseidonTranscript::<G1>::new(&poseidon_config);

        let n = 10;
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) = KZGSetup::<Bn254>::setup(&mut rng, n);
        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(n)
            .collect();
        let cm = KZGProver::<G1>::commit(&pk, &v, &Fr::zero()).unwrap();
        let (eval, proof) =
            KZGProver::<G1>::prove(&pk, transcript_p, &cm, &v, &Fr::zero(), None).unwrap();
        let template = KZG10Verifier::from(
            &vk,
            &pk.powers_of_g[..5],
            Some(PRAGMA_KZG10_VERIFIER.to_string()),
            None,
        );
        let res = template.render().unwrap();
        let kzg_verifier_bytecode = compile_solidity(res, "KZG10");
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

    #[test]
    fn nova_cyclefold_verifier_compiles() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
        let n = 10;
        let (pk, vk_kzg): (ProverKey<G1>, VerifierKey<Bn254>) =
            KZGSetup::<Bn254>::setup(&mut rng, n);

        let (x, y, z) = (21, 21, 42);
        let (_, vk_g16) = {
            let c = TestAddCircuit::<Fr> {
                _f: PhantomData,
                x,
                y,
                z,
            };
            Groth16::<Bn254>::setup(c, &mut rng).unwrap()
        };

        let template = NovaCyclefoldDecider::new(
            vk_g16,
            vk_kzg,
            pk.powers_of_g[0..5].to_vec(),
            Some(PRAGMA_KZG10_VERIFIER.to_string()),
        );
        let res = template.render().expect("Failed to render the template");
        let nova_cyclefold_verifier_bytecode = compile_solidity(res, "NovaCyclefold");
        let mut evm = Evm::default();
        _ = evm.create(nova_cyclefold_verifier_bytecode);
    }

    #[test]
    fn nova_cyclefold_verifier_accepts_and_rejects_proofs() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

        let (x, y, z) = (21, 21, 42);
        let (pk_g16, vk_g16) = {
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
        let g16_proof = Groth16::<Bn254>::prove(&pk_g16, c, &mut rng).unwrap();
        let g16_template = Groth16Verifier::new(vk_g16, Some(PRAGMA_GROTH16_VERIFIER.to_string()));
        let (a_x, a_y) = g16_proof.a.xy().unwrap();
        let (b_x, b_y) = g16_proof.b.xy().unwrap();
        let (c_x, c_y) = g16_proof.c.xy().unwrap();

        let poseidon_config = poseidon_test_config::<Fr>();
        let transcript_p = &mut PoseidonTranscript::<G1>::new(&poseidon_config);
        let transcript_v = &mut PoseidonTranscript::<G1>::new(&poseidon_config);

        let n = 10;
        let (pk_kzg, vk_kzg): (ProverKey<G1>, VerifierKey<Bn254>) =
            KZGSetup::<Bn254>::setup(&mut rng, n);
        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(n)
            .collect();
        let cm = KZGProver::<G1>::commit(&pk_kzg, &v, &Fr::zero()).unwrap();
        let (eval, proof) =
            KZGProver::<G1>::prove(&pk_kzg, transcript_p, &cm, &v, &Fr::zero()).unwrap();
        let kzg10_verifier = KZG10Verifier::new(
            vk_kzg,
            pk_kzg.powers_of_g[..5].to_vec(),
            Some(PRAGMA_KZG10_VERIFIER.to_string()),
            None,
        );

        let template = NovaCyclefoldDecider {
            groth16_verifier: g16_template,
            kzg10_verifier,
        };
        let res = template.render().expect("Failed to render the template");

        let nova_cyclefold_verifier_bytecode = compile_solidity(res, "NovaCyclefold");

        let mut evm = Evm::default();
        let verifier_address = evm.create(nova_cyclefold_verifier_bytecode);

        let (cm_affine, proof_affine) = (cm.into_affine(), proof.into_affine());
        let (x_comm, y_comm) = cm_affine.xy().unwrap();
        let (x_proof, y_proof) = proof_affine.xy().unwrap();
        let y = eval.into_bigint().to_bytes_be();

        transcript_v.absorb_point(&cm).unwrap();
        let x = transcript_v.get_challenge();

        // XXX: Continue here! Extract fn signature and call the method.
        // Once this works, implement testing with CLI rendering.
        let x = x.into_bigint().to_bytes_be();
        let mut calldata: Vec<u8> = chain![
            FUNCTION_SIGNATURE_NOVA_CYCLEFOLD_CHECK,
            a_x.into_bigint().to_bytes_be(),
            a_y.into_bigint().to_bytes_be(),
            b_x.c1.into_bigint().to_bytes_be(),
            b_x.c0.into_bigint().to_bytes_be(),
            b_y.c1.into_bigint().to_bytes_be(),
            b_y.c0.into_bigint().to_bytes_be(),
            c_x.into_bigint().to_bytes_be(),
            c_y.into_bigint().to_bytes_be(),
            BigInt::from(Fr::from(z)).to_bytes_be(),
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
