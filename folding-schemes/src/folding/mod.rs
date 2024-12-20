pub mod circuits;
pub mod hypernova;
pub mod nova;
pub mod protogalaxy;
pub mod traits;

#[cfg(test)]
pub mod tests {

    use ark_pallas::{Fr, Projective as G1};
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use ark_vesta::Projective as G2;
    use std::io::Write;

    use crate::commitment::pedersen::Pedersen;
    use crate::folding::{
        hypernova::HyperNova,
        nova::{Nova, PreprocessorParam as NovaPreprocessorParam},
        protogalaxy::ProtoGalaxy,
    };
    use crate::frontend::utils::CubicFCircuit;
    use crate::frontend::FCircuit;
    use crate::transcript::poseidon::poseidon_canonical_config;
    use crate::FoldingScheme;
    use crate::{Error, SonobeCurve};

    /// tests the IVC proofs and its serializers for the 3 implemented IVCs: Nova, HyperNova and
    /// ProtoGalaxy.
    #[test]
    fn test_serialize_ivc_nova_hypernova_protogalaxy() -> Result<(), Error> {
        let poseidon_config = poseidon_canonical_config::<Fr>();
        type FC = CubicFCircuit<Fr>;
        let f_circuit = FC::new(())?;

        // test Nova
        type N = Nova<G1, G2, FC, Pedersen<G1>, Pedersen<G2>, false>;
        let prep_param = NovaPreprocessorParam::new(poseidon_config.clone(), f_circuit);
        test_serialize_ivc_opt::<G1, G2, FC, N>("nova".to_string(), prep_param.clone())?;

        // test HyperNova
        type HN = HyperNova<
            G1,
            G2,
            FC,
            Pedersen<G1>,
            Pedersen<G2>,
            1, // mu
            1, // nu
            false,
        >;
        test_serialize_ivc_opt::<G1, G2, FC, HN>("hypernova".to_string(), prep_param)?;

        // test ProtoGalaxy
        type P = ProtoGalaxy<G1, G2, FC, Pedersen<G1>, Pedersen<G2>>;
        let prep_param = (poseidon_config, f_circuit);
        test_serialize_ivc_opt::<G1, G2, FC, P>("protogalaxy".to_string(), prep_param)?;
        Ok(())
    }

    fn test_serialize_ivc_opt<
        C1: SonobeCurve<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
        C2: SonobeCurve,
        FC: FCircuit<C1::ScalarField, Params = ()>,
        FS: FoldingScheme<C1, C2, FC>,
    >(
        name: String,
        prep_param: FS::PreprocessorParam,
    ) -> Result<(), Error> {
        let mut rng = ark_std::test_rng();
        let F_circuit = FC::new(())?;

        let fs_params = FS::preprocess(&mut rng, &prep_param)?;

        let z_0 = vec![C1::ScalarField::from(3_u32)];
        let mut fs = FS::init(&fs_params, F_circuit, z_0.clone())?;

        // perform multiple IVC steps (internally folding)
        let num_steps: usize = 3;
        for _ in 0..num_steps {
            fs.prove_step(&mut rng, vec![], None)?;
        }

        // verify the IVCProof
        let ivc_proof: FS::IVCProof = fs.ivc_proof();
        FS::verify(fs_params.1.clone(), ivc_proof.clone())?;

        // serialize the IVCProof and store it in a file
        let mut writer = vec![];
        assert!(ivc_proof.serialize_compressed(&mut writer).is_ok());

        let mut file = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .open(format!("./ivc_proof-{}.serialized", name))?;
        file.write_all(&writer)?;

        // read the IVCProof from the file deserializing it
        let bytes = std::fs::read(format!("./ivc_proof-{}.serialized", name))?;
        let deserialized_ivc_proof = FS::IVCProof::deserialize_compressed(bytes.as_slice())?;
        // verify deserialized IVCProof
        FS::verify(fs_params.1.clone(), deserialized_ivc_proof.clone())?;

        // build the FS from the given IVCProof, FC::Params, ProverParams and VerifierParams
        let mut new_fs = FS::from_ivc_proof(deserialized_ivc_proof, (), fs_params.clone())?;

        // serialize the Nova params
        let mut fs_pp_serialized = vec![];
        fs_params.0.serialize_compressed(&mut fs_pp_serialized)?;
        let mut fs_vp_serialized = vec![];
        fs_params.1.serialize_compressed(&mut fs_vp_serialized)?;

        // deserialize the Nova params. This would be done by the client reading from a file
        let _fs_pp_deserialized = FS::pp_deserialize_with_mode(
            &mut fs_pp_serialized.as_slice(),
            ark_serialize::Compress::Yes,
            ark_serialize::Validate::Yes,
            (), // FCircuit's Params
        )?;

        // perform several IVC steps on both the original FS instance and the recovered from the
        // serialization new FS instance
        let num_steps: usize = 3;
        for _ in 0..num_steps {
            new_fs.prove_step(&mut rng, vec![], None)?;
            fs.prove_step(&mut rng, vec![], None)?;
        }

        // check that the IVCProofs from both FS instances are equal
        assert_eq!(new_fs.ivc_proof(), fs.ivc_proof());

        let fs_vp_deserialized = FS::vp_deserialize_with_mode(
            &mut fs_vp_serialized.as_slice(),
            ark_serialize::Compress::Yes,
            ark_serialize::Validate::Yes,
            (), // fcircuit_params
        )?;

        // get the IVCProof
        let ivc_proof: FS::IVCProof = new_fs.ivc_proof();

        // serialize IVCProof
        let mut ivc_proof_serialized = vec![];
        assert!(ivc_proof
            .serialize_compressed(&mut ivc_proof_serialized)
            .is_ok());
        // deserialize IVCProof
        let ivc_proof_deserialized =
            FS::IVCProof::deserialize_compressed(ivc_proof_serialized.as_slice())?;

        // verify the last IVCProof from the recovered from serialization FS
        FS::verify(fs_vp_deserialized.clone(), ivc_proof_deserialized)?;

        Ok(())
    }
}
