use crate::arith::ccs::CCS;
use crate::arith::r1cs::R1CS;
use crate::folding::hypernova::ProverParams;
use crate::folding::hypernova::VerifierParams;
use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_r1cs_std::groups::{CurveVar, GroupOpsBounds};
use ark_r1cs_std::ToConstraintFieldGadget;
use ark_serialize::CanonicalDeserialize;
use ark_serialize::{CanonicalSerialize, Compress, SerializationError, Validate};
use ark_std::marker::PhantomData;

use crate::folding::hypernova::cccs::CCCS;
use crate::folding::hypernova::lcccs::LCCCS;
use crate::folding::hypernova::Witness;
use crate::folding::nova::{
    CommittedInstance as CycleFoldCommittedInstance, Witness as CycleFoldWitness,
};
use crate::FoldingScheme;
use crate::{
    commitment::CommitmentScheme,
    folding::{circuits::CF2, nova::PreprocessorParam},
    frontend::FCircuit,
};

use super::HyperNova;

impl<C1, GC1, C2, GC2, FC, CS1, CS2, const MU: usize, const NU: usize, const H: bool>
    CanonicalSerialize for HyperNova<C1, GC1, C2, GC2, FC, CS1, CS2, MU, NU, H>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    fn serialize_compressed<W: std::io::prelude::Write>(
        &self,
        writer: W,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.serialize_with_mode(writer, ark_serialize::Compress::Yes)
    }

    fn compressed_size(&self) -> usize {
        self.serialized_size(ark_serialize::Compress::Yes)
    }

    fn serialize_uncompressed<W: std::io::prelude::Write>(
        &self,
        writer: W,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.serialize_with_mode(writer, ark_serialize::Compress::No)
    }

    fn uncompressed_size(&self) -> usize {
        self.serialized_size(ark_serialize::Compress::No)
    }

    fn serialize_with_mode<W: std::io::prelude::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.pp_hash.serialize_with_mode(&mut writer, compress)?;
        self.i.serialize_with_mode(&mut writer, compress)?;
        self.z_0.serialize_with_mode(&mut writer, compress)?;
        self.z_i.serialize_with_mode(&mut writer, compress)?;
        self.W_i.serialize_with_mode(&mut writer, compress)?;
        self.U_i.serialize_with_mode(&mut writer, compress)?;
        self.w_i.serialize_with_mode(&mut writer, compress)?;
        self.u_i.serialize_with_mode(&mut writer, compress)?;
        self.cf_W_i.serialize_with_mode(&mut writer, compress)?;
        self.cf_U_i.serialize_with_mode(&mut writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        self.pp_hash.serialized_size(compress)
            + self.i.serialized_size(compress)
            + self.z_0.serialized_size(compress)
            + self.z_i.serialized_size(compress)
            + self.W_i.serialized_size(compress)
            + self.U_i.serialized_size(compress)
            + self.w_i.serialized_size(compress)
            + self.u_i.serialized_size(compress)
            + self.cf_W_i.serialized_size(compress)
            + self.cf_U_i.serialized_size(compress)
    }
}

impl<C1, GC1, C2, GC2, FC, CS1, CS2, const MU: usize, const NU: usize, const H: bool>
    HyperNova<C1, GC1, C2, GC2, FC, CS1, CS2, MU, NU, H>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField, Params = ()>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    #[allow(clippy::too_many_arguments)]
    pub fn deserialize_hypernova<R: std::io::prelude::Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
        poseidon_config: PoseidonConfig<C1::ScalarField>,
        cs_pp: CS1::ProverParams,
        cs_vp: CS1::VerifierParams,
        cf_cs_pp: CS2::ProverParams,
        cf_cs_vp: CS2::VerifierParams,
    ) -> Result<Self, SerializationError> {
        let f_circuit = FC::new(()).unwrap();
        let prep_param = PreprocessorParam {
            poseidon_config: poseidon_config.clone(),
            F: f_circuit.clone(),
            cs_pp: Some(cs_pp.clone()),
            cs_vp: Some(cs_vp.clone()),
            cf_cs_pp: Some(cf_cs_pp.clone()),
            cf_cs_vp: Some(cf_cs_vp.clone()),
        };
        // `test_rng` won't be used in `preprocess`, since parameters have already been initialized
        let (prover_params, verifier_params) = Self::preprocess(ark_std::test_rng(), &prep_param)
            .or(Err(SerializationError::InvalidData))?;
        let pp_hash = C1::ScalarField::deserialize_with_mode(&mut reader, compress, validate)?;
        let i = C1::ScalarField::deserialize_with_mode(&mut reader, compress, validate)?;
        let z_0 = Vec::<C1::ScalarField>::deserialize_with_mode(&mut reader, compress, validate)?;
        let z_i = Vec::<C1::ScalarField>::deserialize_with_mode(&mut reader, compress, validate)?;
        let W_i =
            Witness::<C1::ScalarField>::deserialize_with_mode(&mut reader, compress, validate)?;
        let U_i = LCCCS::<C1>::deserialize_with_mode(&mut reader, compress, validate)?;
        let w_i =
            Witness::<C1::ScalarField>::deserialize_with_mode(&mut reader, compress, validate)?;
        let u_i = CCCS::<C1>::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_W_i =
            CycleFoldWitness::<C2>::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_U_i = CycleFoldCommittedInstance::<C2>::deserialize_with_mode(
            &mut reader,
            compress,
            validate,
        )?;
        let ccs = prover_params.ccs.ok_or(SerializationError::InvalidData)?;

        Ok(HyperNova {
            _gc1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,
            ccs,
            cf_r1cs: verifier_params.cf_r1cs,
            poseidon_config,
            cs_pp,
            cf_cs_pp,
            F: f_circuit,
            pp_hash,
            i,
            z_0,
            z_i,
            W_i,
            U_i,
            w_i,
            u_i,
            cf_W_i,
            cf_U_i,
        })
    }
}

impl<
        C1: CurveGroup,
        C2: CurveGroup,
        CS1: CommitmentScheme<C1, H>,
        CS2: CommitmentScheme<C2, H>,
        const H: bool,
    > CanonicalSerialize for ProverParams<C1, C2, CS1, CS2, H>
{
    fn serialize_compressed<W: std::io::prelude::Write>(
        &self,
        writer: W,
    ) -> Result<(), SerializationError> {
        self.serialize_with_mode(writer, Compress::Yes)
    }

    fn compressed_size(&self) -> usize {
        self.serialized_size(Compress::Yes)
    }

    fn serialize_uncompressed<W: std::io::prelude::Write>(
        &self,
        writer: W,
    ) -> Result<(), SerializationError> {
        self.serialize_with_mode(writer, Compress::No)
    }

    fn uncompressed_size(&self) -> usize {
        self.serialized_size(Compress::No)
    }

    fn serialize_with_mode<W: std::io::prelude::Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.cs_pp.serialize_with_mode(&mut writer, compress)?;
        self.cf_cs_pp.serialize_with_mode(&mut writer, compress)
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        self.cs_pp.serialized_size(compress) + self.cf_cs_pp.serialized_size(compress)
    }
}

impl<
        C1: CurveGroup,
        C2: CurveGroup,
        CS1: CommitmentScheme<C1, H>,
        CS2: CommitmentScheme<C2, H>,
        const H: bool,
    > ProverParams<C1, C2, CS1, CS2, H>
{
    pub fn deserialize_prover_params<R: std::io::prelude::Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
        ccs: &Option<CCS<C1::ScalarField>>,
        poseidon_config: &PoseidonConfig<C1::ScalarField>,
    ) -> Result<Self, SerializationError> {
        let cs_pp = CS1::ProverParams::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_cs_pp = CS2::ProverParams::deserialize_with_mode(&mut reader, compress, validate)?;

        Ok(ProverParams {
            cs_pp,
            cf_cs_pp,
            ccs: ccs.clone(),
            poseidon_config: poseidon_config.clone(),
        })
    }
}

impl<
        C1: CurveGroup,
        C2: CurveGroup,
        CS1: CommitmentScheme<C1, H>,
        CS2: CommitmentScheme<C2, H>,
        const H: bool,
    > CanonicalSerialize for VerifierParams<C1, C2, CS1, CS2, H>
{
    fn serialize_compressed<W: std::io::prelude::Write>(
        &self,
        writer: W,
    ) -> Result<(), SerializationError> {
        self.serialize_with_mode(writer, Compress::Yes)
    }

    fn compressed_size(&self) -> usize {
        self.serialized_size(Compress::Yes)
    }

    fn serialize_uncompressed<W: std::io::prelude::Write>(
        &self,
        writer: W,
    ) -> Result<(), SerializationError> {
        self.serialize_with_mode(writer, Compress::No)
    }

    fn uncompressed_size(&self) -> usize {
        self.serialized_size(Compress::No)
    }

    fn serialize_with_mode<W: std::io::prelude::Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.cf_r1cs.serialize_with_mode(&mut writer, compress)?;
        self.cs_vp.serialize_with_mode(&mut writer, compress)?;
        self.cf_cs_vp.serialize_with_mode(&mut writer, compress)
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        self.cf_r1cs.serialized_size(compress)
            + self.cs_vp.serialized_size(compress)
            + self.cf_cs_vp.serialized_size(compress)
    }
}

impl<
        C1: CurveGroup,
        C2: CurveGroup,
        CS1: CommitmentScheme<C1, H>,
        CS2: CommitmentScheme<C2, H>,
        const H: bool,
    > VerifierParams<C1, C2, CS1, CS2, H>
{
    pub fn deserialize_verifier_params<R: std::io::Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
        ccs: &CCS<C1::ScalarField>,
        poseidon_config: &PoseidonConfig<C1::ScalarField>,
    ) -> Result<Self, SerializationError> {
        let cf_r1cs = R1CS::deserialize_with_mode(&mut reader, compress, validate)?;
        let cs_vp = CS1::VerifierParams::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_cs_vp = CS2::VerifierParams::deserialize_with_mode(&mut reader, compress, validate)?;
        Ok(VerifierParams {
            ccs: ccs.clone(),
            poseidon_config: poseidon_config.clone(),
            cf_r1cs,
            cs_vp,
            cf_cs_vp,
        })
    }
}

#[cfg(test)]
pub mod tests {
    use crate::FoldingScheme;
    use crate::MultiFolding;
    use ark_serialize::{Compress, Validate, Write};
    use std::fs;

    use crate::{
        commitment::{kzg::KZG, pedersen::Pedersen},
        folding::hypernova::{tests::test_ivc_opt, HyperNova},
        frontend::{utils::CubicFCircuit, FCircuit},
        transcript::poseidon::poseidon_canonical_config,
    };
    use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as Projective};
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
    use ark_serialize::CanonicalSerialize;

    #[test]
    fn test_serde_hypernova() {
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();
        let (mut hn, (_, verifier_params), _, _, _) = test_ivc_opt::<
            KZG<Bn254>,
            Pedersen<Projective2>,
            false,
        >(poseidon_config.clone(), F_circuit);

        let mut writer = vec![];
        assert!(hn.serialize_compressed(&mut writer).is_ok());
        let mut writer = vec![];
        assert!(hn.serialize_uncompressed(&mut writer).is_ok());

        let mut file = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .open("./hypernova.serde")
            .unwrap();

        file.write_all(&writer).unwrap();

        let bytes = fs::read("./hypernova.serde").unwrap();

        let mut hn_deserialized = HyperNova::<
            Projective,
            GVar,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
            KZG<Bn254>,
            Pedersen<Projective2>,
            2,
            3,
            false,
        >::deserialize_hypernova(
            bytes.as_slice(),
            Compress::No,
            Validate::No,
            poseidon_config,
            hn.cs_pp.clone(),
            verifier_params.cs_vp,
            hn.cf_cs_pp.clone(),
            verifier_params.cf_cs_vp,
        )
        .unwrap();

        assert_eq!(hn.i, hn_deserialized.i);

        let mut rng = ark_std::test_rng();
        for _ in 0..3 {
            // prepare some new instances to fold in the multifolding step
            let mut lcccs = vec![];
            for j in 0..1 {
                let instance_state = vec![Fr::from(j as u32 + 85_u32)];
                let (U, W) = hn
                    .new_running_instance(&mut rng, instance_state, vec![])
                    .unwrap();
                lcccs.push((U, W));
            }
            let mut cccs = vec![];
            for j in 0..2 {
                let instance_state = vec![Fr::from(j as u32 + 15_u32)];
                let (u, w) = hn
                    .new_incoming_instance(&mut rng, instance_state, vec![])
                    .unwrap();
                cccs.push((u, w));
            }

            hn.prove_step(&mut rng, vec![], Some((lcccs.clone(), cccs.clone())))
                .unwrap();
            hn_deserialized
                .prove_step(&mut rng, vec![], Some((lcccs, cccs)))
                .unwrap();
        }

        assert_eq!(hn.z_i, hn_deserialized.z_i);
    }
}
