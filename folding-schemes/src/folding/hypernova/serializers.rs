use ark_crypto_primitives::sponge::{
    poseidon::{PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{CurveGroup, Group};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{groups::GroupOpsBounds, prelude::CurveVar, ToConstraintFieldGadget};
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid,
};
use ark_std::{fmt::Debug, marker::PhantomData, rand::RngCore, One, Zero};

use super::{IVCProof, ProverParams, VerifierParams};
use crate::transcript::poseidon::poseidon_canonical_config;
use crate::{arith::Arith, commitment::CommitmentScheme};

impl<C1, C2, CS1, CS2, const H: bool> Valid for ProverParams<C1, C2, CS1, CS2, H>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        self.poseidon_config.full_rounds.check()?;
        self.poseidon_config.partial_rounds.check()?;
        self.poseidon_config.alpha.check()?;
        self.poseidon_config.ark.check()?;
        self.poseidon_config.mds.check()?;
        self.poseidon_config.rate.check()?;
        self.poseidon_config.capacity.check()?;
        self.cs_pp.check()?;
        self.cf_cs_pp.check()?;
        Ok(())
    }
}

impl<C1, C2, CS1, CS2, const H: bool> CanonicalDeserialize for ProverParams<C1, C2, CS1, CS2, H>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    fn deserialize_with_mode<R: std::io::prelude::Read>(
        mut reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        let cs_pp = CS1::ProverParams::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_cs_pp = CS2::ProverParams::deserialize_with_mode(&mut reader, compress, validate)?;
        Ok(ProverParams {
            poseidon_config: poseidon_canonical_config::<C1::ScalarField>(),
            cs_pp,
            cf_cs_pp,
            ccs: None,
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

impl<C1, C2, CS1, CS2, const H: bool> CanonicalSerialize for VerifierParams<C1, C2, CS1, CS2, H>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    fn serialize_with_mode<W: std::io::prelude::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.cs_vp.serialize_with_mode(&mut writer, compress)?;
        self.cf_cs_vp.serialize_with_mode(&mut writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        self.cs_vp.serialized_size(compress) + self.cf_cs_vp.serialized_size(compress)
    }
}
