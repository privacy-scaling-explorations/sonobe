/// Implements serializers & deserializers for the data structures.
use ark_crypto_primitives::sponge::{
    poseidon::{PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{CurveGroup, Group};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{groups::GroupOpsBounds, prelude::CurveVar, ToConstraintFieldGadget};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Valid};
use ark_std::fmt::Debug;
use ark_std::rand::RngCore;
use ark_std::{One, UniformRand, Zero};
use core::marker::PhantomData;

use super::decider_eth_circuit::WitnessVar;
use crate::folding::circuits::cyclefold::{
    fold_cyclefold_circuit, CycleFoldCircuit, CycleFoldCommittedInstance, CycleFoldConfig,
    CycleFoldWitness,
};
use crate::folding::{
    circuits::{CF1, CF2},
    traits::Dummy,
};
use crate::frontend::FCircuit;
use crate::transcript::{poseidon::poseidon_canonical_config, AbsorbNonNative, Transcript};
use crate::utils::vec::is_zero_vec;
use crate::Error;
use crate::{
    arith::r1cs::{extract_r1cs, extract_w_x, R1CS},
    constants::NOVA_N_BITS_RO,
    utils::{get_cm_coordinates, pp_hash},
};
use crate::{arith::Arith, commitment::CommitmentScheme};
use crate::{Compressible, FoldingScheme};

use super::{IVCProof, ProverParams, VerifierParams};

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

impl<C1, C2, CS1, CS2, const H: bool> CanonicalSerialize for ProverParams<C1, C2, CS1, CS2, H>
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
        self.cs_pp.serialize_with_mode(&mut writer, compress)?;
        self.cf_cs_pp.serialize_with_mode(&mut writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        self.cs_pp.serialized_size(compress) + self.cf_cs_pp.serialized_size(compress)
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
        })
    }
}

impl<C1, C2, CS1, CS2, const H: bool> Valid for VerifierParams<C1, C2, CS1, CS2, H>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        self.cs_vp.check()?;
        self.cf_cs_vp.check()?;
        Ok(())
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
