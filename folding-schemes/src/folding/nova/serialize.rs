pub use super::{CommittedInstance, Witness};
pub use crate::folding::circuits::CF2;
use crate::{ccs::r1cs::R1CS, commitment::CommitmentScheme, frontend::FCircuit};
use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_r1cs_std::groups::GroupOpsBounds;
use ark_r1cs_std::{groups::CurveVar, ToConstraintFieldGadget};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Write};
use std::marker::PhantomData;

use super::Nova;
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::Group;

impl<C1, GC1, C2, GC2, FC, CS1, CS2> CanonicalSerialize for Nova<C1, GC1, C2, GC2, FC, CS1, CS2>
where
    C1: CurveGroup,
    C2: CurveGroup,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    GC1: CurveVar<C1, <C2 as Group>::ScalarField>,
    GC1: ToConstraintFieldGadget<<C2 as Group>::ScalarField>,
    GC2: CurveVar<C2, <C2 as CurveGroup>::BaseField>,
    CS1::ProverParams: CanonicalSerialize,
    CS2::ProverParams: CanonicalSerialize,
{
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        // we serialize non-deterministic parameters
        self.cs_params.serialize_with_mode(&mut writer, compress)?;
        self.cf_cs_params
            .serialize_with_mode(&mut writer, compress)?;
        self.i.serialize_with_mode(&mut writer, compress)?;
        self.z_0.serialize_with_mode(&mut writer, compress)?;
        self.z_i.serialize_with_mode(&mut writer, compress)?;
        self.w_i.serialize_with_mode(&mut writer, compress)?;
        self.u_i.serialize_with_mode(&mut writer, compress)?;
        self.W_i.serialize_with_mode(&mut writer, compress)?;
        self.U_i.serialize_with_mode(&mut writer, compress)?;
        self.cf_W_i.serialize_with_mode(&mut writer, compress)?;
        self.cf_U_i.serialize_with_mode(&mut writer, compress)?;
        self.r1cs.serialize_with_mode(&mut writer, compress)?;
        self.cf_r1cs.serialize_with_mode(&mut writer, compress)?;
        // we serialize PoseidonConfig without implementing the `CanonicalDeserialize` trait
        // this is because we can not implement an external trait on an external type.
        self.poseidon_config
            .full_rounds
            .serialize_with_mode(&mut writer, compress)?;
        self.poseidon_config
            .partial_rounds
            .serialize_with_mode(&mut writer, compress)?;
        self.poseidon_config
            .alpha
            .serialize_with_mode(&mut writer, compress)?;
        self.poseidon_config
            .ark
            .serialize_with_mode(&mut writer, compress)?;
        self.poseidon_config
            .mds
            .serialize_with_mode(&mut writer, compress)?;
        self.poseidon_config
            .rate
            .serialize_with_mode(&mut writer, compress)?;
        self.poseidon_config
            .capacity
            .serialize_with_mode(&mut writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        self.cs_params.serialized_size(compress)
            + self.cf_cs_params.serialized_size(compress)
            + self.i.serialized_size(compress)
            + self.z_0.serialized_size(compress)
            + self.z_i.serialized_size(compress)
            + self.w_i.serialized_size(compress)
            + self.u_i.serialized_size(compress)
            + self.W_i.serialized_size(compress)
            + self.U_i.serialized_size(compress)
            + self.cf_W_i.serialized_size(compress)
            + self.cf_U_i.serialized_size(compress)
            + self.r1cs.serialized_size(compress)
            + self.cf_r1cs.serialized_size(compress)
            + self.poseidon_config.full_rounds.serialized_size(compress)
            + self
                .poseidon_config
                .partial_rounds
                .serialized_size(compress)
            + self.poseidon_config.alpha.serialized_size(compress)
            + self.poseidon_config.ark.serialized_size(compress)
            + self.poseidon_config.mds.serialized_size(compress)
            + self.poseidon_config.rate.serialized_size(compress)
            + self.poseidon_config.capacity.serialized_size(compress)
    }

    fn serialize_compressed<W: Write>(
        &self,
        writer: W,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.serialize_with_mode(writer, ark_serialize::Compress::Yes)
    }

    fn compressed_size(&self) -> usize {
        self.serialized_size(ark_serialize::Compress::Yes)
    }

    fn serialize_uncompressed<W: Write>(
        &self,
        writer: W,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.serialize_with_mode(writer, ark_serialize::Compress::No)
    }

    fn uncompressed_size(&self) -> usize {
        self.serialized_size(ark_serialize::Compress::No)
    }
}

// Note that we can't derive or implement `CanonicalDeserialize` directly.
// This is because `CurveVar` notably does not implement the `Sync` trait.
impl<C1, GC1, C2, GC2, FC, CS1, CS2> Nova<C1, GC1, C2, GC2, FC, CS1, CS2>
where
    C1: CurveGroup,
    C2: CurveGroup,
    FC: FCircuit<C1::ScalarField, Params = ()>,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    GC1: CurveVar<C1, <C2 as Group>::ScalarField>,
    GC1: ToConstraintFieldGadget<<C2 as Group>::ScalarField>,
    GC2: CurveVar<C2, <C2 as CurveGroup>::BaseField>,
    CS1::ProverParams: CanonicalDeserialize,
    CS2::ProverParams: CanonicalDeserialize,
{
    pub fn deserialize_nova<R: std::io::prelude::Read>(
        mut reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        let cs_params = CS1::ProverParams::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_cs_params =
            CS2::ProverParams::deserialize_with_mode(&mut reader, compress, validate)?;
        let i = C1::ScalarField::deserialize_with_mode(&mut reader, compress, validate)?;
        let z_0 = Vec::<C1::ScalarField>::deserialize_with_mode(&mut reader, compress, validate)?;
        let z_i = Vec::<C1::ScalarField>::deserialize_with_mode(&mut reader, compress, validate)?;
        let w_i = Witness::<C1>::deserialize_with_mode(&mut reader, compress, validate)?;
        let u_i = CommittedInstance::<C1>::deserialize_with_mode(&mut reader, compress, validate)?;
        let W_i = Witness::<C1>::deserialize_with_mode(&mut reader, compress, validate)?;
        let U_i = CommittedInstance::<C1>::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_W_i = Witness::<C2>::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_U_i =
            CommittedInstance::<C2>::deserialize_with_mode(&mut reader, compress, validate)?;
        let r1cs = R1CS::<C1::ScalarField>::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_r1cs =
            R1CS::<C2::ScalarField>::deserialize_with_mode(&mut reader, compress, validate)?;

        let full_rounds = usize::deserialize_with_mode(&mut reader, compress, validate)?;
        let partial_rounds = usize::deserialize_with_mode(&mut reader, compress, validate)?;
        let alpha = u64::deserialize_with_mode(&mut reader, compress, validate)?;
        let ark =
            Vec::<Vec<C1::ScalarField>>::deserialize_with_mode(&mut reader, compress, validate)?;
        let mds =
            Vec::<Vec<C1::ScalarField>>::deserialize_with_mode(&mut reader, compress, validate)?;
        let rate = usize::deserialize_with_mode(&mut reader, compress, validate)?;
        let capacity = usize::deserialize_with_mode(&mut reader, compress, validate)?;
        let f_circuit = FC::new(()).unwrap();
        let poseidon_config = PoseidonConfig {
            full_rounds,
            partial_rounds,
            alpha,
            ark,
            mds,
            rate,
            capacity,
        };

        Ok(Nova {
            _gc1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,
            cs_params,
            cf_cs_params,
            i,
            z_0,
            z_i,
            w_i,
            u_i,
            W_i,
            U_i,
            cf_W_i,
            cf_U_i,
            r1cs,
            cf_r1cs,
            poseidon_config,
            F: f_circuit,
        })
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{
        commitment::{
            kzg::{ProverKey as KZGProverKey, KZG},
            pedersen::Pedersen,
            CommitmentScheme,
        },
        folding::nova::{get_cs_params_len, Nova, ProverParams},
        frontend::{tests::CubicFCircuit, FCircuit},
        transcript::poseidon::poseidon_canonical_config,
        FoldingScheme,
    };
    use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as Projective};
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
    use ark_poly_commit::kzg10::VerifierKey as KZGVerifierKey;
    use ark_serialize::{CanonicalSerialize, Compress, Validate};
    use std::{fs, io::Write};

    #[test]
    fn test_serde_nova() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();
        let (cs_len, cf_cs_len) =
            get_cs_params_len::<Projective, GVar, Projective2, GVar2, CubicFCircuit<Fr>>(
                &poseidon_config,
                F_circuit,
            )
            .unwrap();
        let (kzg_pk, _): (KZGProverKey<Projective>, KZGVerifierKey<Bn254>) =
            KZG::<Bn254>::setup(&mut rng, cs_len).unwrap();
        let (cf_pedersen_params, _) = Pedersen::<Projective2>::setup(&mut rng, cf_cs_len).unwrap();

        // Initialize nova and make multiple `prove_step()`
        type NOVA<CS1, CS2> =
            Nova<Projective, GVar, Projective2, GVar2, CubicFCircuit<Fr>, CS1, CS2>;
        let prover_params =
            ProverParams::<Projective, Projective2, KZG<Bn254>, Pedersen<Projective2>> {
                poseidon_config: poseidon_config.clone(),
                cs_params: kzg_pk.clone(),
                cf_cs_params: cf_pedersen_params.clone(),
            };

        let z_0 = vec![Fr::from(3_u32)];
        let mut nova = NOVA::init(&prover_params, F_circuit, z_0.clone()).unwrap();

        let num_steps: usize = 3;
        for _ in 0..num_steps {
            nova.prove_step(vec![]).unwrap();
        }

        let mut writer = vec![];
        assert!(nova
            .serialize_with_mode(&mut writer, ark_serialize::Compress::No)
            .is_ok());

        let mut file = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .open("./nova.serde")
            .unwrap();

        file.write_all(&writer).unwrap();

        let bytes = fs::read("./nova.serde").unwrap();

        let mut deserialized_nova =
            Nova::<
                Projective,
                GVar,
                Projective2,
                GVar2,
                CubicFCircuit<Fr>,
                KZG<Bn254>,
                Pedersen<Projective2>,
            >::deserialize_nova(bytes.as_slice(), Compress::No, Validate::No)
            .unwrap();

        assert_eq!(nova.i, deserialized_nova.i);

        let num_steps: usize = 3;
        for _ in 0..num_steps {
            deserialized_nova.prove_step(vec![]).unwrap();
            nova.prove_step(vec![]).unwrap();
        }

        assert_eq!(deserialized_nova.w_i, nova.w_i);
    }
}
