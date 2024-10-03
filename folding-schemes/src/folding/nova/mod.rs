/// Implements the scheme described in [Nova](https://eprint.iacr.org/2021/370.pdf) and
/// [CycleFold](https://eprint.iacr.org/2023/1192.pdf).
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
use decider_eth_circuit::WitnessVar;

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
use crate::FoldingScheme;
use crate::{
    arith::r1cs::{extract_r1cs, extract_w_x, R1CS},
    constants::NOVA_N_BITS_RO,
    utils::{get_cm_coordinates, pp_hash},
};
use crate::{arith::Arith, commitment::CommitmentScheme};

pub mod circuits;
pub mod nifs;
pub mod ova;
pub mod serialize;
pub mod traits;
pub mod zk;

use circuits::{AugmentedFCircuit, ChallengeGadget, CommittedInstanceVar};
use nifs::NIFS;
use traits::NIFSTrait;

// offchain decider
pub mod decider;
pub mod decider_circuits;
// onchain decider
pub mod decider_eth;
pub mod decider_eth_circuit;

use super::traits::{CommittedInstanceOps, WitnessOps};

/// Configuration for Nova's CycleFold circuit
pub struct NovaCycleFoldConfig<C: CurveGroup> {
    _c: PhantomData<C>,
}

impl<C: CurveGroup> CycleFoldConfig for NovaCycleFoldConfig<C> {
    const RANDOMNESS_BIT_LENGTH: usize = NOVA_N_BITS_RO;
    // Number of points to be folded in the CycleFold circuit, in Nova's case, this is a fixed
    // amount:
    // 2 points to be folded.
    const N_INPUT_POINTS: usize = 2;
    type C = C;
    type F = C::BaseField;
}

/// CycleFold circuit for computing random linear combinations of group elements
/// in Nova instances.
pub type NovaCycleFoldCircuit<C, GC> = CycleFoldCircuit<NovaCycleFoldConfig<C>, GC>;

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommittedInstance<C: CurveGroup> {
    pub cmE: C,
    pub u: C::ScalarField,
    pub cmW: C,
    pub x: Vec<C::ScalarField>,
}

impl<C: CurveGroup> Dummy<usize> for CommittedInstance<C> {
    fn dummy(io_len: usize) -> Self {
        Self {
            cmE: C::zero(),
            u: CF1::<C>::zero(),
            cmW: C::zero(),
            x: vec![CF1::<C>::zero(); io_len],
        }
    }
}

impl<C: CurveGroup> Dummy<&R1CS<CF1<C>>> for CommittedInstance<C> {
    fn dummy(r1cs: &R1CS<CF1<C>>) -> Self {
        Self::dummy(r1cs.l)
    }
}

impl<C: CurveGroup> Absorb for CommittedInstance<C>
where
    C::ScalarField: Absorb,
{
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        C::ScalarField::batch_to_sponge_bytes(&self.to_sponge_field_elements_as_vec(), dest);
    }

    fn to_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        self.u.to_sponge_field_elements(dest);
        self.x.to_sponge_field_elements(dest);
        // We cannot call `to_native_sponge_field_elements(dest)` directly, as
        // `to_native_sponge_field_elements` needs `F` to be `C::ScalarField`,
        // but here `F` is a generic `PrimeField`.
        self.cmE
            .to_native_sponge_field_elements_as_vec()
            .to_sponge_field_elements(dest);
        self.cmW
            .to_native_sponge_field_elements_as_vec()
            .to_sponge_field_elements(dest);
    }
}

impl<C: CurveGroup> CommittedInstanceOps<C> for CommittedInstance<C> {
    type Var = CommittedInstanceVar<C>;

    fn get_commitments(&self) -> Vec<C> {
        vec![self.cmW, self.cmE]
    }

    fn is_incoming(&self) -> bool {
        self.cmE == C::zero() && self.u == One::one()
    }
}

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Witness<C: CurveGroup> {
    pub E: Vec<C::ScalarField>,
    pub rE: C::ScalarField,
    pub W: Vec<C::ScalarField>,
    pub rW: C::ScalarField,
}

impl<C: CurveGroup> Witness<C> {
    pub fn new<const H: bool>(w: Vec<C::ScalarField>, e_len: usize, mut rng: impl RngCore) -> Self {
        let (rW, rE) = if H {
            (
                C::ScalarField::rand(&mut rng),
                C::ScalarField::rand(&mut rng),
            )
        } else {
            (C::ScalarField::zero(), C::ScalarField::zero())
        };

        Self {
            E: vec![C::ScalarField::zero(); e_len],
            rE,
            W: w,
            rW,
        }
    }

    pub fn commit<CS: CommitmentScheme<C, HC>, const HC: bool>(
        &self,
        params: &CS::ProverParams,
        x: Vec<C::ScalarField>,
    ) -> Result<CommittedInstance<C>, Error> {
        let mut cmE = C::zero();
        if !is_zero_vec::<C::ScalarField>(&self.E) {
            cmE = CS::commit(params, &self.E, &self.rE)?;
        }
        let cmW = CS::commit(params, &self.W, &self.rW)?;
        Ok(CommittedInstance {
            cmE,
            u: C::ScalarField::one(),
            cmW,
            x,
        })
    }
}

impl<C: CurveGroup> Dummy<&R1CS<CF1<C>>> for Witness<C> {
    fn dummy(r1cs: &R1CS<CF1<C>>) -> Self {
        Self {
            E: vec![C::ScalarField::zero(); r1cs.A.n_rows],
            rE: C::ScalarField::zero(),
            W: vec![C::ScalarField::zero(); r1cs.A.n_cols - 1 - r1cs.l],
            rW: C::ScalarField::zero(),
        }
    }
}

impl<C: CurveGroup> WitnessOps<C::ScalarField> for Witness<C> {
    type Var = WitnessVar<C>;

    fn get_openings(&self) -> Vec<(&[C::ScalarField], C::ScalarField)> {
        vec![(&self.W, self.rW), (&self.E, self.rE)]
    }
}

#[derive(Debug, Clone)]
pub struct PreprocessorParam<C1, C2, FC, CS1, CS2, const H: bool = false>
where
    C1: CurveGroup,
    C2: CurveGroup,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    pub F: FC,
    // cs params if not provided, will be generated at the preprocess method
    pub cs_pp: Option<CS1::ProverParams>,
    pub cs_vp: Option<CS1::VerifierParams>,
    pub cf_cs_pp: Option<CS2::ProverParams>,
    pub cf_cs_vp: Option<CS2::VerifierParams>,
}

impl<C1, C2, FC, CS1, CS2, const H: bool> PreprocessorParam<C1, C2, FC, CS1, CS2, H>
where
    C1: CurveGroup,
    C2: CurveGroup,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    pub fn new(poseidon_config: PoseidonConfig<C1::ScalarField>, F: FC) -> Self {
        Self {
            poseidon_config,
            F,
            cs_pp: None,
            cs_vp: None,
            cf_cs_pp: None,
            cf_cs_vp: None,
        }
    }
}

/// Proving parameters for Nova-based IVC
#[derive(Debug, Clone)]
pub struct ProverParams<C1, C2, CS1, CS2, const H: bool = false>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    /// Poseidon sponge configuration
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    /// Proving parameters of the underlying commitment scheme over C1
    pub cs_pp: CS1::ProverParams,
    /// Proving parameters of the underlying commitment scheme over C2
    pub cf_cs_pp: CS2::ProverParams,
}

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

/// Verification parameters for Nova-based IVC
#[derive(Debug, Clone)]
pub struct VerifierParams<C1, C2, CS1, CS2, const H: bool = false>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    /// Poseidon sponge configuration
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    /// R1CS of the Augmented step circuit
    pub r1cs: R1CS<C1::ScalarField>,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: R1CS<C2::ScalarField>,
    /// Verification parameters of the underlying commitment scheme over C1
    pub cs_vp: CS1::VerifierParams,
    /// Verification parameters of the underlying commitment scheme over C2
    pub cf_cs_vp: CS2::VerifierParams,
}

impl<C1, C2, CS1, CS2, const H: bool> Valid for VerifierParams<C1, C2, CS1, CS2, H>
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
        self.r1cs.check()?;
        self.cf_r1cs.check()?;
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
        self.r1cs.serialize_with_mode(&mut writer, compress)?;
        self.cf_r1cs.serialize_with_mode(&mut writer, compress)?;
        self.cs_vp.serialize_with_mode(&mut writer, compress)?;
        self.cf_cs_vp.serialize_with_mode(&mut writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        self.r1cs.serialized_size(compress)
            + self.cf_r1cs.serialized_size(compress)
            + self.cs_vp.serialized_size(compress)
            + self.cf_cs_vp.serialized_size(compress)
    }
}
impl<C1, C2, CS1, CS2, const H: bool> CanonicalDeserialize for VerifierParams<C1, C2, CS1, CS2, H>
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
        let r1cs = R1CS::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_r1cs = R1CS::deserialize_with_mode(&mut reader, compress, validate)?;
        let cs_vp = CS1::VerifierParams::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_cs_vp = CS2::VerifierParams::deserialize_with_mode(&mut reader, compress, validate)?;
        Ok(VerifierParams {
            poseidon_config: poseidon_canonical_config::<C1::ScalarField>(),
            r1cs,
            cf_r1cs,
            cs_vp,
            cf_cs_vp,
        })
    }
}

impl<C1, C2, CS1, CS2, const H: bool> VerifierParams<C1, C2, CS1, CS2, H>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    /// returns the hash of the public parameters of Nova
    pub fn pp_hash(&self) -> Result<C1::ScalarField, Error> {
        pp_hash::<C1, C2, CS1, CS2, H>(
            &self.r1cs,
            &self.cf_r1cs,
            &self.cs_vp,
            &self.cf_cs_vp,
            &self.poseidon_config,
        )
    }
}

/// Implements Nova+CycleFold's IVC, described in [Nova](https://eprint.iacr.org/2021/370.pdf) and
/// [CycleFold](https://eprint.iacr.org/2023/1192.pdf), following the FoldingScheme trait
/// The `H` const generic specifies whether the homorphic commitment scheme is blinding
#[derive(Clone, Debug)]
pub struct Nova<C1, GC1, C2, GC2, FC, CS1, CS2, const H: bool = false>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,
    /// R1CS of the Augmented Function circuit
    pub r1cs: R1CS<C1::ScalarField>,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: R1CS<C2::ScalarField>,
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    /// CommitmentScheme::ProverParams over C1
    pub cs_pp: CS1::ProverParams,
    /// CycleFold CommitmentScheme::ProverParams, over C2
    pub cf_cs_pp: CS2::ProverParams,
    /// F circuit, the circuit that is being folded
    pub F: FC,
    /// public params hash
    pub pp_hash: C1::ScalarField,
    pub i: C1::ScalarField,
    /// initial state
    pub z_0: Vec<C1::ScalarField>,
    /// current i-th state
    pub z_i: Vec<C1::ScalarField>,
    /// Nova instances
    pub w_i: Witness<C1>,
    pub u_i: CommittedInstance<C1>,
    pub W_i: Witness<C1>,
    pub U_i: CommittedInstance<C1>,

    /// CycleFold running instance
    pub cf_W_i: CycleFoldWitness<C2>,
    pub cf_U_i: CycleFoldCommittedInstance<C2>,
}

impl<C1, GC1, C2, GC2, FC, CS1, CS2, const H: bool> FoldingScheme<C1, C2, FC>
    for Nova<C1, GC1, C2, GC2, FC, CS1, CS2, H>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
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
    type PreprocessorParam = PreprocessorParam<C1, C2, FC, CS1, CS2, H>;
    type ProverParam = ProverParams<C1, C2, CS1, CS2, H>;
    type VerifierParam = VerifierParams<C1, C2, CS1, CS2, H>;
    type RunningInstance = (CommittedInstance<C1>, Witness<C1>);
    type IncomingInstance = (CommittedInstance<C1>, Witness<C1>);
    type MultiCommittedInstanceWithWitness = ();
    type CFInstance = (CycleFoldCommittedInstance<C2>, CycleFoldWitness<C2>);

    fn preprocess(
        mut rng: impl RngCore,
        prep_param: &Self::PreprocessorParam,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        let (r1cs, cf_r1cs) =
            get_r1cs::<C1, GC1, C2, GC2, FC>(&prep_param.poseidon_config, prep_param.F.clone())?;

        // if cs params exist, use them, if not, generate new ones
        let cs_pp: CS1::ProverParams;
        let cs_vp: CS1::VerifierParams;
        let cf_cs_pp: CS2::ProverParams;
        let cf_cs_vp: CS2::VerifierParams;
        if prep_param.cs_pp.is_some()
            && prep_param.cf_cs_pp.is_some()
            && prep_param.cs_vp.is_some()
            && prep_param.cf_cs_vp.is_some()
        {
            cs_pp = prep_param.clone().cs_pp.unwrap();
            cs_vp = prep_param.clone().cs_vp.unwrap();
            cf_cs_pp = prep_param.clone().cf_cs_pp.unwrap();
            cf_cs_vp = prep_param.clone().cf_cs_vp.unwrap();
        } else {
            (cs_pp, cs_vp) = CS1::setup(&mut rng, r1cs.A.n_rows)?;
            (cf_cs_pp, cf_cs_vp) = CS2::setup(&mut rng, cf_r1cs.A.n_rows)?;
        }

        let prover_params = ProverParams::<C1, C2, CS1, CS2, H> {
            poseidon_config: prep_param.poseidon_config.clone(),
            cs_pp: cs_pp.clone(),
            cf_cs_pp: cf_cs_pp.clone(),
        };
        let verifier_params = VerifierParams::<C1, C2, CS1, CS2, H> {
            poseidon_config: prep_param.poseidon_config.clone(),
            r1cs,
            cf_r1cs,
            cs_vp,
            cf_cs_vp,
        };

        Ok((prover_params, verifier_params))
    }

    /// Initializes the Nova+CycleFold's IVC for the given parameters and initial state `z_0`.
    fn init(
        params: &(Self::ProverParam, Self::VerifierParam),
        F: FC,
        z_0: Vec<C1::ScalarField>,
    ) -> Result<Self, Error> {
        let (pp, vp) = params;

        // prepare the circuit to obtain its R1CS
        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();

        let augmented_F_circuit =
            AugmentedFCircuit::<C1, C2, GC2, FC>::empty(&pp.poseidon_config, F.clone());
        let cf_circuit = NovaCycleFoldCircuit::<C1, GC1>::empty();

        augmented_F_circuit.generate_constraints(cs.clone())?;
        cs.finalize();
        let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let r1cs = extract_r1cs::<C1::ScalarField>(&cs);

        cf_circuit.generate_constraints(cs2.clone())?;
        cs2.finalize();
        let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let cf_r1cs = extract_r1cs::<C1::BaseField>(&cs2);

        // compute the public params hash
        let pp_hash = vp.pp_hash()?;

        // setup the dummy instances
        let (W_dummy, U_dummy) = r1cs.dummy_witness_instance();
        let (w_dummy, u_dummy) = r1cs.dummy_witness_instance();
        let (cf_W_dummy, cf_U_dummy) = cf_r1cs.dummy_witness_instance();

        // W_dummy=W_0 is a 'dummy witness', all zeroes, but with the size corresponding to the
        // R1CS that we're working with.
        Ok(Self {
            _gc1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,
            r1cs,
            cf_r1cs,
            poseidon_config: pp.poseidon_config.clone(),
            cs_pp: pp.cs_pp.clone(),
            cf_cs_pp: pp.cf_cs_pp.clone(),
            F,
            pp_hash,
            i: C1::ScalarField::zero(),
            z_0: z_0.clone(),
            z_i: z_0,
            w_i: w_dummy,
            u_i: u_dummy,
            W_i: W_dummy,
            U_i: U_dummy,
            // cyclefold running instance
            cf_W_i: cf_W_dummy,
            cf_U_i: cf_U_dummy,
        })
    }

    /// Implements IVC.P of Nova+CycleFold
    fn prove_step(
        &mut self,
        mut rng: impl RngCore,
        external_inputs: Vec<C1::ScalarField>,
        // Nova does not support multi-instances folding
        _other_instances: Option<Self::MultiCommittedInstanceWithWitness>,
    ) -> Result<(), Error> {
        // ensure that commitments are blinding if user has specified so.
        if H && self.i >= C1::ScalarField::one() {
            let blinding_commitments = if self.i == C1::ScalarField::one() {
                // blinding values of the running instances are zero at the first iteration
                vec![self.w_i.rW, self.w_i.rE]
            } else {
                vec![self.w_i.rW, self.w_i.rE, self.W_i.rW, self.W_i.rE]
            };
            if blinding_commitments.contains(&C1::ScalarField::zero()) {
                return Err(Error::IncorrectBlinding(
                    H,
                    format!("{:?}", blinding_commitments),
                ));
            }
        }
        // `sponge` is for digest computation.
        let sponge = PoseidonSponge::<C1::ScalarField>::new(&self.poseidon_config);
        // `transcript` is for challenge generation.
        let mut transcript = sponge.clone();

        let augmented_F_circuit: AugmentedFCircuit<C1, C2, GC2, FC>;

        // Nova does not support (by design) multi-instances folding
        if _other_instances.is_some() {
            return Err(Error::NoMultiInstances);
        }

        if self.z_i.len() != self.F.state_len() {
            return Err(Error::NotSameLength(
                "z_i.len()".to_string(),
                self.z_i.len(),
                "F.state_len()".to_string(),
                self.F.state_len(),
            ));
        }
        if external_inputs.len() != self.F.external_inputs_len() {
            return Err(Error::NotSameLength(
                "F.external_inputs_len()".to_string(),
                self.F.external_inputs_len(),
                "external_inputs.len()".to_string(),
                external_inputs.len(),
            ));
        }

        if self.i > C1::ScalarField::from_le_bytes_mod_order(&usize::MAX.to_le_bytes()) {
            return Err(Error::MaxStep);
        }

        let i_usize;

        #[cfg(target_pointer_width = "64")]
        {
            let mut i_bytes: [u8; 8] = [0; 8];
            i_bytes.copy_from_slice(&self.i.into_bigint().to_bytes_le()[..8]);
            i_usize = usize::from_le_bytes(i_bytes);
        }

        #[cfg(target_pointer_width = "32")]
        {
            let mut i_bytes: [u8; 4] = [0; 4];
            i_bytes.copy_from_slice(&self.i.into_bigint().to_bytes_le()[..4]);
            i_usize = usize::from_le_bytes(i_bytes);
        }

        let z_i1 = self
            .F
            .step_native(i_usize, self.z_i.clone(), external_inputs.clone())?;

        // compute T and cmT for AugmentedFCircuit
        let (aux_p, aux_v) = self.compute_cmT()?;
        let cmT = aux_v;

        // r_bits is the r used to the RLC of the F' instances
        let r_bits = ChallengeGadget::<C1, CommittedInstance<C1>>::get_challenge_native(
            &mut transcript,
            self.pp_hash,
            &self.U_i,
            &self.u_i,
            Some(&cmT),
        );
        let r_Fr = C1::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits))
            .ok_or(Error::OutOfBounds)?;
        let r_Fq = C1::BaseField::from_bigint(BigInteger::from_bits_le(&r_bits))
            .ok_or(Error::OutOfBounds)?;

        // fold Nova instances
        let (W_i1, U_i1): (Witness<C1>, CommittedInstance<C1>) = NIFS::<C1, CS1, H>::prove(
            r_Fr, &self.W_i, &self.U_i, &self.w_i, &self.u_i, &aux_p, &aux_v,
        )?;

        // folded instance output (public input, x)
        // u_{i+1}.x[0] = H(i+1, z_0, z_{i+1}, U_{i+1})
        let u_i1_x = U_i1.hash(
            &sponge,
            self.pp_hash,
            self.i + C1::ScalarField::one(),
            &self.z_0,
            &z_i1,
        );
        // u_{i+1}.x[1] = H(cf_U_{i+1})
        let cf_u_i1_x: C1::ScalarField;

        if self.i == C1::ScalarField::zero() {
            cf_u_i1_x = self.cf_U_i.hash_cyclefold(&sponge, self.pp_hash);
            // base case
            augmented_F_circuit = AugmentedFCircuit::<C1, C2, GC2, FC> {
                _gc2: PhantomData,
                poseidon_config: self.poseidon_config.clone(),
                pp_hash: Some(self.pp_hash),
                i: Some(C1::ScalarField::zero()), // = i=0
                i_usize: Some(0),
                z_0: Some(self.z_0.clone()), // = z_i
                z_i: Some(self.z_i.clone()),
                external_inputs: Some(external_inputs.clone()),
                u_i_cmW: Some(self.u_i.cmW), // = dummy
                U_i: Some(self.U_i.clone()), // = dummy
                U_i1_cmE: Some(U_i1.cmE),
                U_i1_cmW: Some(U_i1.cmW),
                cmT: Some(cmT),
                F: self.F.clone(),
                x: Some(u_i1_x),
                cf1_u_i_cmW: None,
                cf2_u_i_cmW: None,
                cf_U_i: None,
                cf1_cmT: None,
                cf2_cmT: None,
                cf_x: Some(cf_u_i1_x),
            };

            #[cfg(test)]
            NIFS::<C1, CS1, H>::verify_folded_instance(r_Fr, &self.U_i, &self.u_i, &U_i1, &cmT)?;
        } else {
            // CycleFold part:
            // get the vector used as public inputs 'x' in the CycleFold circuit
            // cyclefold circuit for cmW
            let cfW_u_i_x = [
                vec![r_Fq],
                get_cm_coordinates(&self.U_i.cmW),
                get_cm_coordinates(&self.u_i.cmW),
                get_cm_coordinates(&U_i1.cmW),
            ]
            .concat();
            // cyclefold circuit for cmE
            let cfE_u_i_x = [
                vec![r_Fq],
                get_cm_coordinates(&self.U_i.cmE),
                get_cm_coordinates(&cmT),
                get_cm_coordinates(&U_i1.cmE),
            ]
            .concat();

            let cfW_circuit = NovaCycleFoldCircuit::<C1, GC1> {
                _gc: PhantomData,
                r_bits: Some(r_bits.clone()),
                points: Some(vec![self.U_i.clone().cmW, self.u_i.clone().cmW]),
                x: Some(cfW_u_i_x.clone()),
            };
            let cfE_circuit = NovaCycleFoldCircuit::<C1, GC1> {
                _gc: PhantomData,
                r_bits: Some(r_bits.clone()),
                points: Some(vec![self.U_i.clone().cmE, cmT]),
                x: Some(cfE_u_i_x.clone()),
            };

            // fold self.cf_U_i + cfW_U -> folded running with cfW
            let (_cfW_w_i, cfW_u_i, cfW_W_i1, cfW_U_i1, cfW_cmT, _) = self.fold_cyclefold_circuit(
                &mut transcript,
                self.cf_W_i.clone(), // CycleFold running instance witness
                self.cf_U_i.clone(), // CycleFold running instance
                cfW_u_i_x,
                cfW_circuit,
                &mut rng,
            )?;
            // fold [the output from folding self.cf_U_i + cfW_U] + cfE_U = folded_running_with_cfW + cfE
            let (_cfE_w_i, cfE_u_i, cf_W_i1, cf_U_i1, cf_cmT, _) = self.fold_cyclefold_circuit(
                &mut transcript,
                cfW_W_i1,
                cfW_U_i1.clone(),
                cfE_u_i_x,
                cfE_circuit,
                &mut rng,
            )?;

            cf_u_i1_x = cf_U_i1.hash_cyclefold(&sponge, self.pp_hash);

            augmented_F_circuit = AugmentedFCircuit::<C1, C2, GC2, FC> {
                _gc2: PhantomData,
                poseidon_config: self.poseidon_config.clone(),
                pp_hash: Some(self.pp_hash),
                i: Some(self.i),
                i_usize: Some(i_usize),
                z_0: Some(self.z_0.clone()),
                z_i: Some(self.z_i.clone()),
                external_inputs: Some(external_inputs.clone()),
                u_i_cmW: Some(self.u_i.cmW),
                U_i: Some(self.U_i.clone()),
                U_i1_cmE: Some(U_i1.cmE),
                U_i1_cmW: Some(U_i1.cmW),
                cmT: Some(cmT),
                F: self.F.clone(),
                x: Some(u_i1_x),
                // cyclefold values
                cf1_u_i_cmW: Some(cfW_u_i.cmW),
                cf2_u_i_cmW: Some(cfE_u_i.cmW),
                cf_U_i: Some(self.cf_U_i.clone()),
                cf1_cmT: Some(cfW_cmT),
                cf2_cmT: Some(cf_cmT),
                cf_x: Some(cf_u_i1_x),
            };

            self.cf_W_i = cf_W_i1;
            self.cf_U_i = cf_U_i1;

            #[cfg(test)]
            {
                cfW_u_i.check_incoming()?;
                cfE_u_i.check_incoming()?;
                self.cf_r1cs.check_relation(&_cfW_w_i, &cfW_u_i)?;
                self.cf_r1cs.check_relation(&_cfE_w_i, &cfE_u_i)?;
                self.cf_r1cs.check_relation(&self.cf_W_i, &self.cf_U_i)?;
            }
        }

        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();

        augmented_F_circuit.generate_constraints(cs.clone())?;

        #[cfg(test)]
        assert!(cs.is_satisfied().unwrap());

        let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let (w_i1, x_i1) = extract_w_x::<C1::ScalarField>(&cs);
        if x_i1[0] != u_i1_x || x_i1[1] != cf_u_i1_x {
            return Err(Error::NotEqual);
        }

        #[cfg(test)]
        if x_i1.len() != 2 {
            return Err(Error::NotExpectedLength(x_i1.len(), 2));
        }

        // set values for next iteration
        self.i += C1::ScalarField::one();
        self.z_i = z_i1;
        self.w_i = Witness::<C1>::new::<H>(w_i1, self.r1cs.A.n_rows, &mut rng);
        self.u_i = self.w_i.commit::<CS1, H>(&self.cs_pp, x_i1)?;
        self.W_i = W_i1;
        self.U_i = U_i1;

        #[cfg(test)]
        {
            self.u_i.check_incoming()?;
            self.r1cs.check_relation(&self.w_i, &self.u_i)?;
            self.r1cs.check_relation(&self.W_i, &self.U_i)?;
        }

        Ok(())
    }

    fn state(&self) -> Vec<C1::ScalarField> {
        self.z_i.clone()
    }

    fn instances(
        &self,
    ) -> (
        Self::RunningInstance,
        Self::IncomingInstance,
        Self::CFInstance,
    ) {
        (
            (self.U_i.clone(), self.W_i.clone()),
            (self.u_i.clone(), self.w_i.clone()),
            (self.cf_U_i.clone(), self.cf_W_i.clone()),
        )
    }

    /// Implements IVC.V of Nova+CycleFold. Notice that this method does not include the
    /// commitments verification, which is done in the Decider.
    fn verify(
        vp: Self::VerifierParam,
        z_0: Vec<C1::ScalarField>, // initial state
        z_i: Vec<C1::ScalarField>, // last state
        num_steps: C1::ScalarField,
        running_instance: Self::RunningInstance,
        incoming_instance: Self::IncomingInstance,
        cyclefold_instance: Self::CFInstance,
    ) -> Result<(), Error> {
        let sponge = PoseidonSponge::<C1::ScalarField>::new(&vp.poseidon_config);

        if num_steps == C1::ScalarField::zero() {
            if z_0 != z_i {
                return Err(Error::IVCVerificationFail);
            }
            return Ok(());
        }

        let (U_i, W_i) = running_instance;
        let (u_i, w_i) = incoming_instance;
        let (cf_U_i, cf_W_i) = cyclefold_instance;

        if u_i.x.len() != 2 || U_i.x.len() != 2 {
            return Err(Error::IVCVerificationFail);
        }

        let pp_hash = vp.pp_hash()?;

        // check that u_i's output points to the running instance
        // u_i.X[0] == H(i, z_0, z_i, U_i)
        let expected_u_i_x = U_i.hash(&sponge, pp_hash, num_steps, &z_0, &z_i);
        if expected_u_i_x != u_i.x[0] {
            return Err(Error::IVCVerificationFail);
        }
        // u_i.X[1] == H(cf_U_i)
        let expected_cf_u_i_x = cf_U_i.hash_cyclefold(&sponge, pp_hash);
        if expected_cf_u_i_x != u_i.x[1] {
            return Err(Error::IVCVerificationFail);
        }

        // check R1CS satisfiability, which is equivalent to checking if `u_i`
        // is an incoming instance and if `w_i` and `u_i` satisfy RelaxedR1CS
        u_i.check_incoming()?;
        vp.r1cs.check_relation(&w_i, &u_i)?;
        // check RelaxedR1CS satisfiability
        vp.r1cs.check_relation(&W_i, &U_i)?;

        // check CycleFold RelaxedR1CS satisfiability
        vp.cf_r1cs.check_relation(&cf_W_i, &cf_U_i)?;

        Ok(())
    }
}

impl<C1, GC1, C2, GC2, FC, CS1, CS2, const H: bool> Nova<C1, GC1, C2, GC2, FC, CS1, CS2, H>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
{
    // computes T and cmT for the AugmentedFCircuit
    fn compute_cmT(&self) -> Result<(Vec<C1::ScalarField>, C1), Error> {
        NIFS::<C1, CS1, H>::compute_aux(
            &self.cs_pp,
            &self.r1cs,
            &self.w_i,
            &self.u_i,
            &self.W_i,
            &self.U_i,
        )
    }
}

impl<C1, GC1, C2, GC2, FC, CS1, CS2, const H: bool> Nova<C1, GC1, C2, GC2, FC, CS1, CS2, H>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
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
    // folds the given cyclefold circuit and its instances
    #[allow(clippy::type_complexity)]
    fn fold_cyclefold_circuit<T: Transcript<C1::ScalarField>>(
        &self,
        transcript: &mut T,
        cf_W_i: CycleFoldWitness<C2>, // witness of the running instance
        cf_U_i: CycleFoldCommittedInstance<C2>, // running instance
        cf_u_i_x: Vec<C2::ScalarField>,
        cf_circuit: NovaCycleFoldCircuit<C1, GC1>,
        rng: &mut impl RngCore,
    ) -> Result<
        (
            CycleFoldWitness<C2>,
            CycleFoldCommittedInstance<C2>, // u_i
            CycleFoldWitness<C2>,           // W_i1
            CycleFoldCommittedInstance<C2>, // U_i1
            C2,                             // cmT
            C2::ScalarField,                // r_Fq
        ),
        Error,
    > {
        fold_cyclefold_circuit::<NovaCycleFoldConfig<C1>, C1, GC1, C2, GC2, CS2, H>(
            transcript,
            self.cf_r1cs.clone(),
            self.cf_cs_pp.clone(),
            self.pp_hash,
            cf_W_i,
            cf_U_i,
            cf_u_i_x,
            cf_circuit,
            rng,
        )
    }
}

/// helper method to get the r1cs from the ConstraintSynthesizer
pub fn get_r1cs_from_cs<F: PrimeField>(
    circuit: impl ConstraintSynthesizer<F>,
) -> Result<R1CS<F>, Error> {
    let cs = ConstraintSystem::<F>::new_ref();
    circuit.generate_constraints(cs.clone())?;
    cs.finalize();
    let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
    let r1cs = extract_r1cs::<F>(&cs);
    Ok(r1cs)
}

/// helper method to get the R1CS for both the AugmentedFCircuit and the CycleFold circuit
#[allow(clippy::type_complexity)]
pub fn get_r1cs<C1, GC1, C2, GC2, FC>(
    poseidon_config: &PoseidonConfig<C1::ScalarField>,
    F_circuit: FC,
) -> Result<(R1CS<C1::ScalarField>, R1CS<C2::ScalarField>), Error>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    let augmented_F_circuit =
        AugmentedFCircuit::<C1, C2, GC2, FC>::empty(poseidon_config, F_circuit);
    let cf_circuit = NovaCycleFoldCircuit::<C1, GC1>::empty();
    let r1cs = get_r1cs_from_cs::<C1::ScalarField>(augmented_F_circuit)?;
    let cf_r1cs = get_r1cs_from_cs::<C2::ScalarField>(cf_circuit)?;
    Ok((r1cs, cf_r1cs))
}

/// helper method to get the pedersen params length for both the AugmentedFCircuit and the
/// CycleFold circuit
pub fn get_cs_params_len<C1, GC1, C2, GC2, FC>(
    poseidon_config: &PoseidonConfig<C1::ScalarField>,
    F_circuit: FC,
) -> Result<(usize, usize), Error>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    let (r1cs, cf_r1cs) = get_r1cs::<C1, GC1, C2, GC2, FC>(poseidon_config, F_circuit)?;
    Ok((r1cs.A.n_rows, cf_r1cs.A.n_rows))
}

#[cfg(test)]
pub mod tests {
    use crate::commitment::kzg::KZG;
    use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as Projective};
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};

    use super::*;
    use crate::commitment::pedersen::Pedersen;
    use crate::frontend::utils::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_canonical_config;

    /// This test tests the Nova+CycleFold IVC, and by consequence it is also testing the
    /// AugmentedFCircuit
    #[test]
    fn test_ivc() {
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();

        // run the test using Pedersen commitments on both sides of the curve cycle
        test_ivc_opt::<Pedersen<Projective>, Pedersen<Projective2>, false>(
            poseidon_config.clone(),
            F_circuit,
            3,
        );

        test_ivc_opt::<Pedersen<Projective, true>, Pedersen<Projective2, true>, true>(
            poseidon_config.clone(),
            F_circuit,
            3,
        );

        // run the test using KZG for the commitments on the main curve, and Pedersen for the
        // commitments on the secondary curve
        test_ivc_opt::<KZG<Bn254>, Pedersen<Projective2>, false>(poseidon_config, F_circuit, 3);
    }

    // test_ivc allowing to choose the CommitmentSchemes
    #[allow(clippy::type_complexity)]
    pub(crate) fn test_ivc_opt<
        CS1: CommitmentScheme<Projective, H>,
        CS2: CommitmentScheme<Projective2, H>,
        const H: bool,
    >(
        poseidon_config: PoseidonConfig<Fr>,
        F_circuit: CubicFCircuit<Fr>,
        num_steps: usize,
    ) -> (
        Vec<Fr>,
        Nova<Projective, GVar, Projective2, GVar2, CubicFCircuit<Fr>, CS1, CS2, H>,
    ) {
        let mut rng = ark_std::test_rng();

        let prep_param =
            PreprocessorParam::<Projective, Projective2, CubicFCircuit<Fr>, CS1, CS2, H> {
                poseidon_config,
                F: F_circuit,
                cs_pp: None,
                cs_vp: None,
                cf_cs_pp: None,
                cf_cs_vp: None,
            };
        let nova_params = Nova::<
            Projective,
            GVar,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
            CS1,
            CS2,
            H,
        >::preprocess(&mut rng, &prep_param)
        .unwrap();

        let z_0 = vec![Fr::from(3_u32)];
        let mut nova =
            Nova::<Projective, GVar, Projective2, GVar2, CubicFCircuit<Fr>, CS1, CS2, H>::init(
                &nova_params,
                F_circuit,
                z_0.clone(),
            )
            .unwrap();

        for _ in 0..num_steps {
            nova.prove_step(&mut rng, vec![], None).unwrap();
        }
        assert_eq!(Fr::from(num_steps as u32), nova.i);

        let (running_instance, incoming_instance, cyclefold_instance) = nova.instances();
        Nova::<Projective, GVar, Projective2, GVar2, CubicFCircuit<Fr>, CS1, CS2, H>::verify(
            nova_params.1, // Nova's verifier params
            z_0.clone(),
            nova.z_i.clone(),
            nova.i,
            running_instance,
            incoming_instance,
            cyclefold_instance,
        )
        .unwrap();

        (z_0, nova)
    }
}
