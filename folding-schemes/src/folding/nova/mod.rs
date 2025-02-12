/// Implements the scheme described in [Nova](https://eprint.iacr.org/2021/370.pdf) and
/// [CycleFold](https://eprint.iacr.org/2023/1192.pdf).
///
/// The structure of the Nova code is the following:
/// - NIFS implementation for Nova (nifs.rs), Mova (mova.rs), Ova (ova.rs)
/// - IVC and the Decider (offchain Decider & onchain Decider) implementations for Nova
use ark_crypto_primitives::sponge::{
    poseidon::{PoseidonConfig, PoseidonSponge},
    Absorb,
};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{alloc::AllocVar, prelude::Boolean, R1CSVar};
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError, SynthesisMode,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Valid};
use ark_std::{fmt::Debug, rand::RngCore, One, UniformRand, Zero};
use num_bigint::BigUint;

use crate::{
    arith::{
        r1cs::{extract_r1cs, extract_w_x, R1CS},
        Arith,
    },
    commitment::CommitmentScheme,
    constants::NOVA_N_BITS_RO,
    folding::{
        circuits::{
            cyclefold::{
                CycleFoldAugmentationGadget, CycleFoldCommittedInstance, CycleFoldConfig,
                CycleFoldWitness,
            },
            CF1,
        },
        traits::Dummy,
    },
    frontend::{alloc::LookupConstraintSystem, logup::LogUp, FCircuit},
    transcript::{poseidon::poseidon_canonical_config, Transcript},
    utils::{pp_hash, vec::is_zero_vec},
    Curve, Error, FoldingScheme,
};
use decider_eth_circuit::WitnessVar;

pub mod circuits;
pub mod traits;
pub mod zk;

// NIFS related:
pub mod nifs;

use circuits::AugmentedFCircuit;
use nifs::{nova::NIFS, nova_circuits::CommittedInstanceVar, NIFSTrait};

// offchain decider
pub mod decider;
pub mod decider_circuits;
// onchain decider
pub mod decider_eth;
pub mod decider_eth_circuit;

use super::{
    circuits::{cyclefold::CycleFoldCircuit, CF2},
    traits::{CommittedInstanceOps, Inputize, WitnessOps},
};

/// Configuration for Nova's CycleFold circuit
pub struct NovaCycleFoldConfig<C: Curve> {
    r: Vec<bool>,
    points: Vec<C>,
}

impl<C: Curve> Default for NovaCycleFoldConfig<C> {
    fn default() -> Self {
        Self {
            r: vec![false; NOVA_N_BITS_RO],
            points: vec![C::zero(); 2],
        }
    }
}

impl<C: Curve> CycleFoldConfig<C> for NovaCycleFoldConfig<C> {
    const RANDOMNESS_BIT_LENGTH: usize = NOVA_N_BITS_RO;
    // Number of points to be folded in the CycleFold circuit, in Nova's case, this is a fixed
    // amount:
    // 2 points to be folded.
    const N_INPUT_POINTS: usize = 2;
    const N_UNIQUE_RANDOMNESSES: usize = 1;

    fn alloc_points(&self, cs: ConstraintSystemRef<CF2<C>>) -> Result<Vec<C::Var>, SynthesisError> {
        let points = Vec::new_witness(cs.clone(), || Ok(self.points.clone()))?;
        for point in &points {
            Self::mark_point_as_public(point)?;
        }
        Ok(points)
    }

    fn alloc_randomnesses(
        &self,
        cs: ConstraintSystemRef<CF2<C>>,
    ) -> Result<Vec<Vec<Boolean<CF2<C>>>>, SynthesisError> {
        let one = &CF1::<C>::one().into_bigint().to_bits_le()[..NOVA_N_BITS_RO];
        let one_var = Vec::new_constant(cs.clone(), one)?;
        let r_var = Vec::new_witness(cs.clone(), || Ok(self.r.clone()))?;
        Self::mark_randomness_as_public(&r_var)?;
        Ok(vec![one_var, r_var])
    }
}

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommittedInstance<C: Curve> {
    pub u: C::ScalarField,
    pub x: Vec<C::ScalarField>,
    pub cmW: C,
    pub cmV: Option<C>,
    pub cmE: C,
}

impl<C: Curve> Dummy<(usize, bool)> for CommittedInstance<C> {
    fn dummy((io_len, has_queries): (usize, bool)) -> Self {
        Self {
            u: CF1::<C>::zero(),
            x: vec![CF1::<C>::zero(); io_len],
            cmW: C::zero(),
            cmV: if has_queries { Some(C::zero()) } else { None },
            cmE: C::zero(),
        }
    }
}

impl<C: Curve> Dummy<&R1CS<CF1<C>>> for CommittedInstance<C> {
    fn dummy(r1cs: &R1CS<CF1<C>>) -> Self {
        Self::dummy((r1cs.l, r1cs.n_queries > 0 && r1cs.n_multiplicities > 0))
    }
}

impl<C: Curve> Absorb for CommittedInstance<C> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        C::ScalarField::batch_to_sponge_bytes(&self.to_sponge_field_elements_as_vec(), dest);
    }

    fn to_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        self.u.to_sponge_field_elements(dest);
        self.x.to_sponge_field_elements(dest);
        self.cmW.to_native_sponge_field_elements(dest);
        if let Some(cmV) = &self.cmV {
            cmV.to_native_sponge_field_elements(dest);
        }
        self.cmE.to_native_sponge_field_elements(dest);
    }
}

impl<C: Curve> CommittedInstanceOps<C> for CommittedInstance<C> {
    type Var = CommittedInstanceVar<C>;

    fn get_commitments(&self) -> Vec<C> {
        if let Some(cmV) = &self.cmV {
            vec![self.cmW, *cmV, self.cmE]
        } else {
            vec![self.cmW, self.cmE]
        }
    }

    fn is_incoming(&self) -> bool {
        self.cmE == C::zero() && self.u == One::one()
    }
}

impl<C: Curve> Inputize<CF1<C>> for CommittedInstance<C> {
    /// Returns the internal representation in the same order as how the value
    /// is allocated in `CommittedInstanceVar::new_input`.
    fn inputize(&self) -> Vec<CF1<C>> {
        [
            &[self.u][..],
            &self.x,
            &self.cmW.inputize_nonnative(),
            &if let Some(cmV) = &self.cmV {
                cmV.inputize_nonnative()
            } else {
                vec![]
            },
            &self.cmE.inputize_nonnative(),
        ]
        .concat()
    }
}

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Witness<C: Curve> {
    pub E: Vec<C::ScalarField>,
    pub rE: C::ScalarField,
    pub W: Vec<C::ScalarField>,
    pub rW: C::ScalarField,
    pub V: Vec<C::ScalarField>,
    pub rV: Option<C::ScalarField>,
}

impl<C: Curve> Witness<C> {
    pub fn new<const H: bool>(
        w1: Vec<C::ScalarField>,
        e_len: usize,
        mut rng: impl RngCore,
    ) -> Self {
        let (rW, rE) = if H {
            (
                C::ScalarField::rand(&mut rng),
                C::ScalarField::rand(&mut rng),
            )
        } else {
            (Zero::zero(), Zero::zero())
        };

        Self {
            E: vec![C::ScalarField::zero(); e_len],
            rE,
            W: w1,
            rW,
            V: vec![],
            rV: None,
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
            cmV: None,
            x,
        })
    }
}

impl<C: Curve> Dummy<&R1CS<CF1<C>>> for Witness<C> {
    fn dummy(r1cs: &R1CS<CF1<C>>) -> Self {
        Self {
            E: vec![C::ScalarField::zero(); r1cs.A.n_rows],
            rE: C::ScalarField::zero(),
            W: vec![
                C::ScalarField::zero();
                r1cs.A.n_cols - 1 - r1cs.l - r1cs.n_queries - r1cs.n_multiplicities
            ],
            rW: C::ScalarField::zero(),
            V: vec![C::ScalarField::zero(); r1cs.n_queries + r1cs.n_multiplicities],
            rV: if r1cs.n_queries + r1cs.n_multiplicities > 0 {
                Some(C::ScalarField::zero())
            } else {
                None
            },
        }
    }
}

impl<C: Curve> WitnessOps<C::ScalarField> for Witness<C> {
    type Var = WitnessVar<C>;

    fn get_openings(&self) -> Vec<(&[C::ScalarField], C::ScalarField)> {
        if let Some(rV) = self.rV {
            vec![(&self.W, self.rW), (&self.V, rV), (&self.E, self.rE)]
        } else {
            vec![(&self.W, self.rW), (&self.E, self.rE)]
        }
    }
}

#[derive(Debug, Clone)]
pub struct PreprocessorParam<C1, C2, FC, CS1, CS2, const H: bool = false>
where
    C1: Curve,
    C2: Curve,
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
    C1: Curve,
    C2: Curve,
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
    C1: Curve,
    C2: Curve,
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
    C1: Curve,
    C2: Curve,
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
    C1: Curve,
    C2: Curve,
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
    C1: Curve,
    C2: Curve,
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
    C1: Curve,
    C2: Curve,
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
    C1: Curve,
    C2: Curve,
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
    C1: Curve,
    C2: Curve,
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

impl<C1, C2, CS1, CS2, const H: bool> VerifierParams<C1, C2, CS1, CS2, H>
where
    C1: Curve,
    C2: Curve,
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

#[derive(PartialEq, Eq, Debug, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct IVCProof<C1, C2>
where
    C1: Curve,
    C2: Curve,
{
    // current step of the IVC
    pub i: C1::ScalarField,
    // initial state
    pub z_0: Vec<C1::ScalarField>,
    // current state
    pub z_i: Vec<C1::ScalarField>,
    // running instance
    pub W_i: Witness<C1>,
    pub U_i: CommittedInstance<C1>,
    // incoming instance
    pub w_i: Witness<C1>,
    pub u_i: CommittedInstance<C1>,
    // CycleFold instances
    pub cf_W_i: CycleFoldWitness<C2>,
    pub cf_U_i: CycleFoldCommittedInstance<C2>,
}

/// Implements Nova+CycleFold's IVC, described in [Nova](https://eprint.iacr.org/2021/370.pdf) and
/// [CycleFold](https://eprint.iacr.org/2023/1192.pdf), following the FoldingScheme trait
/// The `H` const generic specifies whether the homorphic commitment scheme is blinding
#[derive(Clone, Debug)]
pub struct Nova<C1, C2, FC, CS1, CS2, const H: bool = false>
where
    C1: Curve,
    C2: Curve,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
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

impl<C1, C2, FC, CS1, CS2, const H: bool> FoldingScheme<C1, C2, FC>
    for Nova<C1, C2, FC, CS1, CS2, H>
where
    C1: Curve,
    C2: Curve,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
    C1: Curve<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
{
    type PreprocessorParam = PreprocessorParam<C1, C2, FC, CS1, CS2, H>;
    type ProverParam = ProverParams<C1, C2, CS1, CS2, H>;
    type VerifierParam = VerifierParams<C1, C2, CS1, CS2, H>;
    type RunningInstance = (CommittedInstance<C1>, Witness<C1>);
    type IncomingInstance = (CommittedInstance<C1>, Witness<C1>);
    type MultiCommittedInstanceWithWitness = ();
    type CFInstance = (CycleFoldCommittedInstance<C2>, CycleFoldWitness<C2>);
    type IVCProof = IVCProof<C1, C2>;

    fn pp_deserialize_with_mode<R: std::io::prelude::Read>(
        reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
        _fc_params: FC::Params, // FCircuit params
    ) -> Result<Self::ProverParam, Error> {
        Ok(Self::ProverParam::deserialize_with_mode(
            reader, compress, validate,
        )?)
    }
    fn vp_deserialize_with_mode<R: std::io::prelude::Read>(
        mut reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
        fc_params: FC::Params,
    ) -> Result<Self::VerifierParam, Error> {
        let poseidon_config = poseidon_canonical_config::<C1::ScalarField>();

        // generate the r1cs & cf_r1cs needed for the VerifierParams. In this way we avoid needing
        // to serialize them, saving significant space in the VerifierParams serialized size.

        // main circuit R1CS:
        let f_circuit = FC::new(fc_params)?;
        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        cs.set_mode(SynthesisMode::Setup);
        let augmented_F_circuit =
            AugmentedFCircuit::<C1, C2, FC>::empty(&poseidon_config, f_circuit.clone());
        augmented_F_circuit.generate_constraints(cs.clone())?;
        cs.finalize_lookup()?;
        let mut cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        LogUp::generate_verification_constraints(&mut cs, Zero::zero())?;
        cs.finalize();
        let r1cs = extract_r1cs::<C1::ScalarField>(&cs)?;

        // CycleFold circuit R1CS
        let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();
        cs2.set_mode(SynthesisMode::Setup);
        let cf_circuit = CycleFoldCircuit::<_, NovaCycleFoldConfig<C1>>::default();
        cf_circuit.generate_constraints(cs2.clone())?;
        cs2.finalize();
        let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let cf_r1cs = extract_r1cs::<C1::BaseField>(&cs2)?;

        let cs_vp = CS1::VerifierParams::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_cs_vp = CS2::VerifierParams::deserialize_with_mode(&mut reader, compress, validate)?;

        Ok(Self::VerifierParam {
            poseidon_config,
            r1cs,
            cf_r1cs,
            cs_vp,
            cf_cs_vp,
        })
    }

    fn preprocess(
        mut rng: impl RngCore,
        prep_param: &Self::PreprocessorParam,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        let (r1cs, cf_r1cs) =
            get_r1cs::<C1, C2, FC>(&prep_param.poseidon_config, prep_param.F.clone())?;

        // if cs params exist, use them, if not, generate new ones
        let (cs_pp, cs_vp) = match (&prep_param.cs_pp, &prep_param.cs_vp) {
            (Some(cs_pp), Some(cs_vp)) => (cs_pp.clone(), cs_vp.clone()),
            _ => CS1::setup(&mut rng, r1cs.A.n_rows)?,
        };
        let (cf_cs_pp, cf_cs_vp) = match (&prep_param.cf_cs_pp, &prep_param.cf_cs_vp) {
            (Some(cf_cs_pp), Some(cf_cs_vp)) => (cf_cs_pp.clone(), cf_cs_vp.clone()),
            _ => CS2::setup(&mut rng, cf_r1cs.A.n_rows)?,
        };

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
        cs.set_mode(SynthesisMode::Setup);
        let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();
        cs2.set_mode(SynthesisMode::Setup);

        let augmented_F_circuit =
            AugmentedFCircuit::<C1, C2, FC>::empty(&pp.poseidon_config, F.clone());
        let cf_circuit = CycleFoldCircuit::<_, NovaCycleFoldConfig<C1>>::default();

        augmented_F_circuit.generate_constraints(cs.clone())?;
        cs.finalize_lookup()?;
        let mut cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        LogUp::generate_verification_constraints(&mut cs, Zero::zero())?;
        cs.finalize();
        let r1cs = extract_r1cs::<C1::ScalarField>(&cs)?;

        cf_circuit.generate_constraints(cs2.clone())?;
        cs2.finalize();
        let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let cf_r1cs = extract_r1cs::<C1::BaseField>(&cs2)?;

        // compute the public params hash
        let pp_hash = vp.pp_hash()?;

        // setup the dummy instances
        let (W_dummy, U_dummy) = r1cs.dummy_witness_instance();
        let (w_dummy, u_dummy) = r1cs.dummy_witness_instance();
        let (cf_W_dummy, cf_U_dummy) = cf_r1cs.dummy_witness_instance();

        // W_dummy=W_0 is a 'dummy witness', all zeroes, but with the size corresponding to the
        // R1CS that we're working with.
        Ok(Self {
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
        external_inputs: FC::ExternalInputs,
        // Nova does not support multi-instances folding (by design)
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
        let sponge = PoseidonSponge::<C1::ScalarField>::new_with_pp_hash(
            &self.poseidon_config,
            self.pp_hash,
        );
        // `transcript` is for challenge generation.
        let mut transcript = sponge.clone();

        let mut augmented_F_circuit: AugmentedFCircuit<C1, C2, FC>;

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

        let i_bn: BigUint = self.i.into();
        let i_usize: usize = i_bn.try_into().map_err(|_| Error::MaxStep)?;

        // fold Nova instances
        let (W_i1, U_i1, cmT, r_bits): (Witness<C1>, CommittedInstance<C1>, C1, Vec<bool>) =
            NIFS::<C1, CS1, PoseidonSponge<C1::ScalarField>, H>::prove(
                &self.cs_pp,
                &self.r1cs,
                &mut transcript,
                &self.W_i,
                &self.U_i,
                &self.w_i,
                &self.u_i,
            )?;

        if self.i == C1::ScalarField::zero() {
            // base case
            augmented_F_circuit = AugmentedFCircuit::empty(&self.poseidon_config, self.F.clone());
            augmented_F_circuit.pp_hash = self.pp_hash;
            augmented_F_circuit.z_0.clone_from(&self.z_0);
            augmented_F_circuit.z_i.clone_from(&self.z_i);
            augmented_F_circuit
                .external_inputs
                .clone_from(&external_inputs);
            augmented_F_circuit.u_i_cmV = self.u_i.cmV;
            augmented_F_circuit.U_i = Some(self.U_i.clone());
            augmented_F_circuit.U_i1_cmV = self.u_i.cmV;
            augmented_F_circuit.cf3_u_i_cmW = if self.u_i.cmV.is_some() {
                Some(Zero::zero())
            } else {
                None
            };
            augmented_F_circuit.cf3_cmT = if self.u_i.cmV.is_some() {
                Some(Zero::zero())
            } else {
                None
            };

            #[cfg(test)]
            {
                let r_Fr = C1::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits))
                    .ok_or(Error::OutOfBounds)?;
                let expected =
                    NIFS::<C1, CS1, PoseidonSponge<C1::ScalarField>, H>::fold_committed_instances(
                        r_Fr, &self.U_i, &self.u_i, &cmT,
                    );
                assert_eq!(U_i1, expected);
            }
        } else {
            // CycleFold part:
            let (cfE_w_i, cfE_u_i) = NovaCycleFoldConfig {
                r: r_bits.clone(),
                points: vec![self.U_i.cmE, cmT],
            }
            .build_circuit()
            .generate_incoming_instance_witness::<_, CS2, H>(&self.cf_cs_pp, &mut rng)?;
            let (cfW_w_i, cfW_u_i) = NovaCycleFoldConfig {
                r: r_bits.clone(),
                points: vec![self.U_i.cmW, self.u_i.cmW],
            }
            .build_circuit()
            .generate_incoming_instance_witness::<_, CS2, H>(&self.cf_cs_pp, &mut rng)?;
            let (cfV_w_i, cfV_u_i) = match (self.U_i.cmV, self.u_i.cmV) {
                (Some(cmV), Some(u_cmV)) => {
                    let (cfV_w_i, cfV_u_i) = NovaCycleFoldConfig {
                        r: r_bits.clone(),
                        points: vec![cmV, u_cmV],
                    }
                    .build_circuit()
                    .generate_incoming_instance_witness::<_, CS2, H>(&self.cf_cs_pp, &mut rng)?;
                    (Some(cfV_w_i), Some(cfV_u_i))
                }
                _ => (None, None),
            };

            let (cf_W_i1, cf_U_i1, cf_cmTs) = CycleFoldAugmentationGadget::fold_native::<_, CS2, H>(
                &mut transcript,
                &self.cf_r1cs,
                &self.cf_cs_pp,
                self.cf_W_i.clone(),
                self.cf_U_i.clone(),
                if let Some(cfV_w_i) = cfV_w_i {
                    vec![cfE_w_i, cfW_w_i, cfV_w_i]
                } else {
                    vec![cfE_w_i, cfW_w_i]
                },
                if let Some(cfV_u_i) = cfV_u_i.clone() {
                    vec![cfE_u_i.clone(), cfW_u_i.clone(), cfV_u_i]
                } else {
                    vec![cfE_u_i.clone(), cfW_u_i.clone()]
                },
            )?;

            augmented_F_circuit = AugmentedFCircuit::<C1, C2, FC> {
                poseidon_config: self.poseidon_config.clone(),
                pp_hash: self.pp_hash,
                i: self.i,
                i_usize,
                z_0: self.z_0.clone(),
                z_i: self.z_i.clone(),
                external_inputs: external_inputs.clone(),
                u_i_cmW: self.u_i.cmW,
                u_i_cmV: self.u_i.cmV,
                U_i: Some(self.U_i.clone()),
                U_i1_cmE: U_i1.cmE,
                U_i1_cmW: U_i1.cmW,
                U_i1_cmV: U_i1.cmV,
                cmT,
                F: self.F.clone(),
                // cyclefold values
                cf1_u_i_cmW: cfE_u_i.cmW,
                cf2_u_i_cmW: cfW_u_i.cmW,
                cf3_u_i_cmW: cfV_u_i.map(|cfV_u_i| cfV_u_i.cmW),
                cf_U_i: self.cf_U_i.clone(),
                cf1_cmT: cf_cmTs[0],
                cf2_cmT: cf_cmTs[1],
                cf3_cmT: cf_cmTs.get(2).copied(),
            };

            self.cf_W_i = cf_W_i1;
            self.cf_U_i = cf_U_i1;
        }

        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();

        let z_i1 = augmented_F_circuit
            .compute_next_state(cs.clone())?
            .value()?;

        cs.finalize_lookup()?;
        let mut cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;

        let w1_len = cs.num_witness_variables;
        let (cmW, rW) = CS1::commit_with_rng(&self.cs_pp, &cs.witness_assignment, &mut rng)?;
        LogUp::generate_verification_constraints(&mut cs, LogUp::challenge(&sponge, &cmW))?;

        #[cfg(test)]
        assert!(cs.is_satisfied()?);

        let (cmV, rV) = if cs.num_witness_variables > w1_len {
            let (cmV, rV) =
                CS1::commit_with_rng(&self.cs_pp, &cs.witness_assignment[w1_len..], &mut rng)?;
            (Some(cmV), Some(rV))
        } else {
            (None, None)
        };

        let (w_i1, x_i1) = extract_w_x::<C1::ScalarField>(&cs);

        #[cfg(test)]
        if cs.num_witness_variables > w1_len {
            if x_i1.len() != 3 {
                return Err(Error::NotExpectedLength(x_i1.len(), 3));
            }
        } else {
            if x_i1.len() != 2 {
                return Err(Error::NotExpectedLength(x_i1.len(), 2));
            }
        }

        // set values for next iteration
        self.i += C1::ScalarField::one();
        self.z_i = z_i1;
        self.w_i.W = w_i1[..w1_len].to_vec();
        self.w_i.rW = rW;
        self.w_i.V = w_i1[w1_len..].to_vec();
        self.w_i.rV = rV;
        self.w_i.rE = if H {
            C1::ScalarField::rand(&mut rng)
        } else {
            Zero::zero()
        };
        self.u_i = CommittedInstance {
            u: One::one(),
            x: x_i1,
            cmW,
            cmV,
            cmE: Zero::zero(),
        };
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

    fn ivc_proof(&self) -> Self::IVCProof {
        Self::IVCProof {
            i: self.i,
            z_0: self.z_0.clone(),
            z_i: self.z_i.clone(),
            W_i: self.W_i.clone(),
            U_i: self.U_i.clone(),
            w_i: self.w_i.clone(),
            u_i: self.u_i.clone(),
            cf_W_i: self.cf_W_i.clone(),
            cf_U_i: self.cf_U_i.clone(),
        }
    }

    fn from_ivc_proof(
        ivc_proof: IVCProof<C1, C2>,
        fcircuit_params: FC::Params,
        params: (Self::ProverParam, Self::VerifierParam),
    ) -> Result<Self, Error> {
        let IVCProof {
            i,
            z_0,
            z_i,
            W_i,
            U_i,
            w_i,
            u_i,
            cf_W_i,
            cf_U_i,
        } = ivc_proof;
        let (pp, vp) = params;

        let f_circuit = FC::new(fcircuit_params)?;
        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();
        let augmented_F_circuit =
            AugmentedFCircuit::<C1, C2, FC>::empty(&pp.poseidon_config, f_circuit.clone());
        let cf_circuit = CycleFoldCircuit::<_, NovaCycleFoldConfig<C1>>::default();

        augmented_F_circuit.generate_constraints(cs.clone())?;
        cs.finalize();
        let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let r1cs = extract_r1cs::<C1::ScalarField>(&cs)?;

        cf_circuit.generate_constraints(cs2.clone())?;
        cs2.finalize();
        let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let cf_r1cs = extract_r1cs::<C1::BaseField>(&cs2)?;

        Ok(Self {
            r1cs,
            cf_r1cs,
            poseidon_config: pp.poseidon_config,
            cs_pp: pp.cs_pp,
            cf_cs_pp: pp.cf_cs_pp,
            F: f_circuit,
            pp_hash: vp.pp_hash()?,
            i,
            z_0,
            z_i,
            w_i,
            u_i,
            W_i,
            U_i,
            cf_W_i,
            cf_U_i,
        })
    }

    /// Implements IVC.V of Nov.clone()a+CycleFold. Notice that this method does not include the
    /// commitments verification, which is done in the Decider.
    fn verify(vp: Self::VerifierParam, ivc_proof: Self::IVCProof) -> Result<(), Error> {
        let Self::IVCProof {
            i: num_steps,
            z_0,
            z_i,
            W_i,
            U_i,
            w_i,
            u_i,
            cf_W_i,
            cf_U_i,
        } = ivc_proof;

        let sponge =
            PoseidonSponge::<C1::ScalarField>::new_with_pp_hash(&vp.poseidon_config, vp.pp_hash()?);

        if num_steps == C1::ScalarField::zero() {
            if z_0 != z_i {
                return Err(Error::IVCVerificationFail);
            }
            return Ok(());
        }

        if u_i.x.len() != U_i.x.len() {
            return Err(Error::IVCVerificationFail);
        }

        let expected_x = match (U_i.cmV, u_i.cmV) {
            (Some(_), Some(_)) => {
                vec![
                    // u_i.X[0] = H(i, z_0, z_i, U_i)
                    U_i.hash(&sponge, num_steps, &z_0, &z_i),
                    // u_i.X[1] = H(cf_U_i)
                    cf_U_i.hash_cyclefold(&sponge),
                    LogUp::challenge(&sponge, &u_i.cmW),
                ]
            }
            (None, None) => {
                vec![
                    // u_i.X[0] = H(i, z_0, z_i, U_i)
                    U_i.hash(&sponge, num_steps, &z_0, &z_i),
                    // u_i.X[1] = H(cf_U_i)
                    cf_U_i.hash_cyclefold(&sponge),
                ]
            }
            _ => return Err(Error::IVCVerificationFail),
        };

        if expected_x != u_i.x {
            return Err(Error::IVCVerificationFail);
        }

        // check R1CS satisfiability, which is equivalent to checking if `u_i`
        // is an incoming instance and if `w_i` and `u_i` satisfy RelaxedR1CS
        u_i.check_incoming().unwrap();
        vp.r1cs.check_relation(&w_i, &u_i).unwrap();
        // check RelaxedR1CS satisfiability
        vp.r1cs.check_relation(&W_i, &U_i).unwrap();

        // check CycleFold RelaxedR1CS satisfiability
        vp.cf_r1cs.check_relation(&cf_W_i, &cf_U_i).unwrap();

        Ok(())
    }
}

/// helper method to get the r1cs from the ConstraintSynthesizer
pub fn get_r1cs_from_cs<F: PrimeField>(
    circuit: impl ConstraintSynthesizer<F>,
) -> Result<R1CS<F>, Error> {
    let cs = ConstraintSystem::<F>::new_ref();
    cs.set_mode(SynthesisMode::Setup);
    circuit.generate_constraints(cs.clone())?;
    cs.finalize_lookup()?;
    let mut cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
    LogUp::generate_verification_constraints(&mut cs, Zero::zero())?;
    cs.finalize();
    let r1cs = extract_r1cs::<F>(&cs)?;
    Ok(r1cs)
}

/// helper method to get the R1CS for both the AugmentedFCircuit and the CycleFold circuit
#[allow(clippy::type_complexity)]
pub fn get_r1cs<C1, C2, FC>(
    poseidon_config: &PoseidonConfig<C1::ScalarField>,
    F_circuit: FC,
) -> Result<(R1CS<C1::ScalarField>, R1CS<C2::ScalarField>), Error>
where
    C1: Curve,
    C2: Curve,
    FC: FCircuit<C1::ScalarField>,
    C1: Curve<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
{
    let augmented_F_circuit = AugmentedFCircuit::<C1, C2, FC>::empty(poseidon_config, F_circuit);
    let cf_circuit = CycleFoldCircuit::<_, NovaCycleFoldConfig<C1>>::default();
    let r1cs = get_r1cs_from_cs::<C1::ScalarField>(augmented_F_circuit)?;
    let cf_r1cs = get_r1cs_from_cs::<C2::ScalarField>(cf_circuit)?;
    Ok((r1cs, cf_r1cs))
}

/// helper method to get the pedersen params length for both the AugmentedFCircuit and the
/// CycleFold circuit
pub fn get_cs_params_len<C1, C2, FC>(
    poseidon_config: &PoseidonConfig<C1::ScalarField>,
    F_circuit: FC,
) -> Result<(usize, usize), Error>
where
    C1: Curve,
    C2: Curve,
    FC: FCircuit<C1::ScalarField>,
    C1: Curve<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
{
    let (r1cs, cf_r1cs) = get_r1cs::<C1, C2, FC>(poseidon_config, F_circuit)?;
    Ok((r1cs.A.n_rows, cf_r1cs.A.n_rows))
}

#[cfg(test)]
pub mod tests {
    use crate::commitment::kzg::KZG;
    use ark_bn254::{Bn254, Fr, G1Projective as Projective};
    use ark_grumpkin::Projective as Projective2;
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar};
    use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
    use ark_std::marker::PhantomData;

    use super::*;
    use crate::commitment::pedersen::Pedersen;
    use crate::frontend::alloc::LookupConstraintSystem;
    use crate::transcript::poseidon::poseidon_canonical_config;

    #[cfg(test)]
    #[derive(Clone, Copy, Debug)]
    pub struct Circuit<F: PrimeField> {
        _f: PhantomData<F>,
    }

    #[cfg(test)]
    impl<F: PrimeField> FCircuit<F> for Circuit<F> {
        type Params = ();
        type ExternalInputs = ();
        type ExternalInputsVar = ();

        fn new(_params: Self::Params) -> Result<Self, Error> {
            Ok(Self { _f: PhantomData })
        }
        fn state_len(&self) -> usize {
            1
        }
        fn generate_step_constraints(
            &self,
            cs: ConstraintSystemRef<F>,
            i: usize,
            z_i: Vec<FpVar<F>>,
            _external_inputs: Self::ExternalInputsVar,
        ) -> Result<Vec<FpVar<F>>, SynthesisError> {
            cs.init_lookup((0..256).map(F::from).collect())?;
            let five = FpVar::<F>::new_constant(cs.clone(), F::from(5u32))?;
            let z_i = z_i[0].clone();
            let t = cs.new_query_fp(|| Ok(F::from(i as u64)))?;

            Ok(vec![&z_i * &z_i * &z_i + &t + &five])
        }
    }

    /// This test tests the Nova+CycleFold IVC, and by consequence it is also testing the
    /// AugmentedFCircuit
    #[test]
    fn test_ivc() -> Result<(), Error> {
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = Circuit::<Fr>::new(())?;

        // run the test using Pedersen commitments on both sides of the curve cycle
        let _ = test_ivc_opt::<_, Pedersen<Projective>, Pedersen<Projective2>, false>(
            poseidon_config.clone(),
            F_circuit,
            3,
        )?;

        let _ = test_ivc_opt::<_, Pedersen<Projective, true>, Pedersen<Projective2, true>, true>(
            poseidon_config.clone(),
            F_circuit,
            3,
        )?;

        // run the test using KZG for the commitments on the main curve, and Pedersen for the
        // commitments on the secondary curve
        let _ = test_ivc_opt::<_, KZG<Bn254>, Pedersen<Projective2>, false>(
            poseidon_config,
            F_circuit,
            3,
        )?;
        Ok(())
    }

    // test_ivc allowing to choose the CommitmentSchemes
    #[allow(clippy::type_complexity)]
    pub(crate) fn test_ivc_opt<
        FC: FCircuit<Fr, ExternalInputs = (), Params = ()>,
        CS1: CommitmentScheme<Projective, H>,
        CS2: CommitmentScheme<Projective2, H>,
        const H: bool,
    >(
        poseidon_config: PoseidonConfig<Fr>,
        F_circuit: FC,
        num_steps: usize,
    ) -> Result<(Vec<Fr>, Nova<Projective, Projective2, FC, CS1, CS2, H>), Error> {
        let mut rng = ark_std::test_rng();

        let prep_param = PreprocessorParam::<Projective, Projective2, FC, CS1, CS2, H> {
            poseidon_config,
            F: F_circuit.clone(),
            cs_pp: None,
            cs_vp: None,
            cf_cs_pp: None,
            cf_cs_vp: None,
        };
        let nova_params =
            Nova::<Projective, Projective2, FC, CS1, CS2, H>::preprocess(&mut rng, &prep_param)?;

        let z_0 = vec![Fr::from(3_u32)];
        let mut nova = Nova::<Projective, Projective2, FC, CS1, CS2, H>::init(
            &nova_params,
            F_circuit,
            z_0.clone(),
        )?;

        for _ in 0..num_steps {
            nova.prove_step(&mut rng, (), None)?;
        }
        assert_eq!(Fr::from(num_steps as u32), nova.i);
        Nova::<Projective, Projective2, FC, CS1, CS2, H>::verify(
            nova_params.1.clone(), // Nova's verifier params
            nova.ivc_proof(),
        )?;

        // serialize the Nova Prover & Verifier params. These params are the trusted setup of the commitment schemes used
        let mut nova_pp_serialized = vec![];
        nova_params
            .0
            .serialize_compressed(&mut nova_pp_serialized)?;
        let mut nova_vp_serialized = vec![];
        nova_params
            .1
            .serialize_compressed(&mut nova_vp_serialized)?;

        // deserialize the Nova params
        let _nova_pp_deserialized =
            ProverParams::<Projective, Projective2, CS1, CS2, H>::deserialize_compressed(
                &mut nova_pp_serialized.as_slice(),
            )?;
        let nova_vp_deserialized =
            Nova::<Projective, Projective2, FC, CS1, CS2, H>::vp_deserialize_with_mode(
                &mut nova_vp_serialized.as_slice(),
                ark_serialize::Compress::Yes,
                ark_serialize::Validate::Yes,
                (), // fcircuit_params
            )?;

        let ivc_proof = nova.ivc_proof();

        // serialize IVCProof
        let mut ivc_proof_serialized = vec![];
        assert!(ivc_proof
            .serialize_compressed(&mut ivc_proof_serialized)
            .is_ok());
        // deserialize IVCProof
        let ivc_proof_deserialized =
            <Nova<Projective, Projective2, FC, CS1, CS2, H> as FoldingScheme<
                Projective,
                Projective2,
                FC,
            >>::IVCProof::deserialize_compressed(ivc_proof_serialized.as_slice())?;

        // verify the deserialized IVCProof with the deserialized VerifierParams
        Nova::<Projective, Projective2, FC, CS1, CS2, H>::verify(
            nova_vp_deserialized, // Nova's verifier params
            ivc_proof_deserialized,
        )?;
        Ok((z_0, nova))
    }
}
