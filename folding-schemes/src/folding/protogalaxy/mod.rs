/// Implements the scheme described in [ProtoGalaxy](https://eprint.iacr.org/2023/1106.pdf)
use ark_crypto_primitives::sponge::poseidon::{PoseidonConfig, PoseidonSponge};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    prelude::Boolean,
    R1CSVar,
};
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, Namespace, SynthesisError,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Valid};
use ark_std::{borrow::Borrow, cmp::max, fmt::Debug, log2, rand::RngCore, One, Zero};
use constants::{INCOMING, RUNNING};
use num_bigint::BigUint;

use crate::{
    arith::{
        r1cs::{extract_r1cs, extract_w_x, R1CS},
        Arith, ArithRelation,
    },
    commitment::CommitmentScheme,
    folding::circuits::{
        cyclefold::{
            CycleFoldAugmentationGadget, CycleFoldCommittedInstance, CycleFoldConfig,
            CycleFoldWitness,
        },
        nonnative::affine::NonNativeAffineVar,
        CF1,
    },
    frontend::{utils::DummyCircuit, FCircuit},
    transcript::{poseidon::poseidon_canonical_config, Transcript},
    utils::pp_hash,
    Curve, Error, FoldingScheme,
};

pub mod circuits;
pub mod constants;
pub mod decider_eth;
pub mod decider_eth_circuit;
pub mod folding;
pub mod traits;
pub(crate) mod utils;

use circuits::AugmentedFCircuit;
use folding::Folding;

use super::{
    circuits::{cyclefold::CycleFoldCircuit, CF2},
    traits::{
        CommittedInstanceOps, CommittedInstanceVarOps, Dummy, Inputize, WitnessOps, WitnessVarOps,
    },
};

/// Configuration for ProtoGalaxy's CycleFold circuit
pub struct ProtoGalaxyCycleFoldConfig<C: Curve> {
    rs: Vec<CF1<C>>,
    points: Vec<C>,
}

impl<C: Curve> Default for ProtoGalaxyCycleFoldConfig<C> {
    fn default() -> Self {
        Self {
            rs: vec![CF1::<C>::one(); 2],
            points: vec![C::zero(); 2],
        }
    }
}

impl<C: Curve> CycleFoldConfig<C> for ProtoGalaxyCycleFoldConfig<C> {
    const RANDOMNESS_BIT_LENGTH: usize = C::ScalarField::MODULUS_BIT_SIZE as usize;
    const N_UNIQUE_RANDOMNESSES: usize = 2;
    const N_INPUT_POINTS: usize = 2;

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
        let rs = vec![self.rs[0]]
            .into_iter()
            .chain(self.rs.windows(2).map(|r| r[1] / r[0]))
            .map(|r| {
                let mut bits = r.into_bigint().to_bits_le();
                bits.resize(CF1::<C>::MODULUS_BIT_SIZE as usize, false);
                Vec::new_witness(cs.clone(), || Ok(bits))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Self::mark_randomness_as_public(&rs.concat())?;
        Ok(rs)
    }
}

/// The committed instance of ProtoGalaxy.
///
/// We use `TYPE` to distinguish between incoming and running instances, as
/// they have slightly different structures (e.g., length of `betas`) and
/// behaviors (e.g., in satisfiability checks).
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommittedInstance<C: Curve, const TYPE: bool> {
    phi: C,
    betas: Vec<C::ScalarField>,
    e: C::ScalarField,
    x: Vec<C::ScalarField>,
}

impl<C: Curve, const TYPE: bool> Dummy<(usize, usize)> for CommittedInstance<C, TYPE> {
    fn dummy((io_len, t): (usize, usize)) -> Self {
        if TYPE == INCOMING {
            assert_eq!(t, 0);
        }
        Self {
            phi: C::zero(),
            betas: vec![Zero::zero(); t],
            e: Zero::zero(),
            x: vec![Zero::zero(); io_len],
        }
    }
}

impl<C: Curve, const TYPE: bool> Dummy<&R1CS<CF1<C>>> for CommittedInstance<C, TYPE> {
    fn dummy(r1cs: &R1CS<CF1<C>>) -> Self {
        let t = if TYPE == RUNNING {
            log2(r1cs.n_constraints()) as usize
        } else {
            0
        };
        Self::dummy((r1cs.n_public_inputs(), t))
    }
}

impl<C: Curve, const TYPE: bool> CommittedInstanceOps<C> for CommittedInstance<C, TYPE> {
    type Var = CommittedInstanceVar<C, TYPE>;

    fn get_commitments(&self) -> Vec<C> {
        vec![self.phi]
    }

    fn is_incoming(&self) -> bool {
        TYPE == INCOMING
    }
}

impl<C: Curve, const TYPE: bool> Inputize<CF1<C>> for CommittedInstance<C, TYPE> {
    /// Returns the internal representation in the same order as how the value
    /// is allocated in `CommittedInstanceVar::new_input`.
    fn inputize(&self) -> Vec<CF1<C>> {
        [
            &self.phi.inputize_nonnative(),
            &self.betas,
            &[self.e][..],
            &self.x,
        ]
        .concat()
    }
}

#[derive(Clone, Debug)]
pub struct CommittedInstanceVar<C: Curve, const TYPE: bool> {
    phi: NonNativeAffineVar<C>,
    betas: Vec<FpVar<C::ScalarField>>,
    e: FpVar<C::ScalarField>,
    x: Vec<FpVar<C::ScalarField>>,
}

impl<C: Curve, const TYPE: bool> AllocVar<CommittedInstance<C, TYPE>, C::ScalarField>
    for CommittedInstanceVar<C, TYPE>
{
    fn new_variable<T: Borrow<CommittedInstance<C, TYPE>>>(
        cs: impl Into<Namespace<C::ScalarField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|u| {
            let cs = cs.into();

            let u = u.borrow();

            Ok(Self {
                phi: NonNativeAffineVar::new_variable(cs.clone(), || Ok(u.phi), mode)?,
                betas: Vec::new_variable(cs.clone(), || Ok(u.betas.clone()), mode)?,
                e: if TYPE == RUNNING {
                    FpVar::new_variable(cs.clone(), || Ok(u.e), mode)?
                } else {
                    FpVar::zero()
                },
                x: Vec::new_variable(cs.clone(), || Ok(u.x.clone()), mode)?,
            })
        })
    }
}

impl<C: Curve, const TYPE: bool> R1CSVar<C::ScalarField> for CommittedInstanceVar<C, TYPE> {
    type Value = CommittedInstance<C, TYPE>;

    fn cs(&self) -> ConstraintSystemRef<C::ScalarField> {
        self.phi
            .cs()
            .or(self.betas.cs())
            .or(self.e.cs())
            .or(self.x.cs())
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        Ok(CommittedInstance {
            phi: self.phi.value()?,
            betas: self
                .betas
                .iter()
                .map(|v| v.value())
                .collect::<Result<_, _>>()?,
            e: self.e.value()?,
            x: self.x.iter().map(|v| v.value()).collect::<Result<_, _>>()?,
        })
    }
}

impl<C: Curve, const TYPE: bool> CommittedInstanceVarOps<C> for CommittedInstanceVar<C, TYPE> {
    type PointVar = NonNativeAffineVar<C>;

    fn get_commitments(&self) -> Vec<Self::PointVar> {
        vec![self.phi.clone()]
    }

    fn get_public_inputs(&self) -> &[FpVar<CF1<C>>] {
        &self.x
    }

    fn enforce_incoming(&self) -> Result<(), SynthesisError> {
        // We don't need to check if `self` is an incoming instance in-circuit,
        // because incoming instances and running instances already have
        // different types of `e` (constant vs witness) when we allocate them
        // in-circuit.
        (TYPE == INCOMING)
            .then_some(())
            .ok_or(SynthesisError::Unsatisfiable)
    }

    fn enforce_partial_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        self.betas.enforce_equal(&other.betas)?;
        self.e.enforce_equal(&other.e)?;
        self.x.enforce_equal(&other.x)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Witness<F: PrimeField> {
    w: Vec<F>,
    r_w: F,
}

impl<F: PrimeField> Witness<F> {
    pub fn new(w: Vec<F>) -> Self {
        // note: at the current version, we don't use the blinding factors and we set them to 0
        // always.
        // Tracking issue: https://github.com/privacy-scaling-explorations/sonobe/issues/82
        Self { w, r_w: F::zero() }
    }

    pub fn commit<CS: CommitmentScheme<C>, C: Curve<ScalarField = F>>(
        &self,
        params: &CS::ProverParams,
        x: Vec<F>,
    ) -> Result<CommittedInstance<C, false>, crate::Error> {
        let phi = CS::commit(params, &self.w, &self.r_w)?;
        Ok(CommittedInstance::<C, false> {
            phi,
            x,
            e: F::zero(),
            betas: vec![],
        })
    }
}

impl<F: PrimeField> Dummy<&R1CS<F>> for Witness<F> {
    fn dummy(r1cs: &R1CS<F>) -> Self {
        Self {
            w: vec![F::zero(); r1cs.n_witnesses()],
            r_w: F::zero(),
        }
    }
}

impl<F: PrimeField> WitnessOps<F> for Witness<F> {
    type Var = WitnessVar<F>;

    fn get_openings(&self) -> Vec<(&[F], F)> {
        vec![(&self.w, self.r_w)]
    }
}

/// In-circuit representation of the Witness associated to the CommittedInstance.
#[derive(Debug, Clone)]
pub struct WitnessVar<F: PrimeField> {
    pub W: Vec<FpVar<F>>,
    pub rW: FpVar<F>,
}

impl<F: PrimeField> AllocVar<Witness<F>, F> for WitnessVar<F> {
    fn new_variable<T: Borrow<Witness<F>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let W = Vec::new_variable(cs.clone(), || Ok(val.borrow().w.to_vec()), mode)?;
            let rW = FpVar::new_variable(cs.clone(), || Ok(val.borrow().r_w), mode)?;

            Ok(Self { W, rW })
        })
    }
}

impl<F: PrimeField> WitnessVarOps<F> for WitnessVar<F> {
    fn get_openings(&self) -> Vec<(&[FpVar<F>], FpVar<F>)> {
        vec![(&self.W, self.rW.clone())]
    }
}

#[derive(Debug, thiserror::Error, PartialEq)]
pub enum ProtoGalaxyError {
    #[error("The remainder from G(X)-F(α)*L_0(X)) / Z(X) should be zero")]
    RemainderNotZero,
    #[error("Could not divide by vanishing polynomial")]
    CouldNotDivideByVanishing,
    #[error("The number of incoming instances + 1 should be a power of two, current number of instances: {0}")]
    WrongNumInstances(usize),
    #[error("The number of incoming items should be a power of two, current number of coefficients: {0}")]
    BTreeNotFull(usize),
    #[error("The lengths of β and δ do not equal: |β| = {0}, |δ|={0}")]
    WrongLenBetas(usize, usize),
}

/// Proving parameters for ProtoGalaxy-based IVC
#[derive(Debug, Clone)]
pub struct ProverParams<C1, C2, CS1, CS2>
where
    C1: Curve,
    C2: Curve,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
{
    /// Poseidon sponge configuration
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    /// Proving parameters of the underlying commitment scheme over C1
    pub cs_params: CS1::ProverParams,
    /// Proving parameters of the underlying commitment scheme over C2
    pub cf_cs_params: CS2::ProverParams,
}
impl<C1, C2, CS1, CS2> CanonicalSerialize for ProverParams<C1, C2, CS1, CS2>
where
    C1: Curve,
    C2: Curve,
    CS1: CommitmentScheme<C1, false>,
    CS2: CommitmentScheme<C2, false>,
{
    fn serialize_with_mode<W: std::io::prelude::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.cs_params.serialize_with_mode(&mut writer, compress)?;
        self.cf_cs_params.serialize_with_mode(&mut writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        self.cs_params.serialized_size(compress) + self.cf_cs_params.serialized_size(compress)
    }
}
impl<C1, C2, CS1, CS2> Valid for ProverParams<C1, C2, CS1, CS2>
where
    C1: Curve,
    C2: Curve,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
{
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        self.poseidon_config.full_rounds.check()?;
        self.poseidon_config.partial_rounds.check()?;
        self.poseidon_config.alpha.check()?;
        self.poseidon_config.ark.check()?;
        self.poseidon_config.mds.check()?;
        self.poseidon_config.rate.check()?;
        self.poseidon_config.capacity.check()?;
        self.cs_params.check()?;
        self.cf_cs_params.check()?;
        Ok(())
    }
}
impl<C1, C2, CS1, CS2> CanonicalDeserialize for ProverParams<C1, C2, CS1, CS2>
where
    C1: Curve,
    C2: Curve,
    CS1: CommitmentScheme<C1, false>,
    CS2: CommitmentScheme<C2, false>,
{
    fn deserialize_with_mode<R: std::io::prelude::Read>(
        mut reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        let cs_params = CS1::ProverParams::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_cs_params =
            CS2::ProverParams::deserialize_with_mode(&mut reader, compress, validate)?;
        Ok(ProverParams {
            poseidon_config: poseidon_canonical_config::<C1::ScalarField>(),
            cs_params,
            cf_cs_params,
        })
    }
}

/// Verification parameters for ProtoGalaxy-based IVC
#[derive(Debug, Clone)]
pub struct VerifierParams<C1, C2, CS1, CS2>
where
    C1: Curve,
    C2: Curve,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
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

impl<C1, C2, CS1, CS2> Valid for VerifierParams<C1, C2, CS1, CS2>
where
    C1: Curve,
    C2: Curve,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
{
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        self.cs_vp.check()?;
        self.cf_cs_vp.check()?;
        Ok(())
    }
}
impl<C1, C2, CS1, CS2> CanonicalSerialize for VerifierParams<C1, C2, CS1, CS2>
where
    C1: Curve,
    C2: Curve,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
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

impl<C1, C2, CS1, CS2> VerifierParams<C1, C2, CS1, CS2>
where
    C1: Curve,
    C2: Curve,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
{
    /// returns the hash of the public parameters of ProtoGalaxy
    pub fn pp_hash(&self) -> Result<C1::ScalarField, Error> {
        // TODO: support hiding commitments in ProtoGalaxy. For now, `H` is set to false. Tracking
        // issue: https://github.com/privacy-scaling-explorations/sonobe/issues/82
        pp_hash::<C1, C2, CS1, CS2, false>(
            &self.r1cs,
            &self.cf_r1cs,
            &self.cs_vp,
            &self.cf_cs_vp,
            &self.poseidon_config,
        )
    }
}

#[derive(PartialEq, Eq, Debug, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct IVCProof<C1: Curve, C2: Curve> {
    pub i: C1::ScalarField,
    pub z_0: Vec<C1::ScalarField>,
    pub z_i: Vec<C1::ScalarField>,
    pub W_i: Witness<C1::ScalarField>,
    pub U_i: CommittedInstance<C1, true>,
    pub w_i: Witness<C1::ScalarField>,
    pub u_i: CommittedInstance<C1, false>,
    pub cf_W_i: CycleFoldWitness<C2>,
    pub cf_U_i: CycleFoldCommittedInstance<C2>,
}

/// Implements ProtoGalaxy+CycleFold's IVC, described in [ProtoGalaxy] and
/// [CycleFold], following the FoldingScheme trait
///
/// [ProtoGalaxy]: https://eprint.iacr.org/2023/1106.pdf
/// [CycleFold]: https://eprint.iacr.org/2023/1192.pdf
#[derive(Clone, Debug)]
pub struct ProtoGalaxy<C1, C2, FC, CS1, CS2>
where
    C1: Curve,
    C2: Curve,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
{
    /// R1CS of the Augmented Function circuit
    pub r1cs: R1CS<C1::ScalarField>,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: R1CS<C2::ScalarField>,
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    /// CommitmentScheme::ProverParams over C1
    pub cs_params: CS1::ProverParams,
    /// CycleFold CommitmentScheme::ProverParams, over C2
    pub cf_cs_params: CS2::ProverParams,
    /// F circuit, the circuit that is being folded
    pub F: FC,
    /// public params hash
    pub pp_hash: C1::ScalarField,
    pub i: C1::ScalarField,
    /// initial state
    pub z_0: Vec<C1::ScalarField>,
    /// current i-th state
    pub z_i: Vec<C1::ScalarField>,
    /// ProtoGalaxy instances
    pub w_i: Witness<C1::ScalarField>,
    pub u_i: CommittedInstance<C1, false>,
    pub W_i: Witness<C1::ScalarField>,
    pub U_i: CommittedInstance<C1, true>,

    /// CycleFold running instance
    pub cf_W_i: CycleFoldWitness<C2>,
    pub cf_U_i: CycleFoldCommittedInstance<C2>,
}

impl<C1, C2, FC, CS1, CS2> ProtoGalaxy<C1, C2, FC, CS1, CS2>
where
    C1: Curve<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    C2: Curve,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
{
    /// This method computes the parameter `t` in ProtoGalaxy for folding `F'`,
    /// the augmented circuit of `F`
    fn compute_t(
        poseidon_config: &PoseidonConfig<CF1<C1>>,
        F: &FC,
        d: usize,
        k: usize,
    ) -> Result<usize, Error> {
        // In ProtoGalaxy, prover and verifier are parameterized by `t = log(n)`
        // where `n` is the number of constraints in the circuit (known as the
        // mapping `f` in the paper).
        // For IVC, `f` is the augmented circuit `F'`, which not only includes
        // the original computation `F`, but also the in-circuit verifier of
        // ProtoGalaxy.
        // Therefore, `t` depends on the size of `F'`, but the size of `F'` in
        // turn depends on `t`.
        // To address this circular dependency, we first find `t_lower_bound`,
        // the lower bound of `t`. Then we incrementally increase `t` and build
        // the circuit `F'` with `t` as ProtoGalaxy's parameter, until `t` is
        // the smallest integer that equals the logarithm of the number of
        // constraints.

        // For `t_lower_bound`, we configure `F'` with `t = 1` and compute log2
        // of the size of `F'`.
        let state_len = F.state_len();

        // `F'` includes `F` and `ProtoGalaxy.V`, where `F` might be costly.
        // Observing that the cost of `F` is constant with respect to `t`, we
        // separately compute `step_constraints`, the size of `F`.
        // Later, we only need to re-run the rest of `F'` with updated `t` to
        // get the size of `F'`.
        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        F.generate_step_constraints(
            cs.clone(),
            0,
            Vec::new_witness(cs.clone(), || Ok(vec![Zero::zero(); state_len]))?,
            FC::ExternalInputsVar::new_witness(cs.clone(), || Ok(FC::ExternalInputs::default()))?,
        )?;
        let step_constraints = cs.num_constraints();

        // Create a dummy circuit with the same state length and external inputs
        // length as `F`, which replaces `F` in the augmented circuit `F'`.
        let dummy_circuit: DummyCircuit = FCircuit::<C1::ScalarField>::new(state_len)?;

        // Compute `augmentation_constraints`, the size of `F'` without `F`.
        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        AugmentedFCircuit::<C1, C2, DummyCircuit>::empty(
            poseidon_config,
            dummy_circuit.clone(),
            1,
            d,
            k,
        )
        .generate_constraints(cs.clone())?;
        let augmentation_constraints = cs.num_constraints();

        // The sum of `step_constraints` and `augmentation_constraints` is the
        // size of `F'` with `t = 1`, and hence the actual `t` should have lower
        // bound `log2(step_constraints + augmentation_constraints)`.
        let t_lower_bound = log2(step_constraints + augmentation_constraints) as usize;
        // Optimization: we in fact only need to try two values of `t`.
        // This is because increasing `t` will only slightly affect the size of
        // `F'` (more specifically, the size of `F'` will never be doubled).
        // Thus, `t_lower_bound` (the log2 size of `F'` with `t = 1`) is very
        // close to the actual `t` (either `t` or `t - 1`).
        let t_upper_bound = t_lower_bound + 1;

        for t in t_lower_bound..=t_upper_bound {
            let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
            AugmentedFCircuit::<C1, C2, DummyCircuit>::empty(
                poseidon_config,
                dummy_circuit.clone(),
                t,
                d,
                k,
            )
            .generate_constraints(cs.clone())?;
            let augmentation_constraints = cs.num_constraints();
            if t == log2(step_constraints + augmentation_constraints) as usize {
                return Ok(t);
            }
        }
        unreachable!()
    }
}

impl<C1, C2, FC, CS1, CS2> FoldingScheme<C1, C2, FC> for ProtoGalaxy<C1, C2, FC, CS1, CS2>
where
    C1: Curve<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    C2: Curve,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
{
    type PreprocessorParam = (PoseidonConfig<CF1<C1>>, FC);
    type ProverParam = ProverParams<C1, C2, CS1, CS2>;
    type VerifierParam = VerifierParams<C1, C2, CS1, CS2>;
    type RunningInstance = (CommittedInstance<C1, true>, Witness<C1::ScalarField>);
    type IncomingInstance = (CommittedInstance<C1, false>, Witness<C1::ScalarField>);
    type MultiCommittedInstanceWithWitness =
        (CommittedInstance<C1, false>, Witness<C1::ScalarField>);
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

        let f_circuit = FC::new(fc_params)?;
        let k = 1;
        let d = R1CS::<CF1<C1>>::empty().degree();
        let t = Self::compute_t(&poseidon_config, &f_circuit, d, k)?;

        // main circuit R1CS:
        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        let augmented_F_circuit =
            AugmentedFCircuit::<C1, C2, FC>::empty(&poseidon_config, f_circuit.clone(), t, d, k);
        augmented_F_circuit.generate_constraints(cs.clone())?;
        cs.finalize();
        let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let r1cs = extract_r1cs::<C1::ScalarField>(&cs)?;

        // CycleFold circuit R1CS
        let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();
        let cf_circuit = CycleFoldCircuit::<_, ProtoGalaxyCycleFoldConfig<C1>>::default();
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
        (poseidon_config, F): &Self::PreprocessorParam,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        // We fix `k`, the number of incoming instances, to 1, because
        // multi-instances folding is not supported yet.
        // TODO: Support multi-instances folding and make `k` a constant generic parameter (as in
        // HyperNova). Tracking issue:
        // https://github.com/privacy-scaling-explorations/sonobe/issues/82
        let k = 1;
        let d = R1CS::<CF1<C1>>::empty().degree();
        let t = Self::compute_t(poseidon_config, F, d, k)?;

        // prepare the circuit to obtain its R1CS
        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();

        let augmented_F_circuit =
            AugmentedFCircuit::<C1, C2, FC>::empty(poseidon_config, F.clone(), t, d, k);
        let cf_circuit = CycleFoldCircuit::<_, ProtoGalaxyCycleFoldConfig<C1>>::default();

        augmented_F_circuit.generate_constraints(cs.clone())?;
        cs.finalize();
        let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let r1cs = extract_r1cs::<C1::ScalarField>(&cs)?;

        cf_circuit.generate_constraints(cs2.clone())?;
        cs2.finalize();
        let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let cf_r1cs = extract_r1cs::<C1::BaseField>(&cs2)?;

        // `CS1` is for committing to ProtoGalaxy's witness vector `w`, so we
        // set `len` to the number of witnesses in `r1cs`.
        let (cs_pp, cs_vp) = CS1::setup(&mut rng, r1cs.n_witnesses())?;
        // `CS2` is for committing to CycleFold's witness vector `w` and error
        // term `e`, where the length of `e` is the number of constraints, so we
        // set `len` to the maximum of `e` and `w`'s lengths.
        let (cf_cs_pp, cf_cs_vp) = CS2::setup(
            &mut rng,
            max(cf_r1cs.n_constraints(), cf_r1cs.n_witnesses()),
        )?;

        Ok((
            Self::ProverParam {
                poseidon_config: poseidon_config.clone(),
                cs_params: cs_pp,
                cf_cs_params: cf_cs_pp,
            },
            Self::VerifierParam {
                poseidon_config: poseidon_config.clone(),
                r1cs,
                cf_r1cs,
                cs_vp,
                cf_cs_vp,
            },
        ))
    }

    /// Initializes the ProtoGalaxy+CycleFold's IVC for the given parameters and
    /// initial state `z_0`.
    fn init(
        (pp, vp): &(Self::ProverParam, Self::VerifierParam),
        F: FC,
        z_0: Vec<C1::ScalarField>,
    ) -> Result<Self, Error> {
        // compute the public params hash
        let pp_hash = vp.pp_hash()?;

        // setup the dummy instances
        let (w_dummy, u_dummy) = vp.r1cs.dummy_witness_instance();
        let (W_dummy, U_dummy) = vp.r1cs.dummy_witness_instance();
        let (cf_W_dummy, cf_U_dummy) = vp.cf_r1cs.dummy_witness_instance();

        // W_dummy=W_0 is a 'dummy witness', all zeroes, but with the size corresponding to the
        // R1CS that we're working with.
        Ok(Self {
            r1cs: vp.r1cs.clone(),
            cf_r1cs: vp.cf_r1cs.clone(),
            poseidon_config: pp.poseidon_config.clone(),
            cs_params: pp.cs_params.clone(),
            cf_cs_params: pp.cf_cs_params.clone(),
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

    /// Implements IVC.P of ProtoGalaxy+CycleFold
    fn prove_step(
        &mut self,
        mut rng: impl RngCore,
        external_inputs: FC::ExternalInputs,
        _other_instances: Option<Self::MultiCommittedInstanceWithWitness>,
    ) -> Result<(), Error> {
        // Multi-instances folding is not supported yet.
        if _other_instances.is_some() {
            return Err(Error::NoMultiInstances);
        }
        // We fix `k`, the number of incoming instances, to 1, because
        // multi-instances folding is not supported yet.
        // TODO: Support multi-instances folding and make `k` a constant generic parameter (as in
        // HyperNova). Tracking issue:
        // https://github.com/privacy-scaling-explorations/sonobe/issues/82
        let k = 1;
        let d = self.r1cs.degree();

        // `sponge` is for digest computation.
        let sponge = PoseidonSponge::<C1::ScalarField>::new_with_pp_hash(
            &self.poseidon_config,
            self.pp_hash,
        );
        // `transcript` is for challenge generation.
        let mut transcript_prover = sponge.clone();

        let mut augmented_F_circuit: AugmentedFCircuit<C1, C2, FC>;

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

        if self.i.is_zero() {
            augmented_F_circuit = AugmentedFCircuit::empty(
                &self.poseidon_config,
                self.F.clone(),
                self.U_i.betas.len(),
                d,
                k,
            );
            augmented_F_circuit.pp_hash = self.pp_hash;
            augmented_F_circuit.z_0.clone_from(&self.z_0);
            augmented_F_circuit.z_i.clone_from(&self.z_i);
            augmented_F_circuit
                .external_inputs
                .clone_from(&external_inputs);

        // There is no need to update `self.U_i` etc. as they are unchanged.
        } else {
            // Primary part:
            // Compute `U_{i+1}` by folding `u_i` into `U_i`.
            let (U_i1, W_i1, proof, aux) = Folding::prove(
                &mut transcript_prover,
                &self.r1cs,
                &self.U_i,
                &self.W_i,
                &[self.u_i.clone()],
                &[self.w_i.clone()],
            )?;

            // CycleFold part:
            // Create cyclefold circuit for enforcing:
            // U_i.phi * L_evals[0] + u_i.phi * L_evals[1] = U_i1.phi
            let (cf_w_i, cf_u_i) = ProtoGalaxyCycleFoldConfig {
                rs: aux.L_X_evals,
                points: vec![self.U_i.phi, self.u_i.phi],
            }
            .build_circuit()
            .generate_incoming_instance_witness::<_, CS2, false>(&self.cf_cs_params, &mut rng)?;

            // fold cf_U_i + cf_u_i -> folded running instance cf_U_i1
            let (cf_W_i1, cf_U_i1, cf_cmTs) =
                CycleFoldAugmentationGadget::fold_native::<_, CS2, false>(
                    &mut transcript_prover,
                    &self.cf_r1cs,
                    &self.cf_cs_params,
                    self.cf_W_i.clone(),
                    self.cf_U_i.clone(),
                    vec![cf_w_i],
                    vec![cf_u_i.clone()],
                )?;

            augmented_F_circuit = AugmentedFCircuit {
                poseidon_config: self.poseidon_config.clone(),
                pp_hash: self.pp_hash,
                i: self.i,
                i_usize,
                z_0: self.z_0.clone(),
                z_i: self.z_i.clone(),
                external_inputs: external_inputs.clone(),
                u_i_phi: self.u_i.phi,
                U_i: self.U_i.clone(),
                U_i1_phi: U_i1.phi,
                F_coeffs: proof.F_coeffs.clone(),
                K_coeffs: proof.K_coeffs.clone(),
                F: self.F.clone(),
                // cyclefold values
                cf_u_i_cmW: cf_u_i.cmW,
                cf_U_i: self.cf_U_i.clone(),
                cf_cmT: cf_cmTs[0],
            };

            #[cfg(test)]
            {
                let mut transcript_verifier = sponge.clone();
                assert_eq!(
                    Folding::verify(
                        &mut transcript_verifier,
                        &self.U_i,
                        &[self.u_i.clone()],
                        proof
                    )?,
                    U_i1
                );
            }

            self.W_i = W_i1;
            self.U_i = U_i1;
            self.cf_W_i = cf_W_i1;
            self.cf_U_i = cf_U_i1;
        }

        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();

        let z_i1 = augmented_F_circuit
            .compute_next_state(cs.clone())?
            .value()?;

        #[cfg(test)]
        assert!(cs.is_satisfied()?);

        let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let (w_i1, x_i1) = extract_w_x::<C1::ScalarField>(&cs);

        #[cfg(test)]
        if x_i1.len() != 2 {
            return Err(Error::NotExpectedLength(x_i1.len(), 2));
        }

        // set values for next iteration
        self.i += C1::ScalarField::one();
        self.z_i = z_i1;
        self.w_i = Witness::new(w_i1);
        self.u_i = self.w_i.commit::<CS1, C1>(&self.cs_params, x_i1)?;

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
        ivc_proof: Self::IVCProof,
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

        Ok(Self {
            r1cs: vp.r1cs.clone(),
            cf_r1cs: vp.cf_r1cs.clone(),
            poseidon_config: pp.poseidon_config,
            cs_params: pp.cs_params,
            cf_cs_params: pp.cf_cs_params,
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

    /// Implements IVC.V of ProtoGalaxy+CycleFold
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

        let sponge = PoseidonSponge::new_with_pp_hash(&vp.poseidon_config, vp.pp_hash()?);

        if u_i.x.len() != 2 || U_i.x.len() != 2 {
            return Err(Error::IVCVerificationFail);
        }

        // check that u_i's output points to the running instance
        // u_i.X[0] == H(i, z_0, z_i, U_i)
        let expected_u_i_x = U_i.hash(&sponge, num_steps, &z_0, &z_i);
        if expected_u_i_x != u_i.x[0] {
            return Err(Error::IVCVerificationFail);
        }
        // u_i.X[1] == H(cf_U_i)
        let expected_cf_u_i_x = cf_U_i.hash_cyclefold(&sponge);
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

#[cfg(test)]
mod tests {
    use super::*;

    use ark_bn254::{Bn254, Fr, G1Projective as Projective};
    use ark_grumpkin::Projective as Projective2;
    use ark_std::test_rng;
    use rayon::prelude::*;

    use crate::{
        commitment::{kzg::KZG, pedersen::Pedersen},
        frontend::utils::CubicFCircuit,
        transcript::poseidon::poseidon_canonical_config,
    };

    /// This test tests the ProtoGalaxy+CycleFold IVC, and by consequence it is
    /// also testing the AugmentedFCircuit
    #[test]
    fn test_ivc() -> Result<(), Error> {
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(())?;

        // run the test using Pedersen commitments on both sides of the curve cycle
        let _ = test_ivc_opt::<Pedersen<Projective>, Pedersen<Projective2>>(
            poseidon_config.clone(),
            F_circuit,
        )?;
        // run the test using KZG for the commitments on the main curve, and Pedersen for the
        // commitments on the secondary curve
        let _ = test_ivc_opt::<KZG<Bn254>, Pedersen<Projective2>>(poseidon_config, F_circuit)?;
        Ok(())
    }

    // test_ivc allowing to choose the CommitmentSchemes
    fn test_ivc_opt<CS1: CommitmentScheme<Projective>, CS2: CommitmentScheme<Projective2>>(
        poseidon_config: PoseidonConfig<Fr>,
        F_circuit: CubicFCircuit<Fr>,
    ) -> Result<(), Error> {
        type PG<CS1, CS2> = ProtoGalaxy<Projective, Projective2, CubicFCircuit<Fr>, CS1, CS2>;

        let params = PG::<CS1, CS2>::preprocess(&mut test_rng(), &(poseidon_config, F_circuit))?;

        let z_0 = vec![Fr::from(3_u32)];
        let mut protogalaxy = PG::init(&params, F_circuit, z_0.clone())?;

        let num_steps: usize = 3;
        for _ in 0..num_steps {
            protogalaxy.prove_step(&mut test_rng(), (), None)?;
        }
        assert_eq!(Fr::from(num_steps as u32), protogalaxy.i);

        let ivc_proof = protogalaxy.ivc_proof();
        PG::<CS1, CS2>::verify(params.1, ivc_proof)?;
        Ok(())
    }

    #[ignore]
    #[test]
    fn test_t_bounds() -> Result<(), Error> {
        let d = R1CS::<Fr>::empty().degree();
        let k = 1;

        let poseidon_config = poseidon_canonical_config::<Fr>();
        for state_len in [1, 10, 100] {
            let dummy_circuit: DummyCircuit = FCircuit::<Fr>::new(state_len)?;

            let costs: Vec<usize> = (1..32)
                .into_par_iter()
                .map(|t| {
                    let cs = ConstraintSystem::<Fr>::new_ref();
                    AugmentedFCircuit::<Projective, Projective2, DummyCircuit>::empty(
                        &poseidon_config,
                        dummy_circuit.clone(),
                        t,
                        d,
                        k,
                    )
                    .generate_constraints(cs.clone())?;
                    Ok(cs.num_constraints())
                })
                .collect::<Result<Vec<usize>, Error>>()?;

            for t_lower_bound in log2(costs[0]) as usize..32 {
                let num_constraints = (1 << t_lower_bound) - costs[0] + costs[t_lower_bound - 1];
                let t = log2(num_constraints) as usize;
                assert!(t == t_lower_bound || t == t_lower_bound + 1);
            }
        }
        Ok(())
    }
}
