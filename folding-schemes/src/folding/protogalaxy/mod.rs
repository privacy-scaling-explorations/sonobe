/// Implements the scheme described in [ProtoGalaxy](https://eprint.iacr.org/2023/1106.pdf)
use ark_crypto_primitives::sponge::{
    poseidon::{PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{CurveGroup, Group};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    groups::{CurveVar, GroupOpsBounds},
    R1CSVar, ToConstraintFieldGadget,
};
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, Namespace, SynthesisError,
};
use ark_std::{
    borrow::Borrow, cmp::max, fmt::Debug, log2, marker::PhantomData, rand::RngCore, One, Zero,
};
use constants::{INCOMING, RUNNING};
use num_bigint::BigUint;

use crate::{
    arith::{
        r1cs::{extract_r1cs, extract_w_x, R1CS},
        Arith,
    },
    commitment::CommitmentScheme,
    folding::circuits::{
        cyclefold::{
            fold_cyclefold_circuit, CycleFoldCircuit, CycleFoldCommittedInstance, CycleFoldConfig,
            CycleFoldWitness,
        },
        nonnative::affine::NonNativeAffineVar,
        CF1, CF2,
    },
    frontend::{utils::DummyCircuit, FCircuit},
    utils::{get_cm_coordinates, pp_hash},
    Error, FoldingScheme,
};

pub mod circuits;
pub mod constants;
pub mod folding;
pub mod traits;
pub(crate) mod utils;

use circuits::AugmentedFCircuit;
use folding::Folding;

use super::traits::{
    CommittedInstanceOps, CommittedInstanceVarOps, Dummy, WitnessOps, WitnessVarOps,
};

/// Configuration for ProtoGalaxy's CycleFold circuit
pub struct ProtoGalaxyCycleFoldConfig<C: CurveGroup> {
    _c: PhantomData<C>,
}

impl<C: CurveGroup> CycleFoldConfig for ProtoGalaxyCycleFoldConfig<C> {
    const RANDOMNESS_BIT_LENGTH: usize = C::ScalarField::MODULUS_BIT_SIZE as usize;
    const N_INPUT_POINTS: usize = 2;
    type C = C;
    type F = C::BaseField;
}

/// CycleFold circuit for computing random linear combinations of group elements
/// in ProtoGalaxy instances.
pub type ProtoGalaxyCycleFoldCircuit<C, GC> = CycleFoldCircuit<ProtoGalaxyCycleFoldConfig<C>, GC>;

/// The committed instance of ProtoGalaxy.
///
/// We use `TYPE` to distinguish between incoming and running instances, as
/// they have slightly different structures (e.g., length of `betas`) and
/// behaviors (e.g., in satisfiability checks).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommittedInstance<C: CurveGroup, const TYPE: bool> {
    phi: C,
    betas: Vec<C::ScalarField>,
    e: C::ScalarField,
    x: Vec<C::ScalarField>,
}

impl<C: CurveGroup, const TYPE: bool> Dummy<(usize, usize)> for CommittedInstance<C, TYPE> {
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

impl<C: CurveGroup, const TYPE: bool> Dummy<&R1CS<CF1<C>>> for CommittedInstance<C, TYPE> {
    fn dummy(r1cs: &R1CS<CF1<C>>) -> Self {
        let t = if TYPE == RUNNING {
            log2(r1cs.num_constraints()) as usize
        } else {
            0
        };
        Self::dummy((r1cs.num_public_inputs(), t))
    }
}

impl<C: CurveGroup, const TYPE: bool> CommittedInstanceOps<C> for CommittedInstance<C, TYPE> {
    type Var = CommittedInstanceVar<C, TYPE>;

    fn get_commitments(&self) -> Vec<C> {
        vec![self.phi]
    }

    fn is_incoming(&self) -> bool {
        TYPE == INCOMING
    }
}

#[derive(Clone, Debug)]
pub struct CommittedInstanceVar<C: CurveGroup, const TYPE: bool> {
    phi: NonNativeAffineVar<C>,
    betas: Vec<FpVar<C::ScalarField>>,
    e: FpVar<C::ScalarField>,
    x: Vec<FpVar<C::ScalarField>>,
}

impl<C: CurveGroup, const TYPE: bool> AllocVar<CommittedInstance<C, TYPE>, C::ScalarField>
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

impl<C: CurveGroup, const TYPE: bool> R1CSVar<C::ScalarField> for CommittedInstanceVar<C, TYPE> {
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

impl<C: CurveGroup, const TYPE: bool> CommittedInstanceVarOps<C> for CommittedInstanceVar<C, TYPE> {
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

#[derive(Clone, Debug)]
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

    pub fn commit<CS: CommitmentScheme<C>, C: CurveGroup<ScalarField = F>>(
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
            w: vec![F::zero(); r1cs.num_witnesses()],
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
    C1: CurveGroup,
    C2: CurveGroup,
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

/// Verification parameters for ProtoGalaxy-based IVC
#[derive(Debug, Clone)]
pub struct VerifierParams<C1, C2, CS1, CS2>
where
    C1: CurveGroup,
    C2: CurveGroup,
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

impl<C1, C2, CS1, CS2> VerifierParams<C1, C2, CS1, CS2>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
{
    /// returns the hash of the public parameters of ProtoGalaxy
    pub fn pp_hash(&self) -> Result<C1::ScalarField, Error> {
        // TODO (@winderica): support hiding commitments in ProtoGalaxy.
        // For now, `H` is set to false.
        // Tracking issue: https://github.com/privacy-scaling-explorations/sonobe/issues/82
        pp_hash::<C1, C2, CS1, CS2, false>(
            &self.r1cs,
            &self.cf_r1cs,
            &self.cs_vp,
            &self.cf_cs_vp,
            &self.poseidon_config,
        )
    }
}

/// Implements ProtoGalaxy+CycleFold's IVC, described in [ProtoGalaxy] and
/// [CycleFold], following the FoldingScheme trait
///
/// [ProtoGalaxy]: https://eprint.iacr.org/2023/1106.pdf
/// [CycleFold]: https://eprint.iacr.org/2023/1192.pdf
#[derive(Clone, Debug)]
pub struct ProtoGalaxy<C1, GC1, C2, GC2, FC, CS1, CS2>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
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

impl<C1, GC1, C2, GC2, FC, CS1, CS2> ProtoGalaxy<C1, GC1, C2, GC2, FC, CS1, CS2>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    C1::ScalarField: Absorb,
    C2::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    /// This method computes the parameter `t` in ProtoGalaxy for folding `F'`,
    /// the augmented circuit of `F`
    fn compute_t(
        poseidon_config: &PoseidonConfig<CF1<C1>>,
        F: &FC,
        d: usize,
        k: usize,
    ) -> Result<usize, SynthesisError> {
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
        let external_inputs_len = F.external_inputs_len();

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
            Vec::new_witness(cs.clone(), || Ok(vec![Zero::zero(); external_inputs_len]))?,
        )?;
        let step_constraints = cs.num_constraints();

        // Create a dummy circuit with the same state length and external inputs
        // length as `F`, which replaces `F` in the augmented circuit `F'`.
        let dummy_circuit: DummyCircuit =
            FCircuit::<C1::ScalarField>::new((state_len, external_inputs_len)).unwrap();

        // Compute `augmentation_constraints`, the size of `F'` without `F`.
        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        AugmentedFCircuit::<C1, C2, GC2, DummyCircuit>::empty(
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
            AugmentedFCircuit::<C1, C2, GC2, DummyCircuit>::empty(
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

impl<C1, GC1, C2, GC2, FC, CS1, CS2> FoldingScheme<C1, C2, FC>
    for ProtoGalaxy<C1, GC1, C2, GC2, FC, CS1, CS2>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    C1::ScalarField: Absorb,
    C2::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    type PreprocessorParam = (PoseidonConfig<CF1<C1>>, FC);
    type ProverParam = ProverParams<C1, C2, CS1, CS2>;
    type VerifierParam = VerifierParams<C1, C2, CS1, CS2>;
    type RunningInstance = (CommittedInstance<C1, true>, Witness<C1::ScalarField>);
    type IncomingInstance = (CommittedInstance<C1, false>, Witness<C1::ScalarField>);
    type MultiCommittedInstanceWithWitness =
        (CommittedInstance<C1, false>, Witness<C1::ScalarField>);
    type CFInstance = (CycleFoldCommittedInstance<C2>, CycleFoldWitness<C2>);

    fn preprocess(
        mut rng: impl RngCore,
        (poseidon_config, F): &Self::PreprocessorParam,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        // We fix `k`, the number of incoming instances, to 1, because
        // multi-instances folding is not supported yet.
        // TODO (@winderica): Support multi-instances folding and make `k` a
        // constant generic parameter (as in HyperNova)
        // Tracking issue: https://github.com/privacy-scaling-explorations/sonobe/issues/82
        let k = 1;
        // `d`, the degree of the constraint system, is set to 2, as we only
        // support R1CS for now, whose highest degree is 2.
        let d = 2;
        let t = Self::compute_t(poseidon_config, F, d, k)?;

        // prepare the circuit to obtain its R1CS
        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();

        let augmented_F_circuit =
            AugmentedFCircuit::<C1, C2, GC2, FC>::empty(poseidon_config, F.clone(), t, d, k);
        let cf_circuit = ProtoGalaxyCycleFoldCircuit::<C1, GC1>::empty();

        augmented_F_circuit.generate_constraints(cs.clone())?;
        cs.finalize();
        let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let r1cs = extract_r1cs::<C1::ScalarField>(&cs);

        cf_circuit.generate_constraints(cs2.clone())?;
        cs2.finalize();
        let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let cf_r1cs = extract_r1cs::<C1::BaseField>(&cs2);

        let (cs_pp, cs_vp) = CS1::setup(&mut rng, r1cs.A.n_rows)?;
        let (cf_cs_pp, cf_cs_vp) = CS2::setup(&mut rng, max(cf_r1cs.A.n_rows, cf_r1cs.A.n_cols))?;

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
            _gc1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,
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
        external_inputs: Vec<C1::ScalarField>,
        _other_instances: Option<Self::MultiCommittedInstanceWithWitness>,
    ) -> Result<(), Error> {
        // Multi-instances folding is not supported yet.
        if _other_instances.is_some() {
            return Err(Error::NoMultiInstances);
        }
        // We fix `k`, the number of incoming instances, to 1, because
        // multi-instances folding is not supported yet.
        // TODO (@winderica): Support multi-instances folding and make `k` a
        // constant generic parameter (as in HyperNova)
        // Tracking issue: https://github.com/privacy-scaling-explorations/sonobe/issues/82
        let k = 1;
        // `d`, the degree of the constraint system, is set to 2, as we only
        // support R1CS for now, whose highest degree is 2.
        let d = 2;

        // `sponge` is for digest computation.
        let sponge = PoseidonSponge::<C1::ScalarField>::new(&self.poseidon_config);
        // `transcript` is for challenge generation.
        let mut transcript_prover = sponge.clone();

        let mut augmented_F_circuit: AugmentedFCircuit<C1, C2, GC2, FC>;

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

        let i_bn: BigUint = self.i.into();
        let i_usize: usize = i_bn.try_into().map_err(|_| Error::MaxStep)?;

        let z_i1 = self
            .F
            .step_native(i_usize, self.z_i.clone(), external_inputs.clone())?;

        // folded instance output (public input, x)
        // u_{i+1}.x[0] = H(i+1, z_0, z_{i+1}, U_{i+1})
        let u_i1_x: C1::ScalarField;
        // u_{i+1}.x[1] = H(cf_U_{i+1})
        let cf_u_i1_x: C1::ScalarField;

        if self.i.is_zero() {
            // Take extra care of the base case
            // `U_{i+1}` (i.e., `U_1`) is fixed to `U_dummy`, so we just use
            // `self.U_i = U_0 = U_dummy`.
            u_i1_x = self.U_i.hash(
                &sponge,
                self.pp_hash,
                self.i + C1::ScalarField::one(),
                &self.z_0,
                &z_i1,
            );
            // `cf_U_{i+1}` (i.e., `cf_U_1`) is fixed to `cf_U_dummy`, so we
            // just use `self.cf_U_i = cf_U_0 = cf_U_dummy`.
            cf_u_i1_x = self.cf_U_i.hash_cyclefold(&sponge, self.pp_hash);

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
            let (U_i1, W_i1, F_coeffs, K_coeffs, L_evals, phi_stars) = Folding::prove(
                &mut transcript_prover,
                &self.r1cs,
                &self.U_i,
                &self.W_i,
                &[self.u_i.clone()],
                &[self.w_i.clone()],
            )?;

            // CycleFold part:
            // get the vector used as public inputs 'x' in the CycleFold circuit
            let mut r0_bits = L_evals[0].into_bigint().to_bits_le();
            let mut r1_bits = L_evals[1].into_bigint().to_bits_le();
            r0_bits.resize(C1::ScalarField::MODULUS_BIT_SIZE as usize, false);
            r1_bits.resize(C1::ScalarField::MODULUS_BIT_SIZE as usize, false);

            // cyclefold circuit for enforcing:
            // 0 + U_i.phi * L_evals[0] == phi_stars[0]
            let cf1_u_i_x = [
                r0_bits
                    .chunks(C1::BaseField::MODULUS_BIT_SIZE as usize - 1)
                    .map(BigInteger::from_bits_le)
                    .map(C1::BaseField::from_bigint)
                    .collect::<Option<Vec<_>>>()
                    .unwrap(),
                get_cm_coordinates(&C1::zero()),
                get_cm_coordinates(&self.U_i.phi),
                get_cm_coordinates(&phi_stars[0]),
            ]
            .concat();
            let cf1_circuit = ProtoGalaxyCycleFoldCircuit::<C1, GC1> {
                _gc: PhantomData,
                r_bits: Some(r0_bits),
                points: Some(vec![C1::zero(), self.U_i.phi]),
                x: Some(cf1_u_i_x.clone()),
            };

            // cyclefold circuit for enforcing:
            // phi_stars[0] + u_i.phi * L_evals[1] == U_i1.phi
            // i.e., U_i.phi * L_evals[0] + u_i.phi * L_evals[1] == U_i1.phi
            let cf2_u_i_x = [
                r1_bits
                    .chunks(C1::BaseField::MODULUS_BIT_SIZE as usize - 1)
                    .map(BigInteger::from_bits_le)
                    .map(C1::BaseField::from_bigint)
                    .collect::<Option<Vec<_>>>()
                    .unwrap(),
                get_cm_coordinates(&phi_stars[0]),
                get_cm_coordinates(&self.u_i.phi),
                get_cm_coordinates(&U_i1.phi),
            ]
            .concat();
            let cf2_circuit = ProtoGalaxyCycleFoldCircuit::<C1, GC1> {
                _gc: PhantomData,
                r_bits: Some(r1_bits),
                points: Some(vec![phi_stars[0], self.u_i.phi]),
                x: Some(cf2_u_i_x.clone()),
            };

            // fold self.cf_U_i + cf1_U -> folded running with cf1
            let (_cf1_w_i, cf1_u_i, cf1_W_i1, cf1_U_i1, cf1_cmT, _) = self.fold_cyclefold_circuit(
                &mut transcript_prover,
                self.cf_W_i.clone(), // CycleFold running instance witness
                self.cf_U_i.clone(), // CycleFold running instance
                cf1_u_i_x,
                cf1_circuit,
                &mut rng,
            )?;
            // fold [the output from folding self.cf_U_i + cf1_U] + cf2_U = folded_running_with_cf1 + cf2
            let (_cf2_w_i, cf2_u_i, cf_W_i1, cf_U_i1, cf2_cmT, _) = self.fold_cyclefold_circuit(
                &mut transcript_prover,
                cf1_W_i1,
                cf1_U_i1.clone(),
                cf2_u_i_x,
                cf2_circuit,
                &mut rng,
            )?;

            // Derive `u_{i+1}.x[0], u_{i+1}.x[1]` by hashing folded instances
            u_i1_x = U_i1.hash(
                &sponge,
                self.pp_hash,
                self.i + C1::ScalarField::one(),
                &self.z_0,
                &z_i1,
            );
            cf_u_i1_x = cf_U_i1.hash_cyclefold(&sponge, self.pp_hash);

            augmented_F_circuit = AugmentedFCircuit {
                _gc2: PhantomData,
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
                F_coeffs: F_coeffs.clone(),
                K_coeffs: K_coeffs.clone(),
                phi_stars,
                F: self.F.clone(),
                x: Some(u_i1_x),
                // cyclefold values
                cf1_u_i_cmW: cf1_u_i.cmW,
                cf2_u_i_cmW: cf2_u_i.cmW,
                cf_U_i: self.cf_U_i.clone(),
                cf1_cmT,
                cf2_cmT,
                cf_x: Some(cf_u_i1_x),
            };

            #[cfg(test)]
            {
                let mut transcript_verifier = sponge.clone();
                assert_eq!(
                    Folding::verify(
                        &mut transcript_verifier,
                        &self.U_i,
                        &[self.u_i.clone()],
                        F_coeffs,
                        K_coeffs
                    )?,
                    U_i1
                );
                cf1_u_i.check_incoming()?;
                cf2_u_i.check_incoming()?;
                self.cf_r1cs.check_relation(&_cf1_w_i, &cf1_u_i)?;
                self.cf_r1cs.check_relation(&_cf2_w_i, &cf2_u_i)?;
                self.cf_r1cs.check_relation(&self.cf_W_i, &self.cf_U_i)?;
            }

            self.W_i = W_i1;
            self.U_i = U_i1;
            self.cf_W_i = cf_W_i1;
            self.cf_U_i = cf_U_i1;
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

    /// Implements IVC.V of ProtoGalaxy+CycleFold
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

impl<C1, GC1, C2, GC2, FC, CS1, CS2> ProtoGalaxy<C1, GC1, C2, GC2, FC, CS1, CS2>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
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
{
    // folds the given cyclefold circuit and its instances
    #[allow(clippy::type_complexity)]
    fn fold_cyclefold_circuit(
        &self,
        transcript: &mut PoseidonSponge<C1::ScalarField>,
        cf_W_i: CycleFoldWitness<C2>, // witness of the running instance
        cf_U_i: CycleFoldCommittedInstance<C2>, // running instance
        cf_u_i_x: Vec<C2::ScalarField>,
        cf_circuit: ProtoGalaxyCycleFoldCircuit<C1, GC1>,
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
        fold_cyclefold_circuit::<ProtoGalaxyCycleFoldConfig<C1>, C1, GC1, C2, GC2, CS2, false>(
            transcript,
            self.cf_r1cs.clone(),
            self.cf_cs_params.clone(),
            self.pp_hash,
            cf_W_i,
            cf_U_i,
            cf_u_i_x,
            cf_circuit,
            rng,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as Projective};
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
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
    fn test_ivc() {
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();

        // run the test using Pedersen commitments on both sides of the curve cycle
        test_ivc_opt::<Pedersen<Projective>, Pedersen<Projective2>>(
            poseidon_config.clone(),
            F_circuit,
        );
        // run the test using KZG for the commitments on the main curve, and Pedersen for the
        // commitments on the secondary curve
        test_ivc_opt::<KZG<Bn254>, Pedersen<Projective2>>(poseidon_config, F_circuit);
    }

    // test_ivc allowing to choose the CommitmentSchemes
    fn test_ivc_opt<CS1: CommitmentScheme<Projective>, CS2: CommitmentScheme<Projective2>>(
        poseidon_config: PoseidonConfig<Fr>,
        F_circuit: CubicFCircuit<Fr>,
    ) {
        type PG<CS1, CS2> =
            ProtoGalaxy<Projective, GVar, Projective2, GVar2, CubicFCircuit<Fr>, CS1, CS2>;

        let params =
            PG::<CS1, CS2>::preprocess(&mut test_rng(), &(poseidon_config, F_circuit)).unwrap();

        let z_0 = vec![Fr::from(3_u32)];
        let mut protogalaxy = PG::init(&params, F_circuit, z_0.clone()).unwrap();

        let num_steps: usize = 3;
        for _ in 0..num_steps {
            protogalaxy
                .prove_step(&mut test_rng(), vec![], None)
                .unwrap();
        }
        assert_eq!(Fr::from(num_steps as u32), protogalaxy.i);

        let (running_instance, incoming_instance, cyclefold_instance) = protogalaxy.instances();
        PG::<CS1, CS2>::verify(
            params.1,
            z_0,
            protogalaxy.z_i,
            protogalaxy.i,
            running_instance,
            incoming_instance,
            cyclefold_instance,
        )
        .unwrap();
    }

    #[ignore]
    #[test]
    fn test_t_bounds() {
        let d = 2;
        let k = 1;

        let poseidon_config = poseidon_canonical_config::<Fr>();
        for state_len in [1, 10, 100] {
            for external_inputs_len in [1, 10, 100] {
                let dummy_circuit: DummyCircuit =
                    FCircuit::<Fr>::new((state_len, external_inputs_len)).unwrap();

                let costs = (1..32)
                    .into_par_iter()
                    .map(|t| {
                        let cs = ConstraintSystem::<Fr>::new_ref();
                        AugmentedFCircuit::<Projective, Projective2, GVar2, DummyCircuit>::empty(
                            &poseidon_config,
                            dummy_circuit.clone(),
                            t,
                            d,
                            k,
                        )
                        .generate_constraints(cs.clone())
                        .unwrap();
                        cs.num_constraints()
                    })
                    .collect::<Vec<_>>();

                for t_lower_bound in log2(costs[0]) as usize..32 {
                    let num_constraints =
                        (1 << t_lower_bound) - costs[0] + costs[t_lower_bound - 1];
                    let t = log2(num_constraints) as usize;
                    assert!(t == t_lower_bound || t == t_lower_bound + 1);
                }
            }
        }
    }
}
