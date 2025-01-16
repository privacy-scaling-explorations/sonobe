/// This file implements a generic offchain decider circuit.
/// For ethereum use cases, use the `GenericOnchainDeciderCircuit`.
/// More details can be found at the documentation page:
/// https://privacy-scaling-explorations.github.io/sonobe-docs/design/nova-decider-offchain.html
use ark_crypto_primitives::sponge::{
    constraints::AbsorbGadget,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig},
};
use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::{marker::PhantomData, Zero};

use crate::{
    arith::{
        r1cs::{circuits::R1CSMatricesVar, R1CS},
        ArithRelation, ArithRelationGadget,
    },
    folding::{
        circuits::{
            cyclefold::{
                CycleFoldCommittedInstance, CycleFoldCommittedInstanceVar, CycleFoldWitness,
            },
            decider::{EvalGadget, KZGChallengesGadget},
            nonnative::affine::NonNativeAffineVar,
            CF1, CF2,
        },
        nova::{decider_eth_circuit::WitnessVar, nifs::nova_circuits::CommittedInstanceVar},
        traits::{CommittedInstanceOps, CommittedInstanceVarOps, Dummy, WitnessOps, WitnessVarOps},
    },
    transcript::TranscriptVar,
    Curve,
};

use super::DeciderEnabledNIFS;

/// Circuit that implements part of the in-circuit checks needed for the offchain verification over
/// the Curve2's BaseField (=Curve1's ScalarField).
pub struct GenericOffchainDeciderCircuit1<
    C1: Curve,
    C2: Curve,
    RU: CommittedInstanceOps<C1>,               // Running instance
    IU: CommittedInstanceOps<C1>,               // Incoming instance
    W: WitnessOps<CF1<C1>>,                     // Witness
    A: ArithRelation<W, RU>,                    // Constraint system
    AVar: ArithRelationGadget<W::Var, RU::Var>, // In-circuit representation of `A`
    D: DeciderEnabledNIFS<C1, RU, IU, W, A>,
> {
    pub _avar: PhantomData<AVar>,
    /// Constraint system of the Augmented Function circuit
    pub arith: A,
    pub poseidon_config: PoseidonConfig<CF1<C1>>,
    /// public params hash
    pub pp_hash: CF1<C1>,
    pub i: CF1<C1>,
    /// initial state
    pub z_0: Vec<CF1<C1>>,
    /// current i-th state
    pub z_i: Vec<CF1<C1>>,
    /// Folding scheme instances
    pub U_i: RU,
    pub W_i: W,
    pub u_i: IU,
    pub w_i: W,
    pub U_i1: RU,
    pub W_i1: W,

    /// Helper for folding verification
    pub proof: D::Proof,
    pub randomness: D::Randomness,

    /// CycleFold running instance
    pub cf_U_i: CycleFoldCommittedInstance<C2>,

    /// KZG challenges
    pub kzg_challenges: Vec<CF1<C1>>,
    pub kzg_evaluations: Vec<CF1<C1>>,
}

impl<
        C1: Curve,
        C2: Curve<ScalarField = CF2<C1>, BaseField = CF1<C1>>,
        RU: CommittedInstanceOps<C1> + for<'a> Dummy<&'a A>,
        IU: CommittedInstanceOps<C1> + for<'a> Dummy<&'a A>,
        W: WitnessOps<CF1<C1>> + for<'a> Dummy<&'a A>,
        A: ArithRelation<W, RU>,
        AVar: ArithRelationGadget<W::Var, RU::Var> + AllocVar<A, CF1<C1>>,
        D: DeciderEnabledNIFS<C1, RU, IU, W, A>,
    >
    Dummy<(
        A,
        &R1CS<CF1<C2>>,
        PoseidonConfig<CF1<C1>>,
        D::ProofDummyCfg,
        D::RandomnessDummyCfg,
        usize,
        usize,
    )> for GenericOffchainDeciderCircuit1<C1, C2, RU, IU, W, A, AVar, D>
{
    fn dummy(
        (
            arith,
            cf_arith,
            poseidon_config,
            proof_config,
            randomness_config,
            state_len,
            num_commitments,
        ): (
            A,
            &R1CS<CF1<C2>>,
            PoseidonConfig<CF1<C1>>,
            D::ProofDummyCfg,
            D::RandomnessDummyCfg,
            usize,
            usize,
        ),
    ) -> Self {
        Self {
            _avar: PhantomData,
            poseidon_config,
            pp_hash: Zero::zero(),
            i: Zero::zero(),
            z_0: vec![Zero::zero(); state_len],
            z_i: vec![Zero::zero(); state_len],
            U_i: RU::dummy(&arith),
            W_i: W::dummy(&arith),
            u_i: IU::dummy(&arith),
            w_i: W::dummy(&arith),
            U_i1: RU::dummy(&arith),
            W_i1: W::dummy(&arith),
            proof: D::Proof::dummy(proof_config),
            randomness: D::Randomness::dummy(randomness_config),
            cf_U_i: CycleFoldCommittedInstance::dummy(cf_arith),
            kzg_challenges: vec![Zero::zero(); num_commitments],
            kzg_evaluations: vec![Zero::zero(); num_commitments],
            arith,
        }
    }
}

impl<
        C1: Curve,
        C2: Curve<ScalarField = CF2<C1>, BaseField = CF1<C1>>,
        RU: CommittedInstanceOps<C1>,
        IU: CommittedInstanceOps<C1>,
        W: WitnessOps<CF1<C1>>,
        A: ArithRelation<W, RU>,
        AVar: ArithRelationGadget<W::Var, RU::Var> + AllocVar<A, CF1<C1>>,
        D: DeciderEnabledNIFS<C1, RU, IU, W, A>,
    > ConstraintSynthesizer<CF1<C1>>
    for GenericOffchainDeciderCircuit1<C1, C2, RU, IU, W, A, AVar, D>
where
    RU::Var: AbsorbGadget<CF1<C1>> + CommittedInstanceVarOps<C1, PointVar = NonNativeAffineVar<C1>>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
        let arith = AVar::new_witness(cs.clone(), || Ok(&self.arith))?;

        let pp_hash = FpVar::new_input(cs.clone(), || Ok(self.pp_hash))?;
        let i = FpVar::new_input(cs.clone(), || Ok(self.i))?;
        let z_0 = Vec::new_input(cs.clone(), || Ok(self.z_0))?;
        let z_i = Vec::new_input(cs.clone(), || Ok(self.z_i))?;

        let u_i = IU::Var::new_witness(cs.clone(), || Ok(self.u_i))?;
        let U_i = RU::Var::new_witness(cs.clone(), || Ok(self.U_i))?;
        // here (U_i1, W_i1) = NIFS.P( (U_i,W_i), (u_i,w_i))
        let U_i1_commitments = Vec::<NonNativeAffineVar<C1>>::new_input(cs.clone(), || {
            Ok(self.U_i1.get_commitments())
        })?;
        let U_i1 = RU::Var::new_witness(cs.clone(), || Ok(self.U_i1))?;
        let W_i1 = W::Var::new_witness(cs.clone(), || Ok(self.W_i1))?;
        U_i1.get_commitments().enforce_equal(&U_i1_commitments)?;

        let cf_U_i =
            CycleFoldCommittedInstanceVar::<C2>::new_input(cs.clone(), || Ok(self.cf_U_i))?;

        // allocate the inputs for the checks 7.1 and 7.2
        let kzg_challenges = Vec::new_input(cs.clone(), || Ok(self.kzg_challenges))?;
        let kzg_evaluations = Vec::new_input(cs.clone(), || Ok(self.kzg_evaluations))?;

        // `sponge` is for digest computation.
        // notice that `pp_hash` has already been absorbed during init.
        let sponge = PoseidonSpongeVar::new_with_pp_hash(&self.poseidon_config, &pp_hash)?;
        // `transcript` is for challenge generation.
        let mut transcript = sponge.clone();

        // 1. enforce `U_{i+1}` and `W_{i+1}` satisfy `arith`
        arith.enforce_relation(&W_i1, &U_i1)?;

        // 2. enforce `u_i` is an incoming instance
        u_i.enforce_incoming()?;

        // 3. u_i.x[0] == H(i, z_0, z_i, U_i), u_i.x[1] == H(cf_U_i)
        let (u_i_x, U_i_vec) = U_i.hash(&sponge, &i, &z_0, &z_i)?;
        let (cf_u_i_x, _) = cf_U_i.hash(&sponge)?;
        u_i.get_public_inputs().enforce_equal(&[u_i_x, cf_u_i_x])?;

        // 6.1. partially enforce `NIFS.V(U_i, u_i) = U_{i+1}`.
        D::fold_field_elements_gadget(
            &self.arith,
            &mut transcript,
            U_i,
            U_i_vec,
            u_i,
            self.proof,
            self.randomness,
        )?
        .enforce_partial_equal(&U_i1)?;

        // 7.1. compute and check KZG challenges
        KZGChallengesGadget::get_challenges_gadget(&mut transcript, &U_i1)?
            .enforce_equal(&kzg_challenges)?;

        // 7.2. check the claimed evaluations
        for (((v, _r), c), e) in W_i1
            .get_openings()
            .iter()
            .zip(&kzg_challenges)
            .zip(&kzg_evaluations)
        {
            // The randomness `_r` is currently not used.
            EvalGadget::evaluate_gadget(v, c)?.enforce_equal(e)?;
        }

        Ok(())
    }
}

/// Circuit that implements part of the in-circuit checks needed for the offchain verification over
/// the Curve1's BaseField (=Curve2's ScalarField).
pub struct GenericOffchainDeciderCircuit2<C2: Curve> {
    /// R1CS of the CycleFold circuit
    pub cf_arith: R1CS<CF1<C2>>,
    pub poseidon_config: PoseidonConfig<CF1<C2>>,
    /// public params hash
    pub pp_hash: CF1<C2>,

    /// CycleFold running instance
    pub cf_U_i: CycleFoldCommittedInstance<C2>,
    pub cf_W_i: CycleFoldWitness<C2>,

    /// KZG challenges
    pub kzg_challenges: Vec<CF1<C2>>,
    pub kzg_evaluations: Vec<CF1<C2>>,
}

impl<C2: Curve> Dummy<(R1CS<CF1<C2>>, PoseidonConfig<CF1<C2>>, usize)>
    for GenericOffchainDeciderCircuit2<C2>
{
    fn dummy(
        (cf_arith, poseidon_config, num_commitments): (
            R1CS<CF1<C2>>,
            PoseidonConfig<CF1<C2>>,
            usize,
        ),
    ) -> Self {
        Self {
            poseidon_config,
            pp_hash: Zero::zero(),
            cf_U_i: CycleFoldCommittedInstance::dummy(&cf_arith),
            cf_W_i: CycleFoldWitness::dummy(&cf_arith),
            kzg_challenges: vec![Zero::zero(); num_commitments],
            kzg_evaluations: vec![Zero::zero(); num_commitments],
            cf_arith,
        }
    }
}

impl<C2: Curve> ConstraintSynthesizer<CF1<C2>> for GenericOffchainDeciderCircuit2<C2> {
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C2>>) -> Result<(), SynthesisError> {
        let cf_r1cs = R1CSMatricesVar::<CF1<C2>, FpVar<CF1<C2>>>::new_witness(cs.clone(), || {
            Ok(self.cf_arith.clone())
        })?;

        let pp_hash = FpVar::new_input(cs.clone(), || Ok(self.pp_hash))?;

        let cf_U_i = CommittedInstanceVar::new_input(cs.clone(), || Ok(self.cf_U_i))?;
        let cf_W_i = WitnessVar::new_witness(cs.clone(), || Ok(self.cf_W_i))?;

        // allocate the inputs for the checks 4.1 and 4.2
        let kzg_challenges = Vec::new_input(cs.clone(), || Ok(self.kzg_challenges))?;
        let kzg_evaluations = Vec::new_input(cs.clone(), || Ok(self.kzg_evaluations))?;

        // `transcript` is for challenge generation.
        let mut transcript = PoseidonSpongeVar::new_with_pp_hash(&self.poseidon_config, &pp_hash)?;

        // 5. enforce `cf_U_i` and `cf_W_i` satisfy `cf_r1cs`
        cf_r1cs.enforce_relation(&cf_W_i, &cf_U_i)?;

        // 4.1. compute and check KZG challenges
        KZGChallengesGadget::get_challenges_gadget(&mut transcript, &cf_U_i)?
            .enforce_equal(&kzg_challenges)?;

        // 4.2. check the claimed evaluations
        for (((v, _r), c), e) in cf_W_i
            .get_openings()
            .iter()
            .zip(&kzg_challenges)
            .zip(&kzg_evaluations)
        {
            // The randomness `_r` is currently not used.
            EvalGadget::evaluate_gadget(v, c)?.enforce_equal(e)?;
        }

        Ok(())
    }
}
