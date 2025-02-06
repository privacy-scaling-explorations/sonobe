/// This file implements the onchain (Ethereum's EVM) decider circuit. For non-ethereum use cases,
/// other more efficient approaches can be used.
use ark_crypto_primitives::sponge::{
    constraints::{AbsorbGadget, CryptographicSpongeVar},
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig},
};
use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::{marker::PhantomData, Zero};

use crate::{
    arith::{r1cs::R1CS, ArithRelation, ArithRelationGadget},
    commitment::pedersen::Params as PedersenParams,
    folding::{
        circuits::{
            cyclefold::{
                CycleFoldCommittedInstance, CycleFoldCommittedInstanceVar, CycleFoldWitness,
            },
            decider::{EvalGadget, KZGChallengesGadget},
            nonnative::affine::NonNativeAffineVar,
            CF1, CF2,
        },
        traits::{CommittedInstanceOps, CommittedInstanceVarOps, Dummy, WitnessOps, WitnessVarOps},
    },
    Curve,
};

use super::DeciderEnabledNIFS;

/// A generic circuit tailored for the onchain (Ethereum's EVM) verification of
/// IVC proofs, where we support IVC built upon any folding scheme.
///
/// Specifically, `GenericDeciderEthCircuit` implements the in-circuit version
/// of the IVC verification algorithm, which essentially checks the following:
/// - `R_arith(W_i, U_i)`:
///   The running instance `U_i` and witness `W_i` satisfy `arith`,
///   and the commitments in `U_i` open to the values in `W_i`.
/// - `R_arith(w_i, u_i)`:
///   The incoming instance `u_i` and witness `w_i` satisfy `arith`,
///   and the commitments in `u_i` open to the values in `w_i`.
/// - `R_cf_arith(cf_W_i, cf_U_i)`:
///   The CycleFold instance `cf_U_i` and witness `cf_W_i` satisfy `cf_arith`,
///   and the commitments in `cf_U_i` open to the values in `cf_W_i`.
/// - `u_i` contains the correct hash of the initial and final states.
///
/// To reduce the number of relation checks, the prover, before invoking the
/// circuit, further folds `U_i, u_i` into `U_{i+1}`, and `W_i, w_i` into
/// `W_{i+1}`.
/// Now, the circuit only needs to perform two relation checks, i.e.,
/// `R_arith(W_{i+1}, U_{i+1})` and `R_cf_arith(cf_W_i, cf_U_i)`, plus a few
/// constraints for enforcing the correct hash in `u_i` and the correct folding
/// from `U_i, u_i` to `U_{i+1}`.
///
/// We further reduce the circuit size by avoiding the non-native commitment
/// checks involved in `R_arith(W_{i+1}, U_{i+1})`.
/// Now, we now only check the satisfiability of the constraint system `arith`
/// with the witness `W_{i+1}` and instance `U_{i+1}` in the circuit, but the
/// actual commitment checks are done with the help of KZG.
///
/// For more details, see [https://privacy-scaling-explorations.github.io/sonobe-docs/design/nova-decider-onchain.html].
pub struct GenericOnchainDeciderCircuit<
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
    /// R1CS of the CycleFold circuit
    pub cf_arith: R1CS<CF1<C2>>,
    /// CycleFold PedersenParams over C2
    pub cf_pedersen_params: PedersenParams<C2>,
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
    pub cf_W_i: CycleFoldWitness<C2>,

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
        R1CS<CF1<C2>>,
        PedersenParams<C2>,
        PoseidonConfig<CF1<C1>>,
        D::ProofDummyCfg,
        D::RandomnessDummyCfg,
        usize,
        usize,
    )> for GenericOnchainDeciderCircuit<C1, C2, RU, IU, W, A, AVar, D>
{
    fn dummy(
        (
            arith,
            cf_arith,
            cf_pedersen_params,
            poseidon_config,
            proof_config,
            randomness_config,
            state_len,
            num_commitments,
        ): (
            A,
            R1CS<CF1<C2>>,
            PedersenParams<C2>,
            PoseidonConfig<CF1<C1>>,
            D::ProofDummyCfg,
            D::RandomnessDummyCfg,
            usize,
            usize,
        ),
    ) -> Self {
        Self {
            _avar: PhantomData,
            cf_pedersen_params,
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
            cf_U_i: CycleFoldCommittedInstance::dummy(&cf_arith),
            cf_W_i: CycleFoldWitness::dummy(&cf_arith),
            kzg_challenges: vec![Zero::zero(); num_commitments],
            kzg_evaluations: vec![Zero::zero(); num_commitments],
            arith,
            cf_arith,
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
    > ConstraintSynthesizer<CF1<C1>> for GenericOnchainDeciderCircuit<C1, C2, RU, IU, W, A, AVar, D>
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
            CycleFoldCommittedInstanceVar::<C2>::new_witness(cs.clone(), || Ok(self.cf_U_i))?;

        // allocate the inputs for the check 7.1 and 7.2
        let kzg_challenges = Vec::new_input(cs.clone(), || Ok(self.kzg_challenges))?;
        let kzg_evaluations = Vec::new_input(cs.clone(), || Ok(self.kzg_evaluations))?;

        // `sponge` is for digest computation.
        let sponge = PoseidonSpongeVar::new(cs.clone(), &self.poseidon_config);
        // `transcript` is for challenge generation.
        let mut transcript = sponge.clone();

        // NOTE: we use the same enumeration as in
        // https://privacy-scaling-explorations.github.io/sonobe-docs/design/nova-decider-onchain.html
        // in order to make it easier to reason about.

        // 1. enforce `U_{i+1}` and `W_{i+1}` satisfy `arith`
        arith.enforce_relation(&W_i1, &U_i1)?;

        // 2. enforce `u_i` is an incoming instance
        u_i.enforce_incoming()?;

        // 3. u_i.x[0] == H(i, z_0, z_i, U_i), u_i.x[1] == H(cf_U_i)
        let (u_i_x, U_i_vec) = U_i.hash(&sponge, &pp_hash, &i, &z_0, &z_i)?;
        let (cf_u_i_x, _) = cf_U_i.hash(&sponge, pp_hash.clone())?;
        u_i.get_public_inputs().enforce_equal(&[u_i_x, cf_u_i_x])?;

        #[cfg(feature = "light-test")]
        log::warn!("[WARNING]: Running with the 'light-test' feature, skipping the big part of the DeciderEthCircuit.\n           Only for testing purposes.");

        // The following two checks (and their respective allocations) are disabled for normal
        // tests since they take several millions of constraints and would take several minutes
        // (and RAM) to run the test. It is active by default, and not active only when
        // 'light-test' feature is used.
        #[cfg(not(feature = "light-test"))]
        {
            // imports here instead of at the top of the file, so we avoid having multiple
            // `#[cfg(not(test))]`
            use crate::{
                arith::r1cs::circuits::R1CSMatricesVar,
                commitment::pedersen::PedersenGadget,
                folding::circuits::{
                    cyclefold::CycleFoldWitnessVar, nonnative::uint::NonNativeUintVar,
                },
            };
            use ark_r1cs_std::{convert::ToBitsGadget, groups::CurveVar};
            let cf_W_i = CycleFoldWitnessVar::<C2>::new_witness(cs.clone(), || Ok(self.cf_W_i))?;
            // 4. check Pedersen commitments of cf_U_i.{cmE, cmW}
            let H = C2::Var::constant(self.cf_pedersen_params.h);
            let G = self
                .cf_pedersen_params
                .generators
                .iter()
                .map(|&g| C2::Var::constant(g.into()))
                .collect::<Vec<_>>();
            let cf_W_i_E_bits = cf_W_i
                .E
                .iter()
                .map(|E_i| E_i.to_bits_le())
                .collect::<Result<Vec<_>, _>>()?;
            let cf_W_i_W_bits = cf_W_i
                .W
                .iter()
                .map(|W_i| W_i.to_bits_le())
                .collect::<Result<Vec<_>, _>>()?;
            PedersenGadget::<C2>::commit(&H, &G, &cf_W_i_E_bits, &cf_W_i.rE.to_bits_le()?)?
                .enforce_equal(&cf_U_i.cmE)?;
            PedersenGadget::<C2>::commit(&H, &G, &cf_W_i_W_bits, &cf_W_i.rW.to_bits_le()?)?
                .enforce_equal(&cf_U_i.cmW)?;

            let cf_r1cs = R1CSMatricesVar::<CF1<C2>, NonNativeUintVar<CF2<C2>>>::new_constant(
                ConstraintSystemRef::None,
                self.cf_arith,
            )?;

            // 5. enforce `cf_U_i` and `cf_W_i` satisfy `cf_r1cs`
            cf_r1cs.enforce_relation(&cf_W_i, &cf_U_i)?;
        }

        // 6.1. partially enforce `NIFS.V(U_i, u_i) = U_{i+1}`.
        D::fold_field_elements_gadget(
            &self.arith,
            &mut transcript,
            pp_hash,
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
