/// This file implements the onchain (Ethereum's EVM) decider circuit. For non-ethereum use cases,
/// other more efficient approaches can be used.
/// More details can be found at the documentation page:
/// https://privacy-scaling-explorations.github.io/sonobe-docs/design/nova-decider-onchain.html
use ark_crypto_primitives::sponge::poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    fields::fp::FpVar,
    R1CSVar,
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::{borrow::Borrow, marker::PhantomData};

use super::{
    nifs::nova_circuits::{CommittedInstanceVar, NIFSGadget},
    nifs::{nova::NIFS, NIFSGadgetTrait, NIFSTrait},
    CommittedInstance, Nova, Witness,
};
use crate::{
    arith::r1cs::{circuits::R1CSMatricesVar, R1CS},
    commitment::{pedersen::Params as PedersenParams, CommitmentScheme},
    folding::{
        circuits::{
            decider::{
                on_chain::GenericOnchainDeciderCircuit, DeciderEnabledNIFS, EvalGadget,
                KZGChallengesGadget,
            },
            nonnative::affine::NonNativeAffineVar,
            CF1,
        },
        traits::{WitnessOps, WitnessVarOps},
    },
    frontend::FCircuit,
    transcript::Transcript,
    Curve, Error,
};

/// In-circuit representation of the Witness associated to the CommittedInstance.
#[derive(Debug, Clone)]
pub struct WitnessVar<C: Curve> {
    pub E: Vec<FpVar<C::ScalarField>>,
    pub rE: FpVar<C::ScalarField>,
    pub W: Vec<FpVar<C::ScalarField>>,
    pub rW: FpVar<C::ScalarField>,
}

impl<C: Curve> AllocVar<Witness<C>, CF1<C>> for WitnessVar<C> {
    fn new_variable<T: Borrow<Witness<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let E: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().E.clone()), mode)?;
            let rE =
                FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().rE), mode)?;

            let W: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().W.clone()), mode)?;
            let rW =
                FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().rW), mode)?;

            Ok(Self { E, rE, W, rW })
        })
    }
}

impl<C: Curve> WitnessVarOps<C::ScalarField> for WitnessVar<C> {
    fn get_openings(&self) -> Vec<(&[FpVar<C::ScalarField>], FpVar<C::ScalarField>)> {
        vec![(&self.W, self.rW.clone()), (&self.E, self.rE.clone())]
    }
}

pub type DeciderEthCircuit<C1, C2> = GenericOnchainDeciderCircuit<
    C1,
    C2,
    CommittedInstance<C1>,
    CommittedInstance<C1>,
    Witness<C1>,
    R1CS<CF1<C1>>,
    R1CSMatricesVar<CF1<C1>, FpVar<CF1<C1>>>,
    DeciderNovaGadget,
>;

/// returns an instance of the DeciderEthCircuit from the given Nova struct
impl<
        C1: Curve,
        C2: Curve,
        FC: FCircuit<C1::ScalarField>,
        CS1: CommitmentScheme<C1, H>,
        // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
        CS2: CommitmentScheme<C2, H, ProverParams = PedersenParams<C2>>,
        const H: bool,
    > TryFrom<Nova<C1, C2, FC, CS1, CS2, H>> for DeciderEthCircuit<C1, C2>
{
    type Error = Error;

    fn try_from(nova: Nova<C1, C2, FC, CS1, CS2, H>) -> Result<Self, Error> {
        let mut transcript = PoseidonSponge::new_with_pp_hash(&nova.poseidon_config, nova.pp_hash);

        // compute the U_{i+1}, W_{i+1}
        let (W_i1, U_i1, cmT, r_bits) = NIFS::<C1, CS1, PoseidonSponge<C1::ScalarField>, H>::prove(
            &nova.cs_pp,
            &nova.r1cs.clone(),
            &mut transcript,
            &nova.W_i,
            &nova.U_i,
            &nova.w_i,
            &nova.u_i,
        )?;
        let r_Fr = C1::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits))
            .ok_or(Error::OutOfBounds)?;

        // compute the KZG challenges used as inputs in the circuit
        let kzg_challenges = KZGChallengesGadget::get_challenges_native(&mut transcript, &U_i1);

        // get KZG evals
        let kzg_evaluations = W_i1
            .get_openings()
            .iter()
            .zip(&kzg_challenges)
            .map(|((v, _), &c)| EvalGadget::evaluate_native(v, c))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Self {
            _avar: PhantomData,
            arith: nova.r1cs,
            cf_arith: nova.cf_r1cs,
            cf_pedersen_params: nova.cf_cs_pp,
            poseidon_config: nova.poseidon_config,
            pp_hash: nova.pp_hash,
            i: nova.i,
            z_0: nova.z_0,
            z_i: nova.z_i,
            U_i: nova.U_i,
            W_i: nova.W_i,
            u_i: nova.u_i,
            w_i: nova.w_i,
            U_i1,
            W_i1,
            proof: cmT,
            randomness: r_Fr,
            cf_U_i: nova.cf_U_i,
            cf_W_i: nova.cf_W_i,
            kzg_challenges,
            kzg_evaluations,
        })
    }
}

pub struct DeciderNovaGadget;

impl<C: Curve>
    DeciderEnabledNIFS<C, CommittedInstance<C>, CommittedInstance<C>, Witness<C>, R1CS<CF1<C>>>
    for DeciderNovaGadget
{
    type ProofDummyCfg = ();
    type Proof = C;
    type RandomnessDummyCfg = ();
    type Randomness = CF1<C>;

    fn fold_field_elements_gadget(
        _arith: &R1CS<CF1<C>>,
        transcript: &mut PoseidonSpongeVar<CF1<C>>,
        U: CommittedInstanceVar<C>,
        U_vec: Vec<FpVar<CF1<C>>>,
        u: CommittedInstanceVar<C>,
        proof: C,
        _randomness: CF1<C>,
    ) -> Result<CommittedInstanceVar<C>, SynthesisError> {
        let cs = U.u.cs();
        let cmT = NonNativeAffineVar::new_input(cs.clone(), || Ok(proof))?;
        let (new_U, _) = NIFSGadget::verify(transcript, U, U_vec, u, Some(cmT))?;
        Ok(new_U)
    }

    fn fold_group_elements_native(
        U_commitments: &[C],
        u_commitments: &[C],
        cmT: Option<Self::Proof>,
        r: Self::Randomness,
    ) -> Result<Vec<C>, Error> {
        let cmT = cmT.ok_or(Error::Empty)?;
        let U_cmW = U_commitments[0];
        let U_cmE = U_commitments[1];
        let u_cmW = u_commitments[0];
        let u_cmE = u_commitments[1];
        if !u_cmE.is_zero() {
            return Err(Error::NotIncomingCommittedInstance);
        }
        let cmW = U_cmW + u_cmW.mul(r);
        let cmE = U_cmE + cmT.mul(r);
        Ok(vec![cmW, cmE])
    }
}

#[cfg(test)]
pub mod tests {
    use ark_pallas::{Fr, Projective};
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    use ark_vesta::Projective as Projective2;

    use super::*;
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::PreprocessorParam;
    use crate::frontend::utils::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_canonical_config;
    use crate::FoldingScheme;

    #[test]
    fn test_decider_circuit() -> Result<(), Error> {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(())?;
        let z_0 = vec![Fr::from(3_u32)];

        type N = Nova<
            Projective,
            Projective2,
            CubicFCircuit<Fr>,
            Pedersen<Projective>,
            Pedersen<Projective2>,
            false,
        >;

        let prep_param = PreprocessorParam::<
            Projective,
            Projective2,
            CubicFCircuit<Fr>,
            Pedersen<Projective>,
            Pedersen<Projective2>,
            false,
        >::new(poseidon_config, F_circuit);
        let nova_params = N::preprocess(&mut rng, &prep_param)?;

        // generate a Nova instance and do a step of it
        let mut nova = N::init(&nova_params, F_circuit, z_0.clone())?;
        nova.prove_step(&mut rng, (), None)?;
        let ivc_proof = nova.ivc_proof();
        N::verify(nova_params.1, ivc_proof)?;

        // load the DeciderEthCircuit from the generated Nova instance
        let decider_circuit = DeciderEthCircuit::<Projective, Projective2>::try_from(nova)?;

        let cs = ConstraintSystem::<Fr>::new_ref();

        // generate the constraints and check that are satisfied by the inputs
        decider_circuit.generate_constraints(cs.clone())?;
        assert!(cs.is_satisfied()?);

        Ok(())
    }
}
