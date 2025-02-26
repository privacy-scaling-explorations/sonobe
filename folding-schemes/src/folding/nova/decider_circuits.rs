/// This file implements the offchain decider circuit. For ethereum use cases, use the
/// DeciderEthCircuit.
/// More details can be found at the documentation page:
/// https://privacy-scaling-explorations.github.io/sonobe-docs/design/nova-decider-offchain.html
use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::fields::fp::FpVar;
use core::marker::PhantomData;

use super::{
    decider_eth_circuit::DeciderNovaGadget,
    nifs::{nova::NIFS, NIFSTrait},
    CommittedInstance, Nova, Witness,
};
use crate::{
    arith::r1cs::{circuits::R1CSMatricesVar, R1CS},
    commitment::CommitmentScheme,
    folding::{
        circuits::{
            decider::{
                off_chain::{GenericOffchainDeciderCircuit1, GenericOffchainDeciderCircuit2},
                EvalGadget, KZGChallengesGadget,
            },
            CF1,
        },
        traits::WitnessOps,
    },
    frontend::FCircuit,
    transcript::{poseidon::poseidon_canonical_config, Transcript},
    Curve, Error,
};

/// Circuit that implements part of the in-circuit checks needed for the offchain verification over
/// the Curve2's BaseField (=Curve1's ScalarField).

pub type DeciderCircuit1<C1, C2> = GenericOffchainDeciderCircuit1<
    C1,
    C2,
    CommittedInstance<C1>,
    CommittedInstance<C1>,
    Witness<C1>,
    R1CS<CF1<C1>>,
    R1CSMatricesVar<CF1<C1>, FpVar<CF1<C1>>>,
    DeciderNovaGadget,
>;

impl<
        C1: Curve,
        C2: Curve,
        FC: FCircuit<C1::ScalarField>,
        CS1: CommitmentScheme<C1, H>,
        CS2: CommitmentScheme<C2, H>,
        const H: bool,
    > TryFrom<Nova<C1, C2, FC, CS1, CS2, H>> for DeciderCircuit1<C1, C2>
{
    type Error = Error;

    fn try_from(nova: Nova<C1, C2, FC, CS1, CS2, H>) -> Result<Self, Error> {
        let mut transcript = PoseidonSponge::new_with_pp_hash(&nova.poseidon_config, nova.pp_hash);
        // pp_hash is absorbed to transcript at the NIFS::prove call

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
            kzg_challenges,
            kzg_evaluations,
        })
    }
}

/// Circuit that implements part of the in-circuit checks needed for the offchain verification over
/// the Curve1's BaseField (=Curve2's ScalarField).
pub type DeciderCircuit2<C2> = GenericOffchainDeciderCircuit2<C2>;

impl<
        C1: Curve,
        C2: Curve,
        FC: FCircuit<C1::ScalarField>,
        CS1: CommitmentScheme<C1, H>,
        CS2: CommitmentScheme<C2, H>,
        const H: bool,
    > TryFrom<Nova<C1, C2, FC, CS1, CS2, H>> for DeciderCircuit2<C2>
{
    type Error = Error;

    fn try_from(nova: Nova<C1, C2, FC, CS1, CS2, H>) -> Result<Self, Error> {
        // compute the Commitment Scheme challenges of the CycleFold instance commitments, used as
        // inputs in the circuit
        let poseidon_config = poseidon_canonical_config::<C2::ScalarField>();
        let pp_hash_Fq =
            C2::ScalarField::from_le_bytes_mod_order(&nova.pp_hash.into_bigint().to_bytes_le());
        let mut transcript =
            PoseidonSponge::<C2::ScalarField>::new_with_pp_hash(&poseidon_config, pp_hash_Fq);

        // compute the KZG challenges used as inputs in the circuit
        let kzg_challenges =
            KZGChallengesGadget::get_challenges_native(&mut transcript, &nova.cf_U_i);

        // get KZG evals
        let kzg_evaluations = nova
            .cf_W_i
            .get_openings()
            .iter()
            .zip(&kzg_challenges)
            .map(|((v, _), &c)| EvalGadget::evaluate_native(v, c))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Self {
            cf_arith: nova.cf_r1cs,
            poseidon_config,
            pp_hash: pp_hash_Fq,
            cf_U_i: nova.cf_U_i,
            cf_W_i: nova.cf_W_i,
            kzg_challenges,
            kzg_evaluations,
        })
    }
}

#[cfg(test)]
pub mod tests {
    use ark_pallas::{Fq, Fr, Projective};
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    use ark_vesta::Projective as Projective2;

    use super::*;
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::PreprocessorParam;
    use crate::frontend::utils::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_canonical_config;
    use crate::FoldingScheme;

    #[test]
    fn test_decider_circuits() -> Result<(), Error> {
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
        // verify the IVC
        let ivc_proof = nova.ivc_proof();
        N::verify(nova_params.1, ivc_proof)?;

        // load the DeciderCircuit 1 & 2 from the Nova instance
        let decider_circuit1 = DeciderCircuit1::<Projective, Projective2>::try_from(nova.clone())?;
        let decider_circuit2 = DeciderCircuit2::<Projective2>::try_from(nova)?;

        // generate the constraints of both circuits and check that are satisfied by the inputs
        let cs1 = ConstraintSystem::<Fr>::new_ref();
        decider_circuit1.generate_constraints(cs1.clone())?;
        assert!(cs1.is_satisfied()?);
        let cs2 = ConstraintSystem::<Fq>::new_ref();
        decider_circuit2.generate_constraints(cs2.clone())?;
        assert!(cs2.is_satisfied()?);
        Ok(())
    }
}
