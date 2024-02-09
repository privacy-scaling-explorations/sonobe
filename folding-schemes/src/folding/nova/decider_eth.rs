/// This file implements the onchain (Ethereum's EVM) decider.
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_r1cs_std::{groups::GroupOpsBounds, prelude::CurveVar};
use ark_snark::SNARK;
use ark_std::rand::CryptoRng;
use ark_std::rand::RngCore;
use core::marker::PhantomData;

pub use super::decider_eth_circuit::DeciderEthCircuit;
use crate::commitment::{pedersen::Params as PedersenParams, CommitmentProver};
use crate::folding::circuits::nonnative::point_to_nonnative_limbs_custom_opt;
use crate::folding::nova::{circuits::CF2, CommittedInstance, Nova};
use crate::frontend::FCircuit;
use crate::Error;
use crate::{Decider as DeciderTrait, FoldingScheme};
use ark_r1cs_std::fields::nonnative::params::OptimizationType;

/// Onchain Decider, for ethereum use cases
#[derive(Clone, Debug)]
pub struct Decider<C1, GC1, C2, GC2, FC, CP1, CP2, S, FS> {
    _c1: PhantomData<C1>,
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,
    _fc: PhantomData<FC>,
    _cp1: PhantomData<CP1>,
    _cp2: PhantomData<CP2>,
    _s: PhantomData<S>,
    _fs: PhantomData<FS>,
}

impl<C1, GC1, C2, GC2, FC, CP1, CP2, S, FS> DeciderTrait<C1, C2, FC, FS>
    for Decider<C1, GC1, C2, GC2, FC, CP1, CP2, S, FS>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    CP1: CommitmentProver<C1>,
    // enforce that the CP2 is Pedersen commitment, since we're at Ethereum's EVM decider
    CP2: CommitmentProver<C2, Params = PedersenParams<C2>>,
    S: SNARK<C1::ScalarField>,
    FS: FoldingScheme<C1, C2, FC>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
    // constrain FS into Nova, since this is a Decider specificly for Nova
    Nova<C1, GC1, C2, GC2, FC, CP1, CP2>: From<FS>,
{
    type ProverParam = S::ProvingKey;
    type Proof = S::Proof;
    type VerifierParam = S::VerifyingKey;
    type PublicInput = Vec<C1::ScalarField>;
    type CommittedInstanceWithWitness = ();
    type CommittedInstance = CommittedInstance<C1>;

    fn prove(
        pp: &Self::ProverParam,
        mut rng: impl RngCore + CryptoRng,
        folding_scheme: FS,
    ) -> Result<Self::Proof, Error> {
        let circuit =
            DeciderEthCircuit::<C1, GC1, C2, GC2, CP1, CP2>::from_nova::<FC>(folding_scheme.into());

        let proof = S::prove(pp, circuit.clone(), &mut rng).unwrap();

        Ok(proof)
    }

    fn verify(
        vp: &Self::VerifierParam,
        i: C1::ScalarField,
        z_0: Vec<C1::ScalarField>,
        z_i: Vec<C1::ScalarField>,
        running_instance: &Self::CommittedInstance,
        proof: Self::Proof,
    ) -> Result<bool, Error> {
        let (cmE_x, cmE_y) = point_to_nonnative_limbs_custom_opt::<C1>(
            running_instance.cmE,
            OptimizationType::Constraints,
        )?;
        let (cmW_x, cmW_y) = point_to_nonnative_limbs_custom_opt::<C1>(
            running_instance.cmW,
            OptimizationType::Constraints,
        )?;
        let public_input: Vec<C1::ScalarField> = vec![
            vec![i],
            z_0,
            z_i,
            vec![running_instance.u],
            running_instance.x.clone(),
            cmE_x,
            cmE_y,
            cmW_x,
            cmW_y,
        ]
        .concat();
        S::verify(vp, &public_input, &proof).map_err(|e| Error::Other(e.to_string()))
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_groth16::Groth16;
    use ark_mnt4_298::{constraints::G1Var as GVar, Fr, G1Projective as Projective, MNT4_298};
    use ark_mnt6_298::{constraints::G1Var as GVar2, G1Projective as Projective2};
    use std::time::Instant;

    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::{get_pedersen_params_len, ProverParams};
    use crate::frontend::tests::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_test_config;

    // Note: since we're testing a big circuit, this test takes a bit more of computation and time,
    // do not run in the normal CI.
    // To run the test use `--ignored` flag, eg. `cargo test -- --ignored`
    #[test]
    #[ignore]
    fn test_decider() {
        type NOVA = Nova<
            Projective,
            GVar,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
            Pedersen<Projective>,
            Pedersen<Projective2>,
        >;
        type DECIDER = Decider<
            Projective,
            GVar,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
            Pedersen<Projective>,
            Pedersen<Projective2>,
            Groth16<MNT4_298>, // here we define the Snark to use in the decider
            NOVA,              // here we define the FoldingScheme to use
        >;

        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(());
        let z_0 = vec![Fr::from(3_u32)];

        let (cm_len, cf_cm_len) =
            get_pedersen_params_len::<Projective, GVar, Projective2, GVar2, CubicFCircuit<Fr>>(
                &poseidon_config,
                F_circuit,
            )
            .unwrap();
        let pedersen_params = Pedersen::<Projective>::new_params(&mut rng, cm_len);
        let cf_pedersen_params = Pedersen::<Projective2>::new_params(&mut rng, cf_cm_len);

        let start = Instant::now();
        let prover_params =
            ProverParams::<Projective, Projective2, Pedersen<Projective>, Pedersen<Projective2>> {
                poseidon_config: poseidon_config.clone(),
                cm_params: pedersen_params,
                cf_cm_params: cf_pedersen_params,
            };
        println!("generating pedersen params, {:?}", start.elapsed());

        // use Nova as FoldingScheme
        let start = Instant::now();
        let mut nova = NOVA::init(&prover_params, F_circuit, z_0.clone()).unwrap();
        println!("Nova initialized, {:?}", start.elapsed());
        let start = Instant::now();
        nova.prove_step().unwrap();
        println!("prove_step, {:?}", start.elapsed());

        // generate Groth16 setup
        let circuit = DeciderEthCircuit::<
            Projective,
            GVar,
            Projective2,
            GVar2,
            Pedersen<Projective>,
            Pedersen<Projective2>,
        >::from_nova::<CubicFCircuit<Fr>>(nova.clone());
        let mut rng = rand::rngs::OsRng;

        let start = Instant::now();
        let (pk, vk) =
            Groth16::<MNT4_298>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
        println!("Groth16 setup, {:?}", start.elapsed());

        // decider proof generation
        let start = Instant::now();
        let proof = DECIDER::prove(&pk, rng, nova.clone()).unwrap();
        println!("Decider Groth16 prove, {:?}", start.elapsed());

        // decider proof verification
        let verified = DECIDER::verify(&vk, nova.i, nova.z_0, nova.z_i, &nova.U_i, proof).unwrap();
        assert!(verified);
    }
}
