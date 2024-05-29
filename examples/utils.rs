#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(clippy::upper_case_acronyms)]
#![allow(dead_code)]
use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as G1};
use ark_crypto_primitives::snark::SNARK;
use ark_groth16::{Groth16, ProvingKey, VerifyingKey as G16VerifierKey};
use ark_grumpkin::{constraints::GVar as GVar2, Projective as G2};
use ark_poly_commit::kzg10::VerifierKey as KZGVerifierKey;
use ark_std::Zero;
use std::time::Instant;

use folding_schemes::{
    commitment::{
        kzg::{ProverKey as KZGProverKey, KZG},
        pedersen::Pedersen,
        CommitmentScheme,
    },
    folding::nova::{
        decider_eth_circuit::DeciderEthCircuit, get_r1cs, Nova, ProverParams, VerifierParams,
    },
    frontend::FCircuit,
    transcript::poseidon::poseidon_canonical_config,
    FoldingScheme,
};

// This method computes the Nova's Prover & Verifier parameters for the example.
// Warning: this method is only for testing purposes. For a real world use case those parameters
// should be generated carefully (both the PoseidonConfig and the PedersenParams).
#[allow(clippy::type_complexity)]
pub(crate) fn init_nova_ivc_params<FC: FCircuit<Fr>>(
    F_circuit: FC,
) -> (
    ProverParams<G1, G2, KZG<'static, Bn254>, Pedersen<G2>>,
    VerifierParams<G1, G2>,
    KZGVerifierKey<Bn254>,
) {
    let mut rng = ark_std::test_rng();
    let poseidon_config = poseidon_canonical_config::<Fr>();

    // get the CM & CF_CM len
    let (r1cs, cf_r1cs) = get_r1cs::<G1, GVar, G2, GVar2, FC>(&poseidon_config, F_circuit).unwrap();
    let cs_len = r1cs.A.n_rows;
    let cf_cs_len = cf_r1cs.A.n_rows;

    // let (pedersen_params, _) = Pedersen::<G1>::setup(&mut rng, cf_len).unwrap();
    let (kzg_pk, kzg_vk): (KZGProverKey<G1>, KZGVerifierKey<Bn254>) =
        KZG::<Bn254>::setup(&mut rng, cs_len).unwrap();
    let (cf_pedersen_params, _) = Pedersen::<G2>::setup(&mut rng, cf_cs_len).unwrap();

    let fs_prover_params = ProverParams::<G1, G2, KZG<Bn254>, Pedersen<G2>> {
        poseidon_config: poseidon_config.clone(),
        cs_params: kzg_pk.clone(),
        cf_cs_params: cf_pedersen_params,
    };
    let fs_verifier_params = VerifierParams::<G1, G2> {
        poseidon_config: poseidon_config.clone(),
        r1cs,
        cf_r1cs,
    };
    (fs_prover_params, fs_verifier_params, kzg_vk)
}

/// Initializes Nova parameters and DeciderEth parameters. Only for test purposes.
#[allow(clippy::type_complexity)]
pub(crate) fn init_ivc_and_decider_params<FC: FCircuit<Fr>>(
    f_circuit: FC,
) -> (
    ProverParams<G1, G2, KZG<'static, Bn254>, Pedersen<G2>>,
    KZGVerifierKey<Bn254>,
    ProvingKey<Bn254>,
    G16VerifierKey<Bn254>,
) {
    let mut rng = rand::rngs::OsRng;
    let start = Instant::now();
    let (fs_prover_params, _, kzg_vk) = init_nova_ivc_params::<FC>(f_circuit.clone());
    println!("generated Nova folding params: {:?}", start.elapsed());

    pub type NOVA<FC> = Nova<G1, GVar, G2, GVar2, FC, KZG<'static, Bn254>, Pedersen<G2>>;
    let z_0 = vec![Fr::zero(); f_circuit.state_len()];
    let nova = NOVA::init(&fs_prover_params, f_circuit, z_0.clone()).unwrap();

    let decider_circuit =
        DeciderEthCircuit::<G1, GVar, G2, GVar2, KZG<Bn254>, Pedersen<G2>>::from_nova::<FC>(
            nova.clone(),
        )
        .unwrap();
    let start = Instant::now();
    let (g16_pk, g16_vk) =
        Groth16::<Bn254>::circuit_specific_setup(decider_circuit.clone(), &mut rng).unwrap();
    println!(
        "generated G16 (Decider circuit) params: {:?}",
        start.elapsed()
    );
    (fs_prover_params, kzg_vk, g16_pk, g16_vk)
}

fn main() {}
