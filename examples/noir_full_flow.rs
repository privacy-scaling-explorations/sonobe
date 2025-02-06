#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(clippy::upper_case_acronyms)]
///
/// This example performs the full flow:
/// - define the circuit to be folded
/// - fold the circuit with Nova+CycleFold's IVC
/// - generate a DeciderEthCircuit final proof
/// - generate the Solidity contract that verifies the proof
/// - verify the proof in the EVM
///
use ark_bn254::{Bn254, Fr, G1Projective as G1};

use ark_groth16::Groth16;
use ark_grumpkin::Projective as G2;

use experimental_frontends::{noir::NoirFCircuit, utils::VecF};
use folding_schemes::{
    commitment::{kzg::KZG, pedersen::Pedersen},
    folding::{
        nova::{
            decider_eth::{prepare_calldata, Decider as DeciderEth},
            Nova, PreprocessorParam,
        },
        traits::CommittedInstanceOps,
    },
    frontend::FCircuit,
    transcript::poseidon::poseidon_canonical_config,
    Decider, Error, FoldingScheme,
};
use std::{path::Path, time::Instant};

use solidity_verifiers::{
    evm::{compile_solidity, Evm},
    utils::get_function_selector_for_nova_cyclefold_verifier,
    verifiers::nova_cyclefold::get_decider_template_for_cyclefold_decider,
    NovaCycleFoldVerifierKey,
};

fn main() -> Result<(), Error> {
    // set the initial state
    let z_0 = vec![Fr::from(1)];

    // initialize the noir fcircuit
    const EXT_INP_LEN: usize = 0;
    let f_circuit = NoirFCircuit::<Fr, EXT_INP_LEN>::new((
        Path::new("./experimental-frontends/src/noir/test_folder/test_mimc/target/test_mimc.json")
            .into(),
        1,
    ))?;

    pub type N = Nova<G1, G2, NoirFCircuit<Fr, EXT_INP_LEN>, KZG<'static, Bn254>, Pedersen<G2>>;
    pub type D = DeciderEth<
        G1,
        G2,
        NoirFCircuit<Fr, EXT_INP_LEN>,
        KZG<'static, Bn254>,
        Pedersen<G2>,
        Groth16<Bn254>,
        N,
    >;

    let poseidon_config = poseidon_canonical_config::<Fr>();
    let mut rng = ark_std::rand::rngs::OsRng;

    // prepare the Nova prover & verifier params
    let nova_preprocess_params = PreprocessorParam::new(poseidon_config, f_circuit.clone());
    let nova_params = N::preprocess(&mut rng, &nova_preprocess_params)?;

    // prepare the Decider prover & verifier params
    let (decider_pp, decider_vp) =
        D::preprocess(&mut rng, (nova_params.clone(), f_circuit.state_len()))?;

    // initialize the folding scheme engine, in our case we use Nova
    let mut nova = N::init(&nova_params, f_circuit.clone(), z_0)?;

    // run n steps of the folding iteration
    for i in 0..5 {
        let start = Instant::now();
        nova.prove_step(rng, VecF(vec![]), None)?;
        println!("Nova::prove_step {}: {:?}", i, start.elapsed());
    }
    // verify the last IVC proof
    let ivc_proof = nova.ivc_proof();
    N::verify(
        nova_params.1, // Nova's verifier params
        ivc_proof,
    )?;

    let start = Instant::now();
    let proof = D::prove(rng, decider_pp, nova.clone())?;
    println!("generated Decider proof: {:?}", start.elapsed());

    let verified = D::verify(
        decider_vp.clone(),
        nova.i,
        nova.z_0.clone(),
        nova.z_i.clone(),
        &nova.U_i.get_commitments(),
        &nova.u_i.get_commitments(),
        &proof,
    )?;
    assert!(verified);
    println!("Decider proof verification: {}", verified);

    // Now, let's generate the Solidity code that verifies this Decider final proof
    let function_selector =
        get_function_selector_for_nova_cyclefold_verifier(nova.z_0.len() * 2 + 1);

    let calldata: Vec<u8> = prepare_calldata(
        function_selector,
        nova.i,
        nova.z_0,
        nova.z_i,
        &nova.U_i,
        &nova.u_i,
        proof,
    )?;

    // prepare the setup params for the solidity verifier
    let nova_cyclefold_vk = NovaCycleFoldVerifierKey::from((decider_vp, f_circuit.state_len()));

    // generate the solidity code
    let decider_solidity_code = get_decider_template_for_cyclefold_decider(nova_cyclefold_vk);

    // verify the proof against the solidity code in the EVM
    let nova_cyclefold_verifier_bytecode = compile_solidity(&decider_solidity_code, "NovaDecider");
    let mut evm = Evm::default();
    let verifier_address = evm.create(nova_cyclefold_verifier_bytecode);
    let (_, output) = evm.call(verifier_address, calldata.clone());
    assert_eq!(*output.last().unwrap(), 1);

    // save smart contract and the calldata
    println!("storing nova-verifier.sol and the calldata into files");
    use std::fs;
    fs::write(
        "./examples/nova-verifier.sol",
        decider_solidity_code.clone(),
    )?;
    fs::write("./examples/solidity-calldata.calldata", calldata.clone())?;
    let s = solidity_verifiers::utils::get_formatted_calldata(calldata.clone());
    fs::write("./examples/solidity-calldata.inputs", s.join(",\n")).expect("");
    Ok(())
}
