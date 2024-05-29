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
use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as G1};

use ark_groth16::Groth16;
use ark_grumpkin::{constraints::GVar as GVar2, Projective as G2};

use std::{path::PathBuf, rc::Rc};
use std::time::Instant;

use folding_schemes::{
    commitment::{kzg::KZG, pedersen::Pedersen},
    folding::nova::{
        decider_eth::{prepare_calldata, Decider as DeciderEth},
        Nova,
    },
    frontend::{circom::CircomFCircuit, FCircuit},
    Decider, FoldingScheme,
};
use solidity_verifiers::{
    evm::{compile_solidity, Evm},
    utils::get_function_selector_for_nova_cyclefold_verifier,
    verifiers::nova_cyclefold::get_decider_template_for_cyclefold_decider,
    NovaCycleFoldVerifierKey,
};

mod utils;
use utils::init_ivc_and_decider_params;

fn main() {
    // set the initial state
    let z_0 = vec![Fr::from(3_u32)];

    // set the external inputs to be used at each step of the IVC, it has length of 10 since this
    // is the number of steps that we will do
    let external_inputs = vec![
        vec![Fr::from(6u32), Fr::from(7u32)],
        vec![Fr::from(8u32), Fr::from(9u32)],
        vec![Fr::from(10u32), Fr::from(11u32)],
        vec![Fr::from(12u32), Fr::from(13u32)],
        vec![Fr::from(14u32), Fr::from(15u32)],
        vec![Fr::from(6u32), Fr::from(7u32)],
        vec![Fr::from(8u32), Fr::from(9u32)],
        vec![Fr::from(10u32), Fr::from(11u32)],
        vec![Fr::from(12u32), Fr::from(13u32)],
        vec![Fr::from(14u32), Fr::from(15u32)],
    ];

    // initialize the Circom circuit
    let r1cs_path =
        PathBuf::from("./folding-schemes/src/frontend/circom/test_folder/external_inputs.r1cs");
    let wasm_path = PathBuf::from(
        "./folding-schemes/src/frontend/circom/test_folder/external_inputs_js/external_inputs.wasm",
    );

    let f_circuit_params = (r1cs_path, wasm_path, 1, 2);
    let mut f_circuit = CircomFCircuit::<Fr>::new(f_circuit_params).unwrap();

    f_circuit.set_custom_step_native(Rc::new(|_i, z_i, external_i| {
        Ok(vec![z_i[0] * z_i[0] * z_i[0] + z_i[0] * external_i[0] + external_i[1]])
    }));

    let (fs_prover_params, kzg_vk, g16_pk, g16_vk) =
        init_ivc_and_decider_params::<CircomFCircuit<Fr>>(f_circuit.clone());

    pub type NOVA =
        Nova<G1, GVar, G2, GVar2, CircomFCircuit<Fr>, KZG<'static, Bn254>, Pedersen<G2>>;
    pub type DECIDERETH_FCircuit = DeciderEth<
        G1,
        GVar,
        G2,
        GVar2,
        CircomFCircuit<Fr>,
        KZG<'static, Bn254>,
        Pedersen<G2>,
        Groth16<Bn254>,
        NOVA,
    >;

    // initialize the folding scheme engine, in our case we use Nova
    let mut nova = NOVA::init(&fs_prover_params, f_circuit.clone(), z_0).unwrap();
    // run n steps of the folding iteration
    for (i, external_inputs_at_step) in external_inputs.iter().enumerate() {
        let start = Instant::now();
        nova.prove_step(external_inputs_at_step.clone()).unwrap();
        println!("Nova::prove_step {}: {:?}", i, start.elapsed());
    }

    let rng = rand::rngs::OsRng;
    let start = Instant::now();
    let proof = DECIDERETH_FCircuit::prove(
        (g16_pk, fs_prover_params.cs_params.clone()),
        rng,
        nova.clone(),
    )
    .unwrap();
    println!("generated Decider proof: {:?}", start.elapsed());

    let verified = DECIDERETH_FCircuit::verify(
        (g16_vk.clone(), kzg_vk.clone()),
        nova.i,
        nova.z_0.clone(),
        nova.z_i.clone(),
        &nova.U_i,
        &nova.u_i,
        &proof,
    )
    .unwrap();
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
    )
    .unwrap();

    // prepare the setup params for the solidity verifier
    let nova_cyclefold_vk = NovaCycleFoldVerifierKey::from((g16_vk, kzg_vk, f_circuit.state_len()));

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
    )
    .unwrap();
    fs::write("./examples/solidity-calldata.calldata", calldata.clone()).unwrap();
    let s = solidity_verifiers::utils::get_formatted_calldata(calldata.clone());
    fs::write("./examples/solidity-calldata.inputs", s.join(",\n")).expect("");
}
