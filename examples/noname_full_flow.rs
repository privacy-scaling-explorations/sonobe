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
use ark_bn254::Fr;
use noname::backends::r1cs::R1csBn254Field;

use folding_schemes::{
    folding::nova::{decider_eth::prepare_calldata, PreprocessorParam},
    frontend::{noname::NonameFCircuit, FCircuit},
    prebuilds::eth::{DECIDER, NOVA},
    transcript::poseidon::poseidon_canonical_config,
    Decider, FoldingScheme,
};
use std::time::Instant;

use solidity_verifiers::{
    evm::{compile_solidity, Evm},
    verifiers::nova_cyclefold::{gen_solidity, get_function_selector},
};

fn main() {
    const NONAME_CIRCUIT_EXTERNAL_INPUTS: &str =
        "fn main(pub ivc_inputs: [Field; 2], external_inputs: [Field; 2]) -> [Field; 2] {
    let xx = external_inputs[0] + ivc_inputs[0];
    let yy = external_inputs[1] * ivc_inputs[1];
    assert_eq(yy, xx);
    return [xx, yy];
}";

    // set the initial state
    let z_0 = vec![Fr::from(2), Fr::from(5)];

    // set the external inputs to be used at each step of the IVC, it has length of 10 since this
    // is the number of steps that we will do
    let external_inputs = vec![
        vec![Fr::from(8u32), Fr::from(2u32)],
        vec![Fr::from(40), Fr::from(5)],
    ];

    // initialize the noname circuit
    let f_circuit_params = (NONAME_CIRCUIT_EXTERNAL_INPUTS.to_owned(), 2, 2);
    let f_circuit = NonameFCircuit::<Fr, R1csBn254Field>::new(f_circuit_params).unwrap();

    let poseidon_config = poseidon_canonical_config::<Fr>();
    let mut rng = rand::rngs::OsRng;

    // prepare the Nova prover & verifier params
    let nova_preprocess_params = PreprocessorParam::new(poseidon_config, f_circuit.clone());
    let nova_params = NOVA::preprocess(&mut rng, &nova_preprocess_params).unwrap();

    // initialize the folding scheme engine, in our case we use Nova
    let mut nova = NOVA::init(nova_params.clone(), f_circuit.clone(), z_0).unwrap();

    // prepare the Decider prover & verifier params
    let (decider_pp, decider_vp) =
        DECIDER::preprocess(&mut rng, &nova_params, nova.clone()).unwrap();

    // run n steps of the folding iteration
    for (i, external_inputs_at_step) in external_inputs.iter().enumerate() {
        let start = Instant::now();
        nova.prove_step(rng, external_inputs_at_step.clone())
            .unwrap();
        println!("Nova::prove_step {}: {:?}", i, start.elapsed());
    }

    let start = Instant::now();
    let proof = DECIDER::prove(rng, decider_pp, nova.clone()).unwrap();
    println!("generated Decider proof: {:?}", start.elapsed());

    let verified = DECIDER::<NonameFCircuit<Fr, R1csBn254Field>>::verify(
        decider_vp.clone(),
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
    let function_selector = get_function_selector(nova.z_0.len() * 2 + 1);

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

    // generate the solidity code
    let decider_solidity_code = gen_solidity(decider_vp, f_circuit.state_len());

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
