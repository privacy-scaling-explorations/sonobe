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
use ark_ff::PrimeField;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use std::marker::PhantomData;
use std::time::Instant;

use folding_schemes::{
    folding::nova::{decider_eth::prepare_calldata, PreprocessorParam},
    frontend::FCircuit,
    // Note: we could use a Nova & Decider instanciations with custom curves, but since we want to
    // verify it in Ethereum's EVM, we use the prebuilds Nova & Decider.
    prebuilds::eth::{DECIDER, NOVA},
    transcript::poseidon::poseidon_canonical_config,
    Decider,
    Error,
    FoldingScheme,
};
use solidity_verifiers::{
    evm::{compile_solidity, Evm},
    verifiers::nova_cyclefold::{gen_solidity, get_function_selector},
};

/// Test circuit to be folded
#[derive(Clone, Copy, Debug)]
pub struct CubicFCircuit<F: PrimeField> {
    _f: PhantomData<F>,
}
impl<F: PrimeField> FCircuit<F> for CubicFCircuit<F> {
    type Params = ();
    fn new(_params: Self::Params) -> Result<Self, Error> {
        Ok(Self { _f: PhantomData })
    }
    fn state_len(&self) -> usize {
        1
    }
    fn external_inputs_len(&self) -> usize {
        0
    }
    fn step_native(
        &self,
        _i: usize,
        z_i: Vec<F>,
        _external_inputs: Vec<F>,
    ) -> Result<Vec<F>, Error> {
        Ok(vec![z_i[0] * z_i[0] * z_i[0] + z_i[0] + F::from(5_u32)])
    }
    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
        _external_inputs: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let five = FpVar::<F>::new_constant(cs.clone(), F::from(5u32))?;
        let z_i = z_i[0].clone();

        Ok(vec![&z_i * &z_i * &z_i + &z_i + &five])
    }
}

fn main() {
    let n_steps = 10;
    // set the initial state
    let z_0 = vec![Fr::from(3_u32)];

    let f_circuit = CubicFCircuit::<Fr>::new(()).unwrap();

    let poseidon_config = poseidon_canonical_config::<Fr>();
    let mut rng = rand::rngs::OsRng;

    // prepare the Nova prover & verifier params
    let nova_preprocess_params = PreprocessorParam::new(poseidon_config.clone(), f_circuit);
    let nova_params = NOVA::preprocess(&mut rng, &nova_preprocess_params).unwrap();

    // initialize the folding scheme engine, in our case we use Nova
    let mut nova = NOVA::init(nova_params.clone(), f_circuit, z_0).unwrap();

    // prepare the Decider prover & verifier params
    let (decider_pp, decider_vp) =
        DECIDER::preprocess(&mut rng, &nova_params, nova.clone()).unwrap();

    // run n steps of the folding iteration
    for i in 0..n_steps {
        let start = Instant::now();
        nova.prove_step(rng, vec![]).unwrap();
        println!("Nova::prove_step {}: {:?}", i, start.elapsed());
    }

    let start = Instant::now();
    let proof = DECIDER::prove(rng, decider_pp, nova.clone()).unwrap();
    println!("generated Decider proof: {:?}", start.elapsed());

    let verified = DECIDER::<CubicFCircuit<Fr>>::verify(
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
