use crate::utils::eth::ToEth;
use ark_bn254::Bn254;
use ark_groth16::Groth16;
use crypto::digest::Digest;
use crypto::sha3::Sha3;
use folding_schemes::commitment::kzg::KZG;
use folding_schemes::folding::nova::decider_eth::Proof;
use folding_schemes::folding::nova::CommittedInstance;
use folding_schemes::Error;
use num_bigint::BigUint;

/// Specifies which API to use for a proof verification in a contract.
#[derive(Copy, Clone, Debug, Default)]
pub enum NovaVerificationMode {
    /// Use the `verifyNovaProof` function.
    #[default]
    Explicit,
    /// Use the `verifyOpaqueNovaProof` function.
    Opaque,
    /// Use the `verifyOpaqueNovaProofWithInputs` function.
    OpaqueWithInputs,
}

/// Formats call data from a vec of bytes to a hashmap
/// Useful for debugging directly on the EVM
/// !! Should follow the contract's function signature, we assume the order of arguments is correct
pub fn get_formatted_calldata(calldata: Vec<u8>) -> Vec<String> {
    let mut formatted_calldata = vec![];
    for i in (4..calldata.len()).step_by(32) {
        let val = BigUint::from_bytes_be(&calldata[i..i + 32]);
        formatted_calldata.push(format!("{}", val));
    }
    formatted_calldata
}

/// Prepares solidity calldata for calling the NovaDecider contract
pub fn prepare_calldata_for_nova_cyclefold_verifier(
    verification_mode: NovaVerificationMode,
    i: ark_bn254::Fr,
    z_0: Vec<ark_bn254::Fr>,
    z_i: Vec<ark_bn254::Fr>,
    running_instance: &CommittedInstance<ark_bn254::G1Projective>,
    incoming_instance: &CommittedInstance<ark_bn254::G1Projective>,
    proof: &Proof<ark_bn254::G1Projective, KZG<Bn254>, Groth16<Bn254>>,
) -> Result<Vec<u8>, Error> {
    let selector = get_function_selector(verification_mode, z_0.len());

    Ok([
        selector.to_eth(),
        i.to_eth(),   // i
        z_0.to_eth(), // z_0
        z_i.to_eth(), // z_i
        running_instance.cmW.to_eth(),
        running_instance.cmE.to_eth(),
        incoming_instance.cmW.to_eth(),
        proof.cmT().to_eth(),                 // cmT
        proof.r().to_eth(),                   // r
        proof.snark_proof().to_eth(),         // pA, pB, pC
        proof.kzg_challenges().to_eth(),      // challenge_W, challenge_E
        proof.kzg_proofs()[0].eval.to_eth(),  // eval W
        proof.kzg_proofs()[1].eval.to_eth(),  // eval E
        proof.kzg_proofs()[0].proof.to_eth(), // W kzg_proof
        proof.kzg_proofs()[1].proof.to_eth(), // E kzg_proof
    ]
    .concat())
}

/// Computes the function selector for the nova cyclefold verifier.
/// It is computed on the fly since it depends on the IVC state length.
fn get_function_selector(mode: NovaVerificationMode, state_len: usize) -> [u8; 4] {
    let fn_sig = match mode {
        NovaVerificationMode::Explicit =>
            format!(
                "verifyNovaProof(uint256[{}],uint256[4],uint256[2],uint256[3],uint256[2],uint256[2][2],uint256[2],uint256[4],uint256[2][2])",
                state_len * 2 + 1
            ),
        NovaVerificationMode::Opaque =>
            format!("verifyOpaqueNovaProof(uint256[{}])", 26 + 2 * state_len),
        NovaVerificationMode::OpaqueWithInputs =>
            format!("verifyOpaqueNovaProofWithInputs(uint256,uint256[{state_len}],uint256[{state_len}],uint256[25])"),
    };

    let mut hasher = Sha3::keccak256();
    hasher.input_str(&fn_sig);
    let hash = &mut [0u8; 32];
    hasher.result(hash);
    [hash[0], hash[1], hash[2], hash[3]]
}
