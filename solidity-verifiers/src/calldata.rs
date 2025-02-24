use crypto::digest::Digest;
use crypto::sha3::Sha3;
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

impl NovaVerificationMode {
    fn function_name(&self) -> &'static str {
        match self {
            NovaVerificationMode::Explicit => "verifyNovaProof",
            NovaVerificationMode::Opaque => "verifyOpaqueNovaProof",
            NovaVerificationMode::OpaqueWithInputs => "verifyOpaqueNovaProofWithInputs",
        }
    }
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

/// Computes the function selector for the nova cyclefold verifier.
/// It is computed on the fly since it depends on the IVC state length.
pub fn get_function_selector_for_nova_cyclefold_verifier(
    mode: NovaVerificationMode,
    state_len: usize,
) -> [u8; 4] {
    let fn_sig = format!(
        "{}(uint256[{}],uint256[4],uint256[2],uint256[3],uint256[2],uint256[2][2],uint256[2],uint256[4],uint256[2][2])",
        mode.function_name(),
        state_len * 2 + 1);

    let mut hasher = Sha3::keccak256();
    hasher.input_str(&fn_sig);
    let hash = &mut [0u8; 32];
    hasher.result(hash);
    [hash[0], hash[1], hash[2], hash[3]]
}
