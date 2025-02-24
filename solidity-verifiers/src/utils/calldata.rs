/// Specifies which API to use for a proof verification in a contract.
pub enum NovaVerificationMode {
    /// Use the `verifyNovaProof` function.
    Explicit,
    /// Use the `verifyOpaqueNovaProof` function.
    Opaque,
    /// Use the `verifyOpaqueNovaProofWithInputs` function.
    OpaqueWithInputs,
}
