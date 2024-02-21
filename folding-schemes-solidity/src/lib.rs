pub use evm::*;
pub use verifiers::templates::*;
mod evm;
mod utils;
mod verifiers;

pub use verifiers::templates::{Groth16Verifier, KZG10Verifier, NovaCyclefoldDecider};
pub use verifiers::{Groth16Data, KzgData, NovaCyclefoldData, ProtocolData};
