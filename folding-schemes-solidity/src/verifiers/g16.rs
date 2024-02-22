use crate::utils::encoding::{g1_to_fq_repr, g2_to_fq_repr};
use crate::utils::encoding::{G1Repr, G2Repr};
use crate::ProtocolData;
use ark_bn254::Bn254;
use ark_groth16::VerifyingKey;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use askama::Template;

use super::PRAGMA_GROTH16_VERIFIER;

#[derive(Template, Default)]
#[template(path = "groth16_verifier.askama.sol", ext = "sol")]
pub struct Groth16Verifier {
    /// SPDX-License-Identifier
    pub sdpx: String,
    /// The `pragma` statement.
    pub pragma_version: String,
    /// The `alpha * G`, where `G` is the generator of `G1`.
    pub vkey_alpha_g1: G1Repr,
    /// The `alpha * H`, where `H` is the generator of `G2`.
    pub vkey_beta_g2: G2Repr,
    /// The `gamma * H`, where `H` is the generator of `G2`.
    pub vkey_gamma_g2: G2Repr,
    /// The `delta * H`, where `H` is the generator of `G2`.
    pub vkey_delta_g2: G2Repr,
    /// Length of the `gamma_abc_g1` vector.
    pub gamma_abc_len: usize,
    /// The `gamma^{-1} * (beta * a_i + alpha * b_i + c_i) * H`, where `H` is the generator of `E::G1`.
    pub gamma_abc_g1: Vec<G1Repr>,
}

impl From<(Groth16Data, &Option<String>)> for Groth16Verifier {
    fn from(value: (Groth16Data, &Option<String>)) -> Self {
        Self {
            pragma_version: value
                .1
                .clone()
                .unwrap_or(PRAGMA_GROTH16_VERIFIER.to_string()),
            sdpx: "// SPDX-License-Identifier: GPL-3.0".to_string(),
            vkey_alpha_g1: g1_to_fq_repr(value.0 .0.alpha_g1),
            vkey_beta_g2: g2_to_fq_repr(value.0 .0.beta_g2),
            vkey_gamma_g2: g2_to_fq_repr(value.0 .0.gamma_g2),
            vkey_delta_g2: g2_to_fq_repr(value.0 .0.delta_g2),
            gamma_abc_len: value.0 .0.gamma_abc_g1.len(),
            gamma_abc_g1: value
                .0
                 .0
                .gamma_abc_g1
                .iter()
                .copied()
                .map(g1_to_fq_repr)
                .collect(),
        }
    }
}

impl Groth16Verifier {
    pub fn new(value: VerifyingKey<Bn254>, pragma: Option<String>) -> Self {
        let pragma_version = pragma.unwrap_or_else(|| PRAGMA_GROTH16_VERIFIER.to_string());
        Self {
            pragma_version,
            sdpx: "// SPDX-License-Identifier: GPL-3.0".to_string(),
            vkey_alpha_g1: g1_to_fq_repr(value.alpha_g1),
            vkey_beta_g2: g2_to_fq_repr(value.beta_g2),
            vkey_gamma_g2: g2_to_fq_repr(value.gamma_g2),
            vkey_delta_g2: g2_to_fq_repr(value.delta_g2),
            gamma_abc_len: value.gamma_abc_g1.len(),
            gamma_abc_g1: value
                .gamma_abc_g1
                .iter()
                .copied()
                .map(g1_to_fq_repr)
                .collect(),
        }
    }
}

// Ideally I would like to link this to the `Decider` trait in FoldingSchemes.
// For now, this is the easiest as NovaCyclefold isn't clear target from where we can get all it's needed arguments.
#[derive(CanonicalDeserialize, CanonicalSerialize, Clone, PartialEq, Debug)]
pub struct Groth16Data(VerifyingKey<Bn254>);

impl From<VerifyingKey<Bn254>> for Groth16Data {
    fn from(value: VerifyingKey<Bn254>) -> Self {
        Self(value)
    }
}

impl ProtocolData for Groth16Data {
    const PROTOCOL_NAME: &'static str = "Groth16";

    fn render_as_template(self, pragma: &Option<String>) -> Vec<u8> {
        Groth16Verifier::from((self, pragma))
            .render()
            .unwrap()
            .into_bytes()
    }
}
