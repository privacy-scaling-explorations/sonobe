use std::ops::Deref;

use crate::utils::encoding::{g1_to_fq_repr, g2_to_fq_repr};
/// Solidity templates for the verifier contracts.
/// We use askama for templating and define which variables are required for each template.
use crate::utils::encoding::{G1Repr, G2Repr};
use ark_bn254::{Bn254, G1Affine};
use ark_groth16::VerifyingKey;
use ark_poly_commit::kzg10::VerifierKey;
use askama::Template;

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

impl Groth16Verifier {
    pub fn from(value: VerifyingKey<Bn254>, pragma: Option<String>) -> Self {
        let pragma_version = pragma.unwrap_or_default();
        let sdpx = "// SPDX-License-Identifier: GPL-3.0".to_string();
        Self {
            pragma_version,
            sdpx,
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

#[derive(Template, Default)]
#[template(path = "kzg10_verifier.askama.sol", ext = "sol")]
pub struct KZG10Verifier {
    /// SPDX-License-Identifier
    pub sdpx: String,
    /// The `pragma` statement.
    pub pragma_version: String,
    /// The generator of `G1`.
    pub g1: G1Repr,
    /// The generator of `G2`.
    pub g2: G2Repr,
    /// The verification key
    pub vk: G2Repr,
    /// Length of the trusted setup vector.
    pub g1_crs_len: usize,
    /// The trusted setup vector.
    pub g1_crs: Vec<G1Repr>,
}

impl KZG10Verifier {
    pub fn from(
        vk: &VerifierKey<Bn254>,
        crs: &[G1Affine],
        pragma: Option<String>,
        sdpx: Option<String>,
    ) -> KZG10Verifier {
        let g1_string_repr = g1_to_fq_repr(vk.g);
        let g2_string_repr = g2_to_fq_repr(vk.h);
        let vk_string_repr = g2_to_fq_repr(vk.beta_h);
        let g1_crs_len = crs.len();
        let g1_crs = crs.iter().map(|g1| g1_to_fq_repr(*g1)).collect();
        let sdpx = sdpx.unwrap_or_default();
        let pragma_version = pragma.unwrap_or_default();
        KZG10Verifier {
            sdpx,
            pragma_version,
            g1: g1_string_repr,
            g2: g2_string_repr,
            vk: vk_string_repr,
            g1_crs,
            g1_crs_len,
        }
    }
}

#[derive(Template)]
#[template(path = "kzg10_groth16_decider_verifier.askama.sol", ext = "sol")]
pub struct Groth16KZG10DeciderVerifier {
    pub groth16_verifier: Groth16Verifier,
    pub kzg10_verifier: KZG10Verifier,
}

impl Deref for Groth16KZG10DeciderVerifier {
    type Target = Groth16Verifier;

    fn deref(&self) -> &Self::Target {
        &self.groth16_verifier
    }
}
