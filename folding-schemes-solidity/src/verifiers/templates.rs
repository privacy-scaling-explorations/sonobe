//! Solidity templates for the verifier contracts.
//! We use askama for templating and define which variables are required for each template.

use crate::utils::encoding::{g1_to_fq_repr, g2_to_fq_repr};
use crate::utils::encoding::{G1Repr, G2Repr};
use crate::{Groth16Data, KzgData, NovaCyclefoldData};
use ark_bn254::{Bn254, G1Affine};
use ark_groth16::VerifyingKey;
use ark_poly_commit::kzg10::VerifierKey;
use askama::Template;
use std::ops::Deref;

// Pragma statements for verifiers
pub(crate) const PRAGMA_GROTH16_VERIFIER: &str = "pragma solidity >=0.7.0 <0.9.0;"; // from snarkjs, avoid changing
pub(crate) const PRAGMA_KZG10_VERIFIER: &str = "pragma solidity >=0.8.1 <=0.8.4;";

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

impl From<(&Groth16Data, &Option<String>)> for Groth16Verifier {
    fn from(value: (&Groth16Data, &Option<String>)) -> Self {
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

impl From<(&KzgData, &Option<String>)> for KZG10Verifier {
    fn from(value: (&KzgData, &Option<String>)) -> Self {
        Self {
            pragma_version: value.1.clone().unwrap_or(PRAGMA_KZG10_VERIFIER.to_string()),
            sdpx: "// SPDX-License-Identifier: GPL-3.0".to_string(),
            g1: g1_to_fq_repr(value.0.vk.g),
            g2: g2_to_fq_repr(value.0.vk.h),
            vk: g2_to_fq_repr(value.0.vk.beta_h),
            g1_crs_len: value.0.g1_crs_batch_points_len,
            g1_crs: value
                .0
                .g1_crs_batch_points
                .clone()
                .unwrap_or_default()
                .iter()
                .map(|g1| g1_to_fq_repr(*g1))
                .collect(),
        }
    }
}

impl KZG10Verifier {
    pub fn new(
        vk: VerifierKey<Bn254>,
        crs: Vec<G1Affine>,
        pragma: Option<String>,
        sdpx: Option<String>,
    ) -> KZG10Verifier {
        let g1_string_repr = g1_to_fq_repr(vk.g);
        let g2_string_repr = g2_to_fq_repr(vk.h);
        let vk_string_repr = g2_to_fq_repr(vk.beta_h);
        let g1_crs_len = crs.len();
        let g1_crs = crs.iter().map(|g1| g1_to_fq_repr(*g1)).collect();

        let pragma_version = pragma.unwrap_or_default();
        KZG10Verifier {
            sdpx: sdpx.unwrap_or_default(),
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
#[template(path = "nova_cyclefold_decider.askama.sol", ext = "sol")]
pub struct NovaCyclefoldDecider {
    pub groth16_verifier: Groth16Verifier,
    pub kzg10_verifier: KZG10Verifier,
}

impl From<(&NovaCyclefoldData, &Option<String>)> for NovaCyclefoldDecider {
    fn from(value: (&NovaCyclefoldData, &Option<String>)) -> Self {
        Self {
            groth16_verifier: Groth16Verifier::from((&value.0.g16_data, value.1)),
            kzg10_verifier: KZG10Verifier::from((&value.0.kzg_data, value.1)),
        }
    }
}

impl NovaCyclefoldDecider {
    fn new(
        vkey_g16: VerifyingKey<Bn254>,
        vkey_kzg: VerifierKey<Bn254>,
        crs_points: Vec<G1Affine>,
        pragma: Option<String>,
    ) -> Self {
        Self {
            groth16_verifier: Groth16Verifier::new(vkey_g16, pragma.clone()),
            kzg10_verifier: KZG10Verifier::new(vkey_kzg, crs_points, pragma, None),
        }
    }
}

impl Deref for NovaCyclefoldDecider {
    type Target = Groth16Verifier;

    fn deref(&self) -> &Self::Target {
        &self.groth16_verifier
    }
}
