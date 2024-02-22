use crate::utils::encoding::{g1_to_fq_repr, g2_to_fq_repr};
use crate::utils::encoding::{G1Repr, G2Repr};
use crate::ProtocolData;
use ark_bn254::{Bn254, G1Affine};
use ark_poly_commit::kzg10::VerifierKey;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use askama::Template;

use super::PRAGMA_KZG10_VERIFIER;

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

impl From<(KzgData, &Option<String>)> for KZG10Verifier {
    fn from(value: (KzgData, &Option<String>)) -> Self {
        let g1_crs_batch_points = value.0.g1_crs_batch_points.unwrap_or_default();

        Self {
            pragma_version: value.1.clone().unwrap_or(PRAGMA_KZG10_VERIFIER.to_string()),
            sdpx: "// SPDX-License-Identifier: GPL-3.0".to_string(),
            g1: g1_to_fq_repr(value.0.vk.g),
            g2: g2_to_fq_repr(value.0.vk.h),
            vk: g2_to_fq_repr(value.0.vk.beta_h),
            g1_crs_len: g1_crs_batch_points.len(),
            g1_crs: g1_crs_batch_points
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

#[derive(CanonicalDeserialize, CanonicalSerialize, Clone, PartialEq, Debug)]
pub struct KzgData {
    vk: VerifierKey<Bn254>,
    g1_crs_batch_points: Option<Vec<G1Affine>>,
}

impl From<(VerifierKey<Bn254>, Option<Vec<G1Affine>>)> for KzgData {
    fn from(value: (VerifierKey<Bn254>, Option<Vec<G1Affine>>)) -> Self {
        Self {
            vk: value.0,
            g1_crs_batch_points: value.1,
        }
    }
}

impl ProtocolData for KzgData {
    const PROTOCOL_NAME: &'static str = "KZG";

    fn render_as_template(self, pragma: &Option<String>) -> Vec<u8> {
        KZG10Verifier::from((self, pragma))
            .render()
            .unwrap()
            .into_bytes()
    }
}
