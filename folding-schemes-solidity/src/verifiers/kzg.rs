use crate::utils::encoding::{g1_to_fq_repr, g2_to_fq_repr};
use crate::utils::encoding::{G1Repr, G2Repr};
use crate::utils::HeaderInclusion;
use crate::{ProtocolData, GPL3_SDPX_IDENTIFIER};
use ark_bn254::{Bn254, G1Affine};
use ark_poly_commit::kzg10::VerifierKey;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use askama::Template;

use super::PRAGMA_KZG10_VERIFIER;

#[derive(Template, Default)]
#[template(path = "kzg10_verifier.askama.sol", ext = "sol")]
pub(crate) struct KZG10Verifier {
    /// The generator of `G1`.
    pub(crate) g1: G1Repr,
    /// The generator of `G2`.
    pub(crate) g2: G2Repr,
    /// The verification key
    pub(crate) vk: G2Repr,
    /// Length of the trusted setup vector.
    pub(crate) g1_crs_len: usize,
    /// The trusted setup vector.
    pub(crate) g1_crs: Vec<G1Repr>,
}

impl From<KzgData> for KZG10Verifier {
    fn from(data: KzgData) -> Self {
        let g1_crs_batch_points = data.g1_crs_batch_points.unwrap_or_default();

        Self {
            g1: g1_to_fq_repr(data.vk.g),
            g2: g2_to_fq_repr(data.vk.h),
            vk: g2_to_fq_repr(data.vk.beta_h),
            g1_crs_len: g1_crs_batch_points.len(),
            g1_crs: g1_crs_batch_points
                .iter()
                .map(|g1| g1_to_fq_repr(*g1))
                .collect(),
        }
    }
}

impl KZG10Verifier {
    #[cfg(test)]
    pub(crate) fn new(vk: VerifierKey<Bn254>, crs: Vec<G1Affine>) -> KZG10Verifier {
        let g1_string_repr = g1_to_fq_repr(vk.g);
        let g2_string_repr = g2_to_fq_repr(vk.h);
        let vk_string_repr = g2_to_fq_repr(vk.beta_h);
        let g1_crs_len = crs.len();
        let g1_crs = crs.iter().map(|g1| g1_to_fq_repr(*g1)).collect();

        KZG10Verifier {
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
    pub(crate) vk: VerifierKey<Bn254>,
    pub(crate) g1_crs_batch_points: Option<Vec<G1Affine>>,
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

    fn render_as_template(self, pragma: Option<String>) -> Vec<u8> {
        HeaderInclusion::<KZG10Verifier>::builder()
            .sdpx(GPL3_SDPX_IDENTIFIER.to_string())
            .pragma_version(pragma.unwrap_or(PRAGMA_KZG10_VERIFIER.to_string()))
            .template(self)
            .build()
            .render()
            .unwrap()
            .into_bytes()
    }
}
