use crate::utils::HeaderInclusion;
use crate::{Groth16Data, KzgData, ProtocolData, PRAGMA_GROTH16_VERIFIER};
use ark_bn254::{Bn254, G1Affine};
use ark_groth16::VerifyingKey;
use ark_poly_commit::kzg10::VerifierKey;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use askama::Template;

use super::g16::Groth16Verifier;
use super::kzg::KZG10Verifier;

#[derive(Template, Default)]
#[template(path = "nova_cyclefold_decider.askama.sol", ext = "sol")]
pub(crate) struct NovaCyclefoldDecider {
    groth16_verifier: Groth16Verifier,
    kzg10_verifier: KZG10Verifier,
}

impl From<NovaCyclefoldData> for NovaCyclefoldDecider {
    fn from(value: NovaCyclefoldData) -> Self {
        Self {
            groth16_verifier: Groth16Verifier::from(value.g16_data),
            kzg10_verifier: KZG10Verifier::from(value.kzg_data),
        }
    }
}

#[derive(CanonicalDeserialize, CanonicalSerialize, PartialEq, Debug)]
pub struct NovaCyclefoldData {
    g16_data: Groth16Data,
    kzg_data: KzgData,
}

impl ProtocolData for NovaCyclefoldData {
    const PROTOCOL_NAME: &'static str = "NovaCyclefold";

    fn render_as_template(self, pragma: Option<String>) -> Vec<u8> {
        HeaderInclusion::<NovaCyclefoldDecider>::builder()
            .pragma_version(pragma.unwrap_or(PRAGMA_GROTH16_VERIFIER.to_string()))
            .template(self)
            .build()
            .render()
            .unwrap()
            .into_bytes()
    }
}

impl From<(Groth16Data, KzgData)> for NovaCyclefoldData {
    fn from(value: (Groth16Data, KzgData)) -> Self {
        Self {
            g16_data: value.0,
            kzg_data: value.1,
        }
    }
}

impl NovaCyclefoldData {
    pub fn new(
        vkey_g16: VerifyingKey<Bn254>,
        vkey_kzg: VerifierKey<Bn254>,
        crs_points: Vec<G1Affine>,
    ) -> Self {
        Self {
            g16_data: Groth16Data::from(vkey_g16),
            // TODO: Remove option from crs points
            kzg_data: KzgData::from((vkey_kzg, Some(crs_points))),
        }
    }
}
