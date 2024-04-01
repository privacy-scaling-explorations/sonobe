use crate::utils::HeaderInclusion;
use crate::{Groth16Data, KzgData, ProtocolData, PRAGMA_GROTH16_VERIFIER};
use ark_bn254::{Bn254, G1Affine};
use ark_groth16::VerifyingKey;
use ark_poly_commit::kzg10::VerifierKey;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use askama::Template;

use super::g16::Groth16Verifier;
use super::kzg::KZG10Verifier;

pub fn get_decider_template_for_cyclefold_decider(
    nova_cyclefold_data: NovaCyclefoldData,
) -> String {
    let decider_template = HeaderInclusion::<NovaCyclefoldDecider>::builder()
        .template(nova_cyclefold_data)
        .build()
        .render()
        .unwrap();
    decider_template
}

#[derive(Template, Default)]
#[template(path = "nova_cyclefold_decider.askama.sol", ext = "sol")]
pub(crate) struct NovaCyclefoldDecider {
    groth16_verifier: Groth16Verifier,
    kzg10_verifier: KZG10Verifier,
    z_len: usize,
    public_inputs_len: usize,
}

impl From<NovaCyclefoldData> for NovaCyclefoldDecider {
    fn from(value: NovaCyclefoldData) -> Self {
        let groth16_verifier = Groth16Verifier::from(value.g16_data);
        let public_inputs_len = groth16_verifier.gamma_abc_len;
        Self {
            groth16_verifier,
            kzg10_verifier: KZG10Verifier::from(value.kzg_data),
            z_len: value.z_len,
            public_inputs_len,
        }
    }
}

#[derive(CanonicalDeserialize, CanonicalSerialize, PartialEq, Debug, Clone)]
pub struct NovaCyclefoldData {
    g16_data: Groth16Data,
    kzg_data: KzgData,
    z_len: usize,
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

impl From<(Groth16Data, KzgData, usize)> for NovaCyclefoldData {
    fn from(value: (Groth16Data, KzgData, usize)) -> Self {
        Self {
            g16_data: value.0,
            kzg_data: value.1,
            z_len: value.2,
        }
    }
}

impl NovaCyclefoldData {
    pub fn new(
        vkey_g16: VerifyingKey<Bn254>,
        vkey_kzg: VerifierKey<Bn254>,
        crs_points: Vec<G1Affine>,
        z_len: usize,
    ) -> Self {
        Self {
            g16_data: Groth16Data::from(vkey_g16),
            // TODO: Remove option from crs points
            kzg_data: KzgData::from((vkey_kzg, Some(crs_points))),
            z_len,
        }
    }
}
