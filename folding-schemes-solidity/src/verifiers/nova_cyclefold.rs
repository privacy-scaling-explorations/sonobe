use crate::{Groth16Data, KzgData, ProtocolData};
use ark_bn254::{Bn254, G1Affine};
use ark_groth16::VerifyingKey;
use ark_poly_commit::kzg10::VerifierKey;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use askama::Template;

use super::g16::Groth16Verifier;
use super::kzg::KZG10Verifier;

#[derive(CanonicalDeserialize, CanonicalSerialize, PartialEq, Debug)]
pub struct NovaCyclefoldData {
    g16_data: Groth16Data,
    kzg_data: KzgData,
}

impl ProtocolData for NovaCyclefoldData {
    const PROTOCOL_NAME: &'static str = "NovaCyclefold";

    fn render_as_template(self, pragma: &Option<String>) -> Vec<u8> {
        NovaCyclefoldDecider::from((self, pragma))
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

#[derive(Template)]
#[template(path = "nova_cyclefold_decider.askama.sol", ext = "sol")]
pub struct NovaCyclefoldDecider {
    pub groth16_verifier: Groth16Verifier,
    pub kzg10_verifier: KZG10Verifier,
}

impl From<(NovaCyclefoldData, &Option<String>)> for NovaCyclefoldDecider {
    fn from(value: (NovaCyclefoldData, &Option<String>)) -> Self {
        Self {
            groth16_verifier: Groth16Verifier::from((value.0.g16_data, value.1)),
            kzg10_verifier: KZG10Verifier::from((value.0.kzg_data, value.1)),
        }
    }
}

impl NovaCyclefoldDecider {
    pub(crate) fn new(
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
