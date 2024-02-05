use crate::utils::encoding::{g1_to_fq_repr, g2_to_fq_repr};
/// Solidity templates for the verifier contracts.
/// We use askama for templating and define which variables are required for each template.
use crate::utils::encoding::{G1Repr, G2Repr};
use ark_bn254::{Bn254, G1Projective};
use ark_groth16::VerifyingKey;
use ark_poly_commit::kzg10::VerifierKey;
use askama::Template;
use folding_schemes::commitment::kzg::ProverKey;

#[derive(Template, Default)]
#[template(path = "groth_16_verifier.sol", ext = "sol")]
pub struct SolidityVerifier {
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

impl From<VerifyingKey<Bn254>> for SolidityVerifier {
    fn from(value: VerifyingKey<Bn254>) -> Self {
        Self {
            vkey_alpha_g1: g1_to_fq_repr(value.alpha_g1),
            vkey_beta_g2: g2_to_fq_repr(value.beta_g2),
            vkey_gamma_g2: g2_to_fq_repr(value.gamma_g2),
            vkey_delta_g2: g2_to_fq_repr(value.delta_g2),
            gamma_abc_len: value.gamma_abc_g1.len(),
            gamma_abc_g1: value
                .gamma_abc_g1
                .iter()
                .copied()
                .map(|f| g1_to_fq_repr(f))
                .collect(),
        }
    }
}

#[derive(Template, Default)]
#[template(path = "kzg_10_verifier.sol", ext = "sol")]
pub struct KZG10Verifier {
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
    pub fn from(pk: &ProverKey<G1Projective>, vk: &VerifierKey<Bn254>) -> KZG10Verifier {
        let g1_string_repr = g1_to_fq_repr(vk.g);
        let g2_string_repr = g2_to_fq_repr(vk.h);
        let vk_string_repr = g2_to_fq_repr(vk.beta_h);
        let g1_crs_len = pk.powers_of_g.len();

        let g1_crs = pk
            .powers_of_g
            .into_iter()
            .map(|g1| g1_to_fq_repr(*g1))
            .collect();
        KZG10Verifier {
            g1: g1_string_repr,
            g2: g2_string_repr,
            vk: vk_string_repr,
            g1_crs,
            g1_crs_len,
        }
    }
}
