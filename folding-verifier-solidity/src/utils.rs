use ark_bn254::Bn254;
use ark_bn254::{Fq, Fr, G1Affine, G2Affine};
use ark_groth16::{Proof, VerifyingKey};
use askama::Template;
use std::{fmt, fmt::Display};

#[derive(Debug, Default)]
pub struct FqWrapper(pub Fq);

#[derive(Debug, Default)]
pub struct G1Repr(pub [FqWrapper; 2]);

#[derive(Debug, Default)]
pub struct G2Repr([[FqWrapper; 2]; 2]);

fn g1_to_fq_repr(g1: G1Affine) -> G1Repr {
    G1Repr([FqWrapper(g1.x), FqWrapper(g1.y)])
}

fn g2_to_fq_repr(g2: G2Affine) -> G2Repr {
    G2Repr([
        [FqWrapper(g2.x.c0), FqWrapper(g2.x.c1)],
        [FqWrapper(g2.y.c0), FqWrapper(g2.y.c1)],
    ])
}

impl Display for FqWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0 .0.to_string())
    }
}

impl Display for G1Repr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:#?}", self.0)
    }
}

impl Display for G2Repr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:#?}", self.0)
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;
    use ark_serialize::CanonicalDeserialize;
    use std::fs::File;

    fn load_test_data() -> (VerifyingKey<Bn254>, Proof<Bn254>, Fr) {
        let manifest_dir = env!("CARGO_MANIFEST_DIR");

        let file = File::open(format!("{}/assets/G16_test_vk_data", manifest_dir)).unwrap();
        let vk = VerifyingKey::<Bn254>::deserialize_compressed(&file).unwrap();

        let file = File::open(format!("{}/assets/G16_test_proof_data", manifest_dir)).unwrap();
        let proof = Proof::<Bn254>::deserialize_compressed(&file).unwrap();

        (vk, proof, Fr::from(35u64))
    }

    use super::*;

    #[test]
    fn something() {
        let (vk, proof, pi) = load_test_data();
        let template = SolidityVerifier::from(vk);

        let res = template.render().unwrap();
        eprintln!("{}", res);
    }
}
