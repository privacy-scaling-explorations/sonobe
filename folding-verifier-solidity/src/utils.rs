use std::{
    fmt,
    fmt::Display,
    fs::{create_dir_all, File},
    io::{self, Write},
    process::{Command, Stdio},
    str,
};

use ark_bn254::{Fq, G1Affine, G2Affine};
use askama::Template;

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
        write!(f, "{:#?}", self.0)
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

#[derive(Debug, Default)]
pub struct G1StringRepr([String; 2]);

#[derive(Debug, Default)]
pub struct G2StringRepr([String; 2], [String; 2]);

#[derive(Template, Default)]
#[template(path = "kzg_10_verifier.sol", ext = "sol")]
pub struct KZG10Verifier {
    pub g1: G1StringRepr,
    pub g2: G2StringRepr,
    pub vk: G2StringRepr,
    pub g1_crs: Vec<G1StringRepr>,
    pub g1_crs_len: usize,
}

impl KZG10Verifier {
    pub fn new(g1: G1Affine, g2: G2Affine, vk: G2Affine, g1_crs: Vec<G1Affine>) -> Self {
        let g1_string_repr = G1StringRepr([g1.x.to_string(), g1.y.to_string()]);
        let g2_string_repr = G2StringRepr(
            [g2.x.c0.to_string(), g2.x.c1.to_string()],
            [g2.y.c0.to_string(), g2.y.c1.to_string()],
        );
        let vk_string_repr = G2StringRepr(
            [vk.x.c0.to_string(), vk.x.c1.to_string()],
            [vk.y.c0.to_string(), vk.y.c1.to_string()],
        );
        let g1_crs_len = g1_crs.len();
        let g1_crs = g1_crs
            .into_iter()
            .map(|g1| G1StringRepr([g1.x.to_string(), g1.y.to_string()]))
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

// from: https://github.com/privacy-scaling-explorations/halo2-solidity-verifier/blob/85cb77b171ce3ee493628007c7a1cfae2ea878e6/examples/separately.rs#L56
fn save_solidity(name: impl AsRef<str>, solidity: &str) {
    const DIR_GENERATED: &str = "./generated";
    create_dir_all(DIR_GENERATED).unwrap();
    File::create(format!("{DIR_GENERATED}/{}", name.as_ref()))
        .unwrap()
        .write_all(solidity.as_bytes())
        .unwrap();
}

mod tests {

    use super::*;
    use crate::evm::test::Evm;
    use ark_std::UniformRand;

    #[test]
    fn something() {
        let mut template = SolidityVerifier::default();
        template.gamma_abc_len = 1;
        template.gamma_abc_g1.push(G1Repr::default());
        let res = template.render().unwrap();
        eprintln!("{:?}", res);
    }

    #[test]
    fn test_kzg_verifier_compiles() {
        let rng = &mut ark_std::test_rng();
        let g1 = G1Affine::rand(rng);
        let g2 = G2Affine::rand(rng);
        let vk = G2Affine::rand(rng);
        let g1_crs = (0..10).map(|_| G1Affine::rand(rng)).collect();
        let template = KZG10Verifier::new(g1, g2, vk, g1_crs);
        let res = template.render().unwrap();
        save_solidity("kzg_10_verifier.sol", &res);
        let kzg_verifier_bytecode = crate::evm::test::compile_solidity(&res);
        let mut evm = Evm::default();
        let kzg_verifier_address = evm.create(kzg_verifier_bytecode);
        println!("kzg verifier address: {:?}", kzg_verifier_address);
        let verifier_runtime_code_size = evm.code_size(kzg_verifier_address);
    }

    #[test]
    fn test_kzg_10_verifier_template() {
        let rng = &mut ark_std::test_rng();
        let g1 = G1Affine::rand(rng);
        let g2 = G2Affine::rand(rng);
        let vk = G2Affine::rand(rng);
        let g1_crs = (0..10).map(|_| G1Affine::rand(rng)).collect();
        let template = KZG10Verifier::new(g1, g2, vk, g1_crs);
        let res = template.render().unwrap();
        eprintln!("{:?}", res);
    }
}
