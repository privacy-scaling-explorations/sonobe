use ark_bn254::{Fq, G1Affine, G2Affine};
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

#[cfg(test)]
mod tests {

    use std::{
        fs::{create_dir_all, File},
        io::Write,
    };

    use super::*;
    use crate::evm::test::Evm;
    use ark_bn254::{Bn254, Fr, G1Projective as G1};
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::{BigInteger, PrimeField};
    use ark_poly_commit::kzg10::VerifierKey;
    use ark_std::{test_rng, UniformRand, Zero};
    use folding_schemes::{
        commitment::{
            kzg::{KZGProver, KZGSetup, ProverKey},
            CommitmentProver,
        },
        transcript::{
            poseidon::{poseidon_test_config, PoseidonTranscript},
            Transcript,
        },
    };
    use itertools::chain;

    // from: https://github.com/privacy-scaling-explorations/halo2-solidity-verifier/blob/85cb77b171ce3ee493628007c7a1cfae2ea878e6/examples/separately.rs#L56
    pub fn save_solidity(name: impl AsRef<str>, solidity: &str) {
        const DIR_GENERATED: &str = "./generated";
        create_dir_all(DIR_GENERATED).unwrap();
        File::create(format!("{DIR_GENERATED}/{}", name.as_ref()))
            .unwrap()
            .write_all(solidity.as_bytes())
            .unwrap();
    }

    // pub const FN_KZG10_BATCH_CHECK: [u8; 4] = [0xfe, 0x41, 0x5e, 0xbc];
    pub const FN_KZG10_CHECK: [u8; 4] = [0x9e, 0x78, 0xcc, 0xf7];

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
        _ = evm.create(kzg_verifier_bytecode);
    }

    #[test]
    fn test_kzg_verifier_accepts_valid_proofs() {
        let rng = &mut test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();
        let transcript_p = &mut PoseidonTranscript::<G1>::new(&poseidon_config);
        let transcript_v = &mut PoseidonTranscript::<G1>::new(&poseidon_config);

        let n = 10;
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) = KZGSetup::<Bn254>::setup(rng, n);
        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(rng)).take(n).collect();
        let cm = KZGProver::<G1>::commit(&pk, &v, &Fr::zero()).unwrap();
        let (eval, proof) =
            KZGProver::<G1>::prove(&pk, transcript_p, &cm, &v, &Fr::zero()).unwrap();

        let crs = pk
            .powers_of_g
            .iter()
            .map(|tau_g| *tau_g)
            .collect::<Vec<_>>();

        let template = KZG10Verifier::new(crs[0], vk.h, vk.beta_h, crs);
        let res = template.render().unwrap();
        let kzg_verifier_bytecode = crate::evm::test::compile_solidity(&res);
        let mut evm = Evm::default();
        let verifier_address = evm.create(kzg_verifier_bytecode);

        let (cm_affine, proof_affine) = (cm.into_affine(), proof.into_affine());
        let (x_comm, y_comm) = cm_affine.xy().unwrap();
        let (x_proof, y_proof) = proof_affine.xy().unwrap();
        let y = eval.into_bigint().to_bytes_be();

        transcript_v.absorb_point(&cm).unwrap();
        let x = transcript_v.get_challenge();

        let x = x.into_bigint().to_bytes_be();
        let mut calldata: Vec<u8> = chain![
            FN_KZG10_CHECK,
            x_comm.into_bigint().to_bytes_be(),
            y_comm.into_bigint().to_bytes_be(),
            x_proof.into_bigint().to_bytes_be(),
            y_proof.into_bigint().to_bytes_be(),
            x.clone(),
            y,
        ]
        .collect();

        let (_, output) = evm.call(verifier_address, calldata.clone());
        assert_eq!(*output.last().unwrap(), 1);

        // change calldata to make it invalid
        let last_calldata_element = calldata.last_mut().unwrap();
        *last_calldata_element = 0;
        let (_, output) = evm.call(verifier_address, calldata);
        assert_eq!(*output.last().unwrap(), 0);
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
