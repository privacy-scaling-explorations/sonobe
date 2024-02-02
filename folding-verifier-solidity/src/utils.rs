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
        write!(f, "{}", self.0.to_string())
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
    use crate::evm::*;
    use ark_ec::AffineRepr;
    use ark_ff::{BigInteger, PrimeField};
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Write};
    use hex::encode;
    use revm::primitives::U256;
    use std::{
        fs::File,
        io,
        process::{Command, Stdio},
    };

    fn load_test_data() -> (VerifyingKey<Bn254>, Proof<Bn254>, Fr) {
        let manifest_dir = env!("CARGO_MANIFEST_DIR");

        let file = File::open(format!("{}/assets/G16_test_vk_data", manifest_dir)).unwrap();
        let vk = VerifyingKey::<Bn254>::deserialize_compressed(&file).unwrap();

        let file = File::open(format!("{}/assets/G16_test_proof_data", manifest_dir)).unwrap();
        let proof = Proof::<Bn254>::deserialize_compressed(&file).unwrap();

        (vk, proof, Fr::from(35u64))
    }

    /// Compile given Solidity `code` into deployment bytecode.
    pub fn compile_solidity(code: &str) -> Vec<u8> {
        let mut cmd = match Command::new("solc")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .arg("--bin")
            .arg("-")
            .spawn()
        {
            Ok(cmd) => cmd,
            Err(err) if err.kind() == io::ErrorKind::NotFound => {
                panic!("Command 'solc' not found");
            }
            Err(err) => {
                panic!("Failed to spawn cmd with command 'solc':\n{err}");
            }
        };

        cmd.stdin
            .take()
            .unwrap()
            .write_all(code.as_bytes())
            .unwrap();
        let output = cmd.wait_with_output().unwrap().stdout;
        let binary = *split_by_ascii_whitespace(&output).last().unwrap();
        hex::decode(binary).unwrap()
    }

    fn split_by_ascii_whitespace(bytes: &[u8]) -> Vec<&[u8]> {
        let mut split = Vec::new();
        let mut start = None;
        for (idx, byte) in bytes.iter().enumerate() {
            if byte.is_ascii_whitespace() {
                if let Some(start) = start.take() {
                    split.push(&bytes[start..idx]);
                }
            } else if start.is_none() {
                start = Some(idx);
            }
        }
        split
    }

    #[test]
    fn something() {
        let (vk, proof, pi) = load_test_data();
        let template = SolidityVerifier::from(vk);

        println!("{}", template);

        let res = template.render().unwrap();
        // let bytecode = compile_solidity(&res);

        // let mut evm = Evm::default();
        // let verifier_address = evm.create(bytecode);
        // let verifier_runtime_code_size = evm.code_size(verifier_address);

        let mut calldata = vec![];
        pi.serialize_uncompressed(&mut calldata).unwrap();
        proof.serialize_uncompressed(&mut calldata).unwrap();
        println!("A coord X {}", proof.a.x().unwrap().into_bigint());
        println!("A coord Y {}", proof.a.y().unwrap().into_bigint());
        println!("B X c0 {}", proof.b.x().unwrap().c0.into_bigint());
        println!("{}", proof.b.x().unwrap().c1.into_bigint());
        println!("{}", proof.b.y().unwrap().c0.into_bigint());
        println!("{}", proof.b.y().unwrap().c1.into_bigint());
        println!("C coord X {}", proof.c.x().unwrap().into_bigint());
        println!("C coord Y {}", proof.c.y().unwrap().into_bigint());

        println!("{:?}", hex::encode(calldata));

        /*
        [12789841443114878786012274900958960562863291377603298588996397612743214270533, 8371334585386453528714380627543265152075449166138960668073923127915708302918]
        [[12522206255038260967553106003273653153059437125460434909321001278476478563099, 7102572973382534269970250325141231327406282500396145387860750610050816584321], [11959723456754807302055526676718525325852240128103399509369713681715451048557, 16100176535437748320172804270898298046286395181881469074804264499369100517575]]
        [7966130069787952207190650262573736474574320231144059824022215179523642128059, 5008468717564049131407964336167989927527065952193350248286730060342196401539]
        [2300000000000000000000000000000000000000000000000000000000000000]
         */

        //[12789841443114878786012274900958960562863291377603298588996397612743214270533, 8371334585386453528714380627543265152075449166138960668073923127915708302918], [[12522206255038260967553106003273653153059437125460434909321001278476478563099, 7102572973382534269970250325141231327406282500396145387860750610050816584321], [11959723456754807302055526676718525325852240128103399509369713681715451048557, 16100176535437748320172804270898298046286395181881469074804264499369100517575]], [7966130069787952207190650262573736474574320231144059824022215179523642128059, 5008468717564049131407964336167989927527065952193350248286730060342196401539], [2300000000000000000000000000000000000000000000000000000000000000]
    }
}
