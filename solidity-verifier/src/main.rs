use ::clap::Parser;
use ark_bn254::Bn254;
use ark_groth16::VerifyingKey;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Write};
use askama::Template;
use folding_verifier_solidity::SolidityVerifier;
use log::warn;
use settings::Cli;
use std::{fs, io};
use std::{fs::File, path::Path};

mod settings;

fn read_file<R: CanonicalDeserialize>(path: &Path) -> Result<R, io::Error> {
    let bytes = std::fs::read(path)?;
    R::deserialize_compressed(&bytes[..])
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, format!("{:?}", e)))
}

fn create_or_open_then_write<T: AsRef<[u8]>>(path: &Path, content: &T) -> Result<(), io::Error> {
    let mut file = fs::OpenOptions::new().create(true).write(true).open(path)?;
    file.write_all(content.as_ref())
}

fn main() {
    let cli = Cli::parse();

    // generate a subscriber with the desired log level
    env_logger::builder()
        .format_timestamp_secs()
        .filter_level(cli.verbosity.log_level_filter())
        .init();

    warn!("Jello!");
    let g16_vkey_path = cli.g16_vkey;

    let out_path = cli.out;
    warn!("{:?}", &out_path);
    // Fetch the exact protocol for which we need to generate the Decider verifier contract.
    let protocol = cli.protocol;
    match protocol {
        settings::Protocol::NovaCyclefold => {
            let g16_vkey = read_file::<VerifyingKey<Bn254>>(&g16_vkey_path)
                .expect(&format!("Can't find key at {:?}", &g16_vkey_path));
            create_or_open_then_write(
                &out_path,
                &SolidityVerifier::from(g16_vkey)
                    .render()
                    .unwrap()
                    .as_bytes(),
            )
            .unwrap();
        }
        _ => unreachable!(),
    }
}
