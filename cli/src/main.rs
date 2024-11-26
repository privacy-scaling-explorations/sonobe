use ::clap::Parser;
use ark_serialize::Write;
use settings::Cli;
use std::path::Path;
use std::{fs, io};

mod settings;

fn create_or_open_then_write<T: AsRef<[u8]>>(path: &Path, content: &T) -> Result<(), io::Error> {
    let mut file = fs::OpenOptions::new()
        .create(true)
        .truncate(true)
        .write(true)
        .open(path)?;
    file.write_all(content.as_ref())
}

fn main() {
    let cli = Cli::parse();

    // generate a subscriber with the desired log level
    env_logger::builder()
        .format_timestamp_secs()
        .filter_level(cli.verbosity.log_level_filter())
        .init();

    let out_path = cli.out;

    // Fetch the exact protocol for which we need to generate the Decider verifier contract.
    let protocol = cli.protocol;
    // Fetch the protocol data passed by the user from the file.
    let protocol_vk = std::fs::read(cli.protocol_vk).unwrap();

    // Generate the Solidity Verifier contract for the selected protocol with the given data.
    create_or_open_then_write(
        &out_path,
        &protocol.render(&protocol_vk, cli.pragma).unwrap(),
    )
    .unwrap();
}
