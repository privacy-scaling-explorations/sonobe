use ::clap::Parser;
use log::warn;
use settings::Cli;

mod settings;

fn main() {
    let cli = Cli::parse();

    // generate a subscriber with the desired log level
    env_logger::builder()
        .format_timestamp_secs()
        .filter_level(cli.verbosity.log_level_filter())
        .init();

    warn!("Jello!");

    // Fetch the exact protocol for which we need to generate the Decider verifier contract.
    let protocol = cli.protocol;
    match protocol {
        settings::Protocol::NovaCyclefold => {
            todo!()
        }
        _ => unreachable!(),
    }
}
