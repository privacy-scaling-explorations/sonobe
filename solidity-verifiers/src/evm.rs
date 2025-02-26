pub use revm;
use revm::{
    primitives::{hex, Address, ExecutionResult, Output, TransactTo, TxEnv},
    Evm as EVM, EvmBuilder, InMemoryDB,
};
use std::{
    fmt::Debug,
    fs::{self, create_dir_all, File},
    io::{self, Write},
    path::PathBuf,
    process::{Command, Stdio},
    str,
};

// from: https://github.com/privacy-scaling-explorations/halo2-solidity-verifier/blob/85cb77b171ce3ee493628007c7a1cfae2ea878e6/examples/separately.rs#L56
pub fn save_solidity(name: impl AsRef<str>, solidity: &str) {
    let curdir = PathBuf::from(".");
    let curdir_abs_path = fs::canonicalize(curdir).expect("Failed to get current directory");
    let curdir_abs_path = curdir_abs_path
        .to_str()
        .expect("Failed to convert path to string");
    let dir_generated = format!("{curdir_abs_path}/generated");
    create_dir_all(dir_generated.clone()).unwrap();
    File::create(format!("{}/{}", dir_generated, name.as_ref()))
        .unwrap()
        .write_all(solidity.as_bytes())
        .unwrap();
}

/// Compile solidity with `--via-ir` flag, then return creation bytecode.
///
/// # Panics
/// Panics if executable `solc` can not be found, or compilation fails.
pub fn compile_solidity(solidity: impl AsRef<[u8]>, contract_name: &str) -> Vec<u8> {
    let mut process = match Command::new("solc")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .arg("--bin")
        .arg("--optimize")
        .arg("-")
        .spawn()
    {
        Ok(process) => process,
        Err(err) if err.kind() == io::ErrorKind::NotFound => {
            panic!("Command 'solc' not found");
        }
        Err(err) => {
            panic!("Failed to spawn process with command 'solc':\n{err}");
        }
    };
    process
        .stdin
        .take()
        .unwrap()
        .write_all(solidity.as_ref())
        .unwrap();
    let output = process.wait_with_output().unwrap();
    let stdout = str::from_utf8(&output.stdout).unwrap();
    if let Some(binary) = find_binary(stdout, contract_name) {
        binary
    } else {
        panic!(
            "Compilation fails:\n{}",
            str::from_utf8(&output.stderr).unwrap()
        )
    }
}

/// Find binary from `stdout` with given `contract_name`.
/// `contract_name` is provided since `solc` may compile multiple contracts or libraries.
/// hence, we need to find the correct binary.
fn find_binary(stdout: &str, contract_name: &str) -> Option<Vec<u8>> {
    let intro_str = format!("======= <stdin>:{contract_name} =======\nBinary:\n");
    let start = stdout.find(&intro_str)?;
    let end = stdout[start + intro_str.len()..]
        .find('\n')
        .map(|pos| pos + start + intro_str.len())
        .unwrap_or(stdout.len());
    let binary_section = stdout[start + intro_str.len()..end].trim();
    Some(hex::decode(binary_section).unwrap())
}

/// Evm runner.
#[derive(Debug)]
pub struct Evm<'a> {
    evm: EVM<'a, (), InMemoryDB>,
}

impl<'a> Default for Evm<'a> {
    fn default() -> Self {
        Self {
            evm: EvmBuilder::default().with_db(InMemoryDB::default()).build(),
        }
    }
}

impl<'a> Evm<'a> {
    /// Apply create transaction with given `bytecode` as creation bytecode.
    /// Return created `address`.
    ///
    /// # Panics
    /// Panics if execution reverts or halts unexpectedly.
    pub fn create(&mut self, bytecode: Vec<u8>) -> Address {
        let (_, output) = self.transact_success_or_panic(TxEnv {
            gas_limit: u64::MAX,
            transact_to: TransactTo::Create,
            data: bytecode.into(),
            ..Default::default()
        });
        match output {
            Output::Create(_, Some(address)) => address,
            _ => unreachable!(),
        }
    }

    /// Apply call transaction to given `address` with `calldata`.
    /// Returns `gas_used` and `return_data`.
    ///
    /// # Panics
    /// Panics if execution reverts or halts unexpectedly.
    pub fn call(&mut self, address: Address, calldata: Vec<u8>) -> (u64, Vec<u8>) {
        let (gas_used, output) = self.transact_success_or_panic(TxEnv {
            gas_limit: u64::MAX,
            transact_to: TransactTo::Call(address),
            data: calldata.into(),
            ..Default::default()
        });
        match output {
            Output::Call(output) => (gas_used, output.into()),
            _ => unreachable!(),
        }
    }

    fn transact_success_or_panic(&mut self, tx: TxEnv) -> (u64, Output) {
        *self.evm.tx_mut() = tx;
        let result = self.evm.transact_commit().unwrap();
        match result {
            ExecutionResult::Success {
                gas_used,
                output,
                logs,
                ..
            } => {
                if !logs.is_empty() {
                    println!("--- logs from {} ---", logs[0].address);
                    for (log_idx, log) in logs.iter().enumerate() {
                        println!("log#{log_idx}");
                        for (topic_idx, topic) in log.topics().iter().enumerate() {
                            println!("  topic{topic_idx}: {topic:?}");
                        }
                    }
                    println!("--- end ---");
                }
                (gas_used, output)
            }
            ExecutionResult::Revert { gas_used, output } => (gas_used, Output::Call(output)),
            ExecutionResult::Halt { reason, gas_used } => panic!(
                "Transaction halts unexpectedly with gas_used {gas_used} and reason {reason:?}"
            ),
        }
    }
}
