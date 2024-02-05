pub(crate) mod test {
    pub use revm;
    use revm::{
        primitives::{hex, Address, CreateScheme, ExecutionResult, Output, TransactTo, TxEnv},
        InMemoryDB, EVM,
    };
    use std::{
        fmt::{self, Debug, Formatter},
        fs::{create_dir_all, File},
        io::{self, Write},
        process::{Command, Stdio},
        str,
    };

    // from: https://github.com/privacy-scaling-explorations/halo2-solidity-verifier/blob/85cb77b171ce3ee493628007c7a1cfae2ea878e6/examples/separately.rs#L56
    pub fn save_solidity(name: impl AsRef<str>, solidity: &str) {
        const DIR_GENERATED: &str = "./generated";
        create_dir_all(DIR_GENERATED).unwrap();
        File::create(format!("{DIR_GENERATED}/{}", name.as_ref()))
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
        let start_contract = stdout.find(contract_name)?;
        let stdout_contract = &stdout[start_contract..];
        let start = stdout_contract.find("Binary:")? + 8;
        Some(hex::decode(&stdout_contract[start..stdout_contract.len() - 1]).unwrap())
    }

    /// Evm runner.
    pub struct Evm {
        evm: EVM<InMemoryDB>,
    }

    impl Debug for Evm {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            let mut debug_struct = f.debug_struct("Evm");
            debug_struct
                .field("env", &self.evm.env)
                .field("db", &self.evm.db.as_ref().unwrap())
                .finish()
        }
    }

    impl Default for Evm {
        fn default() -> Self {
            Self {
                evm: EVM {
                    env: Default::default(),
                    db: Some(Default::default()),
                },
            }
        }
    }

    impl Evm {
        /// Return code_size of given address.
        ///
        /// # Panics
        /// Panics if given address doesn't have bytecode.
        pub fn code_size(&mut self, address: Address) -> usize {
            self.evm.db.as_ref().unwrap().accounts[&address]
                .info
                .code
                .as_ref()
                .unwrap()
                .len()
        }

        /// Apply create transaction with given `bytecode` as creation bytecode.
        /// Return created `address`.
        ///
        /// # Panics
        /// Panics if execution reverts or halts unexpectedly.
        pub fn create(&mut self, bytecode: Vec<u8>) -> Address {
            let (_, output) = self.transact_success_or_panic(TxEnv {
                gas_limit: u64::MAX,
                transact_to: TransactTo::Create(CreateScheme::Create),
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
            self.evm.env.tx = tx;
            let result = self.evm.transact_commit().unwrap();
            self.evm.env.tx = Default::default();
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
                            for (topic_idx, topic) in log.topics.iter().enumerate() {
                                println!("  topic{topic_idx}: {topic:?}");
                            }
                        }
                        println!("--- end ---");
                    }
                    (gas_used, output)
                }
                ExecutionResult::Revert { gas_used, output } => {
                    panic!("Transaction reverts with gas_used {gas_used} and output {output:#x}")
                }
                ExecutionResult::Halt { reason, gas_used } => panic!(
                    "Transaction halts unexpectedly with gas_used {gas_used} and reason {reason:?}"
                ),
            }
        }
    }
}
