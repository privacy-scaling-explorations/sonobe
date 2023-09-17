use super::{fnv, CircomBase, SafeMemory, Wasm};
use color_eyre::Result;
use num_bigint::BigInt;
use num_traits::Zero;
use std::cell::Cell;
use wasmer::{imports, Function, Instance, Memory, MemoryType, Module, RuntimeError, Store};

#[cfg(feature = "circom-2")]
use num::ToPrimitive;

#[cfg(feature = "circom-2")]
use super::Circom2;

use super::Circom;

#[derive(Clone, Debug)]
pub struct WitnessCalculator {
    pub instance: Wasm,
    pub memory: SafeMemory,
    pub n64: u32,
    pub circom_version: u32,
}

// Error type to signal end of execution.
// From https://docs.wasmer.io/integrations/examples/exit-early
#[derive(thiserror::Error, Debug, Clone, Copy)]
#[error("{0}")]
struct ExitCode(u32);

#[cfg(feature = "circom-2")]
fn from_array32(arr: Vec<u32>) -> BigInt {
    let mut res = BigInt::zero();
    let radix = BigInt::from(0x100000000u64);
    for &val in arr.iter() {
        res = res * &radix + BigInt::from(val);
    }
    res
}

#[cfg(feature = "circom-2")]
fn to_array32(s: &BigInt, size: usize) -> Vec<u32> {
    let mut res = vec![0; size];
    let mut rem = s.clone();
    let radix = BigInt::from(0x100000000u64);
    let mut c = size;
    while !rem.is_zero() {
        c -= 1;
        res[c] = (&rem % &radix).to_u32().unwrap();
        rem /= &radix;
    }

    res
}

impl WitnessCalculator {
    pub fn new(path: impl AsRef<std::path::Path>) -> Result<Self> {
        Self::from_file(path)
    }

    pub fn from_file(path: impl AsRef<std::path::Path>) -> Result<Self> {
        let store = Store::default();
        let module = Module::from_file(&store, path)?;
        Self::from_module(module)
    }

    pub fn from_module(module: Module) -> Result<Self> {
        let store = module.store();

        // Set up the memory
        let memory = Memory::new(store, MemoryType::new(2000, None, false)).unwrap();
        let import_object = imports! {
            "env" => {
                "memory" => memory.clone(),
            },
            // Host function callbacks from the WASM
            "runtime" => {
                "error" => runtime::error(store),
                "logSetSignal" => runtime::log_signal(store),
                "logGetSignal" => runtime::log_signal(store),
                "logFinishComponent" => runtime::log_component(store),
                "logStartComponent" => runtime::log_component(store),
                "log" => runtime::log_component(store),
                "exceptionHandler" => runtime::exception_handler(store),
                "showSharedRWMemory" => runtime::show_memory(store),
                "printErrorMessage" => runtime::print_error_message(store),
                "writeBufferMessage" => runtime::write_buffer_message(store),
            }
        };
        let instance = Wasm::new(Instance::new(&module, &import_object)?);

        let version = instance.get_version().unwrap_or(1);

        // Circom 2 feature flag with version 2
        #[cfg(feature = "circom-2")]
        fn new_circom2(instance: Wasm, memory: Memory, version: u32) -> Result<WitnessCalculator> {
            let n32 = instance.get_field_num_len32()?;
            let mut safe_memory = SafeMemory::new(memory, n32 as usize, BigInt::zero());
            instance.get_raw_prime()?;
            let mut arr = vec![0; n32 as usize];
            for i in 0..n32 {
                let res = instance.read_shared_rw_memory(i)?;
                arr[(n32 as usize) - (i as usize) - 1] = res;
            }
            let prime = from_array32(arr);

            let n64 = ((prime.bits() - 1) / 64 + 1) as u32;
            safe_memory.prime = prime;

            Ok(WitnessCalculator {
                instance,
                memory: safe_memory,
                n64,
                circom_version: version,
            })
        }

        fn new_circom1(instance: Wasm, memory: Memory, version: u32) -> Result<WitnessCalculator> {
            // Fallback to Circom 1 behavior
            let n32 = (instance.get_fr_len()? >> 2) - 2;
            let mut safe_memory = SafeMemory::new(memory, n32 as usize, BigInt::zero());
            let ptr = instance.get_ptr_raw_prime()?;
            let prime = safe_memory.read_big(ptr as usize, n32 as usize)?;

            let n64 = ((prime.bits() - 1) / 64 + 1) as u32;
            safe_memory.prime = prime;

            Ok(WitnessCalculator {
                instance,
                memory: safe_memory,
                n64,
                circom_version: version,
            })
        }

        // Three possibilities:
        // a) Circom 2 feature flag enabled, WASM runtime version 2
        // b) Circom 2 feature flag enabled, WASM runtime version 1
        // c) Circom 1 default behavior
        //
        // Once Circom 2 support is more stable, feature flag can be removed

        cfg_if::cfg_if! {
            if #[cfg(feature = "circom-2")] {
                match version {
                    2 => new_circom2(instance, memory, version),
                    1 => new_circom1(instance, memory, version),
                    _ => panic!("Unknown Circom version")
                }
            } else {
                new_circom1(instance, memory, version)
            }
        }
    }

    pub fn calculate_witness<I: IntoIterator<Item = (String, Vec<BigInt>)>>(
        &mut self,
        inputs: I,
        sanity_check: bool,
    ) -> Result<Vec<BigInt>> {
        self.instance.init(sanity_check)?;

        cfg_if::cfg_if! {
            if #[cfg(feature = "circom-2")] {
                match self.circom_version {
                    2 => self.calculate_witness_circom2(inputs, sanity_check),
                    1 => self.calculate_witness_circom1(inputs, sanity_check),
                    _ => panic!("Unknown Circom version")
                }
            } else {
                self.calculate_witness_circom1(inputs, sanity_check)
            }
        }
    }

    // Circom 1 default behavior
    fn calculate_witness_circom1<I: IntoIterator<Item = (String, Vec<BigInt>)>>(
        &mut self,
        inputs: I,
        sanity_check: bool,
    ) -> Result<Vec<BigInt>> {
        self.instance.init(sanity_check)?;

        let old_mem_free_pos = self.memory.free_pos();
        let p_sig_offset = self.memory.alloc_u32();
        let p_fr = self.memory.alloc_fr();

        // allocate the inputs
        for (name, values) in inputs.into_iter() {
            let (msb, lsb) = fnv(&name);

            self.instance
                .get_signal_offset32(p_sig_offset, 0, msb, lsb)?;

            let sig_offset = self.memory.read_u32(p_sig_offset as usize) as usize;

            for (i, value) in values.into_iter().enumerate() {
                self.memory.write_fr(p_fr as usize, &value)?;
                self.instance
                    .set_signal(0, 0, (sig_offset + i) as u32, p_fr)?;
            }
        }

        let mut w = Vec::new();

        let n_vars = self.instance.get_n_vars()?;
        for i in 0..n_vars {
            let ptr = self.instance.get_ptr_witness(i)? as usize;
            let el = self.memory.read_fr(ptr)?;
            w.push(el);
        }

        self.memory.set_free_pos(old_mem_free_pos);

        Ok(w)
    }

    // Circom 2 feature flag with version 2
    #[cfg(feature = "circom-2")]
    fn calculate_witness_circom2<I: IntoIterator<Item = (String, Vec<BigInt>)>>(
        &mut self,
        inputs: I,
        sanity_check: bool,
    ) -> Result<Vec<BigInt>> {
        self.instance.init(sanity_check)?;

        let n32 = self.instance.get_field_num_len32()?;

        // allocate the inputs
        for (name, values) in inputs.into_iter() {
            let (msb, lsb) = fnv(&name);

            for (i, value) in values.into_iter().enumerate() {
                let f_arr = to_array32(&value, n32 as usize);
                for j in 0..n32 {
                    self.instance
                        .write_shared_rw_memory(j, f_arr[(n32 as usize) - 1 - (j as usize)])?;
                }
                self.instance.set_input_signal(msb, lsb, i as u32)?;
            }
        }

        let mut w = Vec::new();

        let witness_size = self.instance.get_witness_size()?;
        for i in 0..witness_size {
            self.instance.get_witness(i)?;
            let mut arr = vec![0; n32 as usize];
            for j in 0..n32 {
                arr[(n32 as usize) - 1 - (j as usize)] = self.instance.read_shared_rw_memory(j)?;
            }
            w.push(from_array32(arr));
        }

        Ok(w)
    }

    pub fn calculate_witness_element<
        E: ark_ec::pairing::Pairing,
        I: IntoIterator<Item = (String, Vec<BigInt>)>,
    >(
        &mut self,
        inputs: I,
        sanity_check: bool,
    ) -> Result<Vec<E::ScalarField>> {
        use ark_ff::PrimeField;
        let witness = self.calculate_witness(inputs, sanity_check)?;
        let modulus = <E::ScalarField as PrimeField>::MODULUS;

        // convert it to field elements
        use num_traits::Signed;
        let witness = witness
            .into_iter()
            .map(|w| {
                let w = if w.sign() == num_bigint::Sign::Minus {
                    // Need to negate the witness element if negative
                    modulus.into() - w.abs().to_biguint().unwrap()
                } else {
                    w.to_biguint().unwrap()
                };
                E::ScalarField::from(w)
            })
            .collect::<Vec<_>>();

        Ok(witness)
    }

    pub fn get_witness_buffer(&self) -> Result<Vec<u8>> {
        let ptr = self.instance.get_ptr_witness_buffer()? as usize;

        let view = self.memory.memory.view::<u8>();

        let len = self.instance.get_n_vars()? * self.n64 * 8;
        let arr = view[ptr..ptr + len as usize]
            .iter()
            .map(Cell::get)
            .collect::<Vec<_>>();

        Ok(arr)
    }
}

// callback hooks for debugging
mod runtime {
    use super::*;

    pub fn error(store: &Store) -> Function {
        #[allow(unused)]
        #[allow(clippy::many_single_char_names)]
        fn func(a: i32, b: i32, c: i32, d: i32, e: i32, f: i32) -> Result<(), RuntimeError> {
            // NOTE: We can also get more information why it is failing, see p2str etc here:
            // https://github.com/iden3/circom_runtime/blob/master/js/witness_calculator.js#L52-L64
            println!("runtime error, exiting early: {a} {b} {c} {d} {e} {f}",);
            Err(RuntimeError::user(Box::new(ExitCode(1))))
        }
        Function::new_native(store, func)
    }

    // Circom 2.0
    pub fn exception_handler(store: &Store) -> Function {
        #[allow(unused)]
        fn func(a: i32) {}
        Function::new_native(store, func)
    }

    // Circom 2.0
    pub fn show_memory(store: &Store) -> Function {
        #[allow(unused)]
        fn func() {}
        Function::new_native(store, func)
    }

    // Circom 2.0
    pub fn print_error_message(store: &Store) -> Function {
        #[allow(unused)]
        fn func() {}
        Function::new_native(store, func)
    }

    // Circom 2.0
    pub fn write_buffer_message(store: &Store) -> Function {
        #[allow(unused)]
        fn func() {}
        Function::new_native(store, func)
    }

    pub fn log_signal(store: &Store) -> Function {
        #[allow(unused)]
        fn func(a: i32, b: i32) {}
        Function::new_native(store, func)
    }

    pub fn log_component(store: &Store) -> Function {
        #[allow(unused)]
        fn func(a: i32) {}
        Function::new_native(store, func)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{collections::HashMap, path::PathBuf};

    struct TestCase<'a> {
        circuit_path: &'a str,
        inputs_path: &'a str,
        n_vars: u32,
        n64: u32,
        witness: &'a [&'a str],
    }

    pub fn root_path(p: &str) -> String {
        let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        path.push(p);
        path.to_string_lossy().to_string()
    }

    #[test]
    fn multiplier_1() {
        run_test(TestCase {
            circuit_path: root_path("test-vectors/mycircuit.wasm").as_str(),
            inputs_path: root_path("test-vectors/mycircuit-input1.json").as_str(),
            n_vars: 4,
            n64: 4,
            witness: &["1", "33", "3", "11"],
        });
    }

    #[test]
    fn multiplier_2() {
        run_test(TestCase {
            circuit_path: root_path("test-vectors/mycircuit.wasm").as_str(),
            inputs_path: root_path("test-vectors/mycircuit-input2.json").as_str(),
            n_vars: 4,
            n64: 4,
            witness: &[
                "1",
                "21888242871839275222246405745257275088548364400416034343698204186575672693159",
                "21888242871839275222246405745257275088548364400416034343698204186575796149939",
                "11",
            ],
        });
    }

    #[test]
    fn multiplier_3() {
        run_test(TestCase {
            circuit_path: root_path("test-vectors/mycircuit.wasm").as_str(),
            inputs_path: root_path("test-vectors/mycircuit-input3.json").as_str(),
            n_vars: 4,
            n64: 4,
            witness: &[
                "1",
                "21888242871839275222246405745257275088548364400416034343698204186575808493616",
                "10944121435919637611123202872628637544274182200208017171849102093287904246808",
                "2",
            ],
        });
    }

    #[test]
    fn safe_multipler() {
        let witness =
            std::fs::read_to_string(root_path("test-vectors/safe-circuit-witness.json")).unwrap();
        let witness: Vec<String> = serde_json::from_str(&witness).unwrap();
        let witness = &witness.iter().map(|x| x.as_ref()).collect::<Vec<_>>();
        run_test(TestCase {
            circuit_path: root_path("test-vectors/circuit2.wasm").as_str(),
            inputs_path: root_path("test-vectors/mycircuit-input1.json").as_str(),
            n_vars: 132, // 128 + 4
            n64: 4,
            witness,
        });
    }

    #[test]
    fn smt_verifier() {
        let witness =
            std::fs::read_to_string(root_path("test-vectors/smtverifier10-witness.json")).unwrap();
        let witness: Vec<String> = serde_json::from_str(&witness).unwrap();
        let witness = &witness.iter().map(|x| x.as_ref()).collect::<Vec<_>>();

        run_test(TestCase {
            circuit_path: root_path("test-vectors/smtverifier10.wasm").as_str(),
            inputs_path: root_path("test-vectors/smtverifier10-input.json").as_str(),
            n_vars: 4794,
            n64: 4,
            witness,
        });
    }

    use serde_json::Value;
    use std::str::FromStr;

    fn value_to_bigint(v: Value) -> BigInt {
        match v {
            Value::String(inner) => BigInt::from_str(&inner).unwrap(),
            Value::Number(inner) => BigInt::from(inner.as_u64().expect("not a u32")),
            _ => panic!("unsupported type"),
        }
    }

    fn run_test(case: TestCase) {
        let mut wtns = WitnessCalculator::new(case.circuit_path).unwrap();
        assert_eq!(
            wtns.memory.prime.to_str_radix(16),
            "30644E72E131A029B85045B68181585D2833E84879B9709143E1F593F0000001".to_lowercase()
        );
        assert_eq!({ wtns.instance.get_n_vars().unwrap() }, case.n_vars);
        assert_eq!({ wtns.n64 }, case.n64);

        let inputs_str = std::fs::read_to_string(case.inputs_path).unwrap();
        let inputs: std::collections::HashMap<String, serde_json::Value> =
            serde_json::from_str(&inputs_str).unwrap();

        let inputs = inputs
            .iter()
            .map(|(key, value)| {
                let res = match value {
                    Value::String(inner) => {
                        vec![BigInt::from_str(inner).unwrap()]
                    }
                    Value::Number(inner) => {
                        vec![BigInt::from(inner.as_u64().expect("not a u32"))]
                    }
                    Value::Array(inner) => inner.iter().cloned().map(value_to_bigint).collect(),
                    _ => panic!(),
                };

                (key.clone(), res)
            })
            .collect::<HashMap<_, _>>();

        let res = wtns.calculate_witness(inputs, false).unwrap();
        for (r, w) in res.iter().zip(case.witness) {
            assert_eq!(r, &BigInt::from_str(w).unwrap());
        }
    }
}
