use color_eyre::Result;
use wasmer::{Function, Instance, Value};

#[derive(Clone, Debug)]
pub struct Wasm(Instance);

pub trait CircomBase {
    fn init(&self, sanity_check: bool) -> Result<()>;
    fn func(&self, name: &str) -> &Function;
    fn get_ptr_witness_buffer(&self) -> Result<u32>;
    fn get_ptr_witness(&self, w: u32) -> Result<u32>;
    fn get_n_vars(&self) -> Result<u32>;
    fn get_signal_offset32(
        &self,
        p_sig_offset: u32,
        component: u32,
        hash_msb: u32,
        hash_lsb: u32,
    ) -> Result<()>;
    fn set_signal(&self, c_idx: u32, component: u32, signal: u32, p_val: u32) -> Result<()>;
    fn get_u32(&self, name: &str) -> Result<u32>;
    // Only exists natively in Circom2, hardcoded for Circom
    fn get_version(&self) -> Result<u32>;
}

pub trait Circom {
    fn get_fr_len(&self) -> Result<u32>;
    fn get_ptr_raw_prime(&self) -> Result<u32>;
}

pub trait Circom2 {
    fn get_field_num_len32(&self) -> Result<u32>;
    fn get_raw_prime(&self) -> Result<()>;
    fn read_shared_rw_memory(&self, i: u32) -> Result<u32>;
    fn write_shared_rw_memory(&self, i: u32, v: u32) -> Result<()>;
    fn set_input_signal(&self, hmsb: u32, hlsb: u32, pos: u32) -> Result<()>;
    fn get_witness(&self, i: u32) -> Result<()>;
    fn get_witness_size(&self) -> Result<u32>;
}

impl Circom for Wasm {
    fn get_fr_len(&self) -> Result<u32> {
        self.get_u32("getFrLen")
    }

    fn get_ptr_raw_prime(&self) -> Result<u32> {
        self.get_u32("getPRawPrime")
    }
}

#[cfg(feature = "circom-2")]
impl Circom2 for Wasm {
    fn get_field_num_len32(&self) -> Result<u32> {
        self.get_u32("getFieldNumLen32")
    }

    fn get_raw_prime(&self) -> Result<()> {
        let func = self.func("getRawPrime");
        func.call(&[])?;
        Ok(())
    }

    fn read_shared_rw_memory(&self, i: u32) -> Result<u32> {
        let func = self.func("readSharedRWMemory");
        let result = func.call(&[i.into()])?;
        Ok(result[0].unwrap_i32() as u32)
    }

    fn write_shared_rw_memory(&self, i: u32, v: u32) -> Result<()> {
        let func = self.func("writeSharedRWMemory");
        func.call(&[i.into(), v.into()])?;
        Ok(())
    }

    fn set_input_signal(&self, hmsb: u32, hlsb: u32, pos: u32) -> Result<()> {
        let func = self.func("setInputSignal");
        func.call(&[hmsb.into(), hlsb.into(), pos.into()])?;
        Ok(())
    }

    fn get_witness(&self, i: u32) -> Result<()> {
        let func = self.func("getWitness");
        func.call(&[i.into()])?;
        Ok(())
    }

    fn get_witness_size(&self) -> Result<u32> {
        self.get_u32("getWitnessSize")
    }
}

impl CircomBase for Wasm {
    fn init(&self, sanity_check: bool) -> Result<()> {
        let func = self.func("init");
        func.call(&[Value::I32(sanity_check as i32)])?;
        Ok(())
    }

    fn get_ptr_witness_buffer(&self) -> Result<u32> {
        self.get_u32("getWitnessBuffer")
    }

    fn get_ptr_witness(&self, w: u32) -> Result<u32> {
        let func = self.func("getPWitness");
        let res = func.call(&[w.into()])?;

        Ok(res[0].unwrap_i32() as u32)
    }

    fn get_n_vars(&self) -> Result<u32> {
        self.get_u32("getNVars")
    }

    fn get_signal_offset32(
        &self,
        p_sig_offset: u32,
        component: u32,
        hash_msb: u32,
        hash_lsb: u32,
    ) -> Result<()> {
        let func = self.func("getSignalOffset32");
        func.call(&[
            p_sig_offset.into(),
            component.into(),
            hash_msb.into(),
            hash_lsb.into(),
        ])?;

        Ok(())
    }

    fn set_signal(&self, c_idx: u32, component: u32, signal: u32, p_val: u32) -> Result<()> {
        let func = self.func("setSignal");
        func.call(&[c_idx.into(), component.into(), signal.into(), p_val.into()])?;

        Ok(())
    }

    // Default to version 1 if it isn't explicitly defined
    fn get_version(&self) -> Result<u32> {
        match self.0.exports.get_function("getVersion") {
            Ok(func) => Ok(func.call(&[])?[0].unwrap_i32() as u32),
            Err(_) => Ok(1),
        }
    }

    fn get_u32(&self, name: &str) -> Result<u32> {
        let func = self.func(name);
        let result = func.call(&[])?;
        Ok(result[0].unwrap_i32() as u32)
    }

    fn func(&self, name: &str) -> &Function {
        self.0
            .exports
            .get_function(name)
            .unwrap_or_else(|_| panic!("function {} not found", name))
    }
}

impl Wasm {
    pub fn new(instance: Instance) -> Self {
        Self(instance)
    }
}
