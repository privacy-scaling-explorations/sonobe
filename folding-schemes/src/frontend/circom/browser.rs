use crate::frontend::FCircuit;
use crate::frontend::FpVar::Var;
use crate::Error;
use ark_circom::circom::{CircomCircuit, R1CS as CircomR1CS};
use ark_circom::circom::{R1CSFile, R1CS};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::fmt::Debug;
use byteorder::{LittleEndian, ReadBytesExt};
use std::io::{BufReader, Cursor, Read};
use std::usize;

/// This circuit is the one we will use in order to fold from the browser.
///
/// A clear example on how to do all of this can be seen at:
/// <https://github.com/CPerezz/wasm-sonobe-integration>
#[derive(Clone, Debug)]
pub struct CircomFCircuitBrowser<F: PrimeField> {
    pub state_len: usize,
    pub external_inputs_len: usize,
    pub witness: Vec<F>,
    pub r1cs: CircomR1CS<F>,
}

impl<F: PrimeField> FCircuit<F> for CircomFCircuitBrowser<F> {
    /// (r1cs_file_bytes,  state_len, external_inputs_len)
    type Params = (Vec<u8>, usize, usize);

    fn new(params: Self::Params) -> Result<Self, Error> {
        let (r1cs_bytes, state_len, external_inputs_len) = params;
        let reader = BufReader::new(Cursor::new(&r1cs_bytes[..]));

        let mut r1cs: R1CS<F> = R1CSFile::<F>::new(reader)
            .expect("Error reading R1cs")
            .into();

        // That's some weird magic. Ask @dmpierre
        r1cs.wire_mapping = None;

        Ok(Self {
            state_len,
            external_inputs_len,
            witness: vec![F::zero(); r1cs.num_variables],
            r1cs,
        })
    }

    fn state_len(&self) -> usize {
        self.state_len
    }
    fn external_inputs_len(&self) -> usize {
        self.external_inputs_len
    }

    fn step_native(
        &self,
        _i: usize,
        z_i: Vec<F>,
        external_inputs: Vec<F>,
    ) -> Result<Vec<F>, Error> {
        // Should we keep these?
        assert_eq!(z_i.len(), self.state_len());
        assert_eq!(external_inputs.len(), self.external_inputs_len());

        // Extracts the z_i1(next state) from the witness vector and external inputs.
        let z_i1 = z_i[..self.state_len()].to_vec();
        Ok(z_i1)
    }

    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
        // This in reality contains the `witness` passed from the `prove_step` call from the
        // browser.
        _external_inputs: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        // Since public inputs are already allocated variables, we will tell `circom-compat` to not re-allocate those
        let mut already_allocated_public_inputs = vec![];
        for var in z_i.iter() {
            match var {
                Var(var) => already_allocated_public_inputs.push(var.variable),
                _ => return Err(SynthesisError::Unsatisfiable), // allocated z_i should be Var
            }
        }

        // Initializes the CircomCircuit.
        let circom_circuit = CircomCircuit {
            r1cs: self.r1cs.clone(),
            witness: Some(self.witness.clone()),
            public_inputs_indexes: already_allocated_public_inputs,
            // Since public inputs are already allocated variables, we will tell `circom-compat` to not re-allocate those
            allocate_inputs_as_witnesses: true,
        };

        // Generates the constraints for the circom_circuit.
        circom_circuit.generate_constraints(cs.clone())?;

        // Extracts the z_i1(next state) from the witness vector.
        let z_i1: Vec<FpVar<F>> = Vec::<FpVar<F>>::new_witness(cs.clone(), || {
            Ok(self.witness[1..1 + self.state_len()].to_vec())
        })?;

        Ok(z_i1)
    }

    fn load_witness(&mut self, witness: Vec<F>) {
        self.witness = witness;
    }
}

/// Load Circom-generated witness from u8 array by a reader.
///
/// This fn has been taken from <https://github.com/nalinbhardwaj/Nova-Scotia/blob/main/src/circom/file.rs>
pub fn load_witness_from_bin_reader<R: Read, F: PrimeField>(mut reader: R) -> Vec<F> {
    let mut wtns_header = [0u8; 4];
    reader.read_exact(&mut wtns_header).expect("read_error");
    if wtns_header != [119, 116, 110, 115] {
        panic!("invalid file header");
    }
    let version = reader.read_u32::<LittleEndian>().expect("read_error");
    if version > 2 {
        panic!("unsupported file version");
    }
    let num_sections = reader.read_u32::<LittleEndian>().expect("read_error");
    if num_sections != 2 {
        panic!("invalid num sections");
    }
    // read the first section
    let sec_type = reader.read_u32::<LittleEndian>().expect("read_error");
    if sec_type != 1 {
        panic!("invalid section type");
    }
    let sec_size = reader.read_u64::<LittleEndian>().expect("read_error");
    if sec_size != 4 + 32 + 4 {
        panic!("invalid section len")
    }
    let field_size: u32 = reader.read_u32::<LittleEndian>().expect("read_error");
    if field_size != 32 {
        panic!("invalid field byte size");
    }
    let mut prime = vec![0u8; field_size as usize];
    reader.read_exact(&mut prime).expect("read_error");
    let witness_len: u32 = reader.read_u32::<LittleEndian>().expect("read_error");
    let sec_type = reader.read_u32::<LittleEndian>().expect("read_error");
    if sec_type != 2 {
        panic!("invalid section type");
    }
    let sec_size = reader.read_u64::<LittleEndian>().expect("read_error");
    if sec_size != (witness_len * field_size) as u64 {
        panic!("invalid witness section size");
    }
    let mut result = Vec::with_capacity(witness_len as usize);
    for _ in 0..witness_len {
        result.push(read_field::<&mut R, F>(&mut reader).expect("read_error"));
    }
    result
}

fn read_field<R: Read, F: PrimeField>(
    mut reader: R,
) -> Result<F, ark_serialize::SerializationError> {
    let mut repr: Vec<u8> = F::ZERO.into_bigint().to_bytes_le();
    for digit in repr.iter_mut() {
        *digit = reader.read_u8()?;
    }
    Ok(F::from_le_bytes_mod_order(&repr[..]))
}
