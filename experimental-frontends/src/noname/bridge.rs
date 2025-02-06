// From https://github.com/dmpierre/ark-noname/tree/feat/sonobe-integration
use std::collections::HashMap;

use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystemRef, LinearCombination, SynthesisError, Variable,
};
use noname::backends::{
    r1cs::{GeneratedWitness, LinearCombination as NoNameLinearCombination, R1CS},
    BackendField,
};
use noname::witness::CompiledCircuit;
use num_bigint::BigUint;

pub struct NonameSonobeCircuit<'a, 'b, 'c, F: PrimeField, BF: BackendField> {
    pub compiled_circuit: CompiledCircuit<R1CS<BF>>,
    pub witness: GeneratedWitness<BF>,
    pub assigned_z_i: &'a Vec<FpVar<F>>,
    pub assigned_external_inputs: &'b Vec<FpVar<F>>,
    pub assigned_z_i1: &'c Vec<FpVar<F>>,
}

impl<'a, 'b, 'c, F: PrimeField, BF: BackendField> ConstraintSynthesizer<F>
    for NonameSonobeCircuit<'a, 'b, 'c, F, BF>
{
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let public_io_length = self.assigned_z_i.len() * 2;
        let external_inputs_len = self.assigned_external_inputs.len();

        // we need to map noname r1cs indexes with sonobe
        let mut idx_to_var = HashMap::new();

        // for both the  z_i, z_i1 vectors, we assume that they have been assigned in the order
        // with which it will appear in the witness
        let mut z_i_pointer = 0;
        let mut z_i1_pointer = 0;
        let mut external_inputs_pointer = 0;

        // arkworks assigns by default the 1 constant
        // assumes witness is: [1, public_outputs, public_inputs, private_inputs, aux]
        let witness_size = self.witness.witness.len();
        for idx in 1..witness_size {
            if idx <= public_io_length {
                if idx <= self.assigned_z_i.len() {
                    // in noname public outputs come first
                    // we are in the case of public outputs (z_i1 vector)
                    // those have already been assigned at specific indexes by sonobe
                    let var = match &self.assigned_z_i1[z_i1_pointer] {
                        FpVar::Var(allocated_fp) => allocated_fp.variable,
                        _ => return Err(SynthesisError::Unsatisfiable),
                    };
                    idx_to_var.insert(idx, var);
                    z_i1_pointer += 1;
                } else {
                    // we are in the case of public inputs (z_i values)
                    // those have already been assigned at specific indexes by sonobe
                    let var = match &self.assigned_z_i[z_i_pointer] {
                        FpVar::Var(allocated_fp) => allocated_fp.variable,
                        _ => return Err(SynthesisError::Unsatisfiable),
                    };
                    idx_to_var.insert(idx, var);
                    z_i_pointer += 1;
                }
            } else if idx <= public_io_length + external_inputs_len {
                // we are in the case of external inputs
                // those have already been assigned at specific indexes
                let var = match &self.assigned_external_inputs[external_inputs_pointer] {
                    FpVar::Var(allocated_fp) => allocated_fp.variable,
                    _ => return Err(SynthesisError::Unsatisfiable),
                };
                idx_to_var.insert(idx, var);
                external_inputs_pointer += 1;
            } else {
                // we are in the case of auxiliary private inputs
                // we need to assign those
                let value: BigUint = Into::into(self.witness.witness[idx]);
                let field_element = F::from(value);
                let var = cs.new_witness_variable(|| Ok(field_element))?;
                idx_to_var.insert(idx, var);
            }
        }

        if (z_i_pointer != self.assigned_z_i.len())
            || (external_inputs_pointer != self.assigned_external_inputs.len())
        {
            return Err(SynthesisError::AssignmentMissing);
        }
        let make_index = |index: usize| match index == 0 {
            true => Ok(Variable::One),
            false => {
                let var = idx_to_var
                    .get(&index)
                    .ok_or(SynthesisError::AssignmentMissing)?;
                Ok(var.to_owned())
            }
        };

        let make_lc = |lc_data: NoNameLinearCombination<BF>| {
            let mut lc = LinearCombination::<F>::zero();
            for (cellvar, coeff) in lc_data.terms.into_iter() {
                let idx = make_index(cellvar.index)?;
                let coeff = F::from(Into::<BigUint>::into(coeff));

                lc += (coeff, idx)
            }

            // add constant
            let constant = F::from(Into::<BigUint>::into(lc_data.constant));
            lc += (constant, make_index(0)?);
            Ok(lc)
        };

        for constraint in self.compiled_circuit.circuit.backend.constraints {
            cs.enforce_constraint(
                make_lc(constraint.a)?,
                make_lc(constraint.b)?,
                make_lc(constraint.c)?,
            )?;
        }

        Ok(())
    }
}
