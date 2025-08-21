// From https://github.com/dmpierre/arkworks_backend/tree/feat/sonobe-integration
use std::collections::{BTreeMap, HashMap};
use std::convert::TryInto;

use acvm::acir::{
    acir_field::GenericFieldElement,
    circuit::{Circuit, Opcode, PublicInputs},
    native_types::{Expression, Witness, WitnessMap},
};
use ark_ff::{Field, PrimeField};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::{
    lc,
    gr1cs::{
        ConstraintSynthesizer, ConstraintSystemRef, LinearCombination, SynthesisError, Variable,
    },
};

// AcirCircuit and AcirArithGate are structs that arkworks can synthesise.
//
// The difference between these structures and the ACIR structure that the compiler uses is the following:
// - The compilers ACIR struct is currently fixed to bn254
// - These structures only support arithmetic gates, while the compiler has other
// gate types. These can be added later once the backend knows how to deal with things like XOR
// or once ACIR is taught how to do convert these black box functions to Arithmetic gates.
//
// XXX: Ideally we want to implement `ConstraintSynthesizer` on ACIR however
// this does not seem possible since ACIR is juts a description of the constraint system and the API Asks for prover values also.
//
// Perfect API would look like:
// - index(srs, circ)
// - prove(index_pk, prover_values, rng)
// - verify(index_vk, verifier, rng)
#[derive(Clone)]
pub struct AcirCircuitSonobe<'a, F: Field + PrimeField> {
    pub(crate) gates: Vec<Expression<GenericFieldElement<F>>>,
    pub(crate) public_inputs: PublicInputs,
    pub(crate) values: BTreeMap<Witness, F>,
    pub already_assigned_witnesses: HashMap<Witness, &'a FpVar<F>>,
}

impl<'a, ConstraintF: Field + PrimeField> ConstraintSynthesizer<ConstraintF>
    for AcirCircuitSonobe<'a, ConstraintF>
{
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let mut variables = Vec::with_capacity(self.values.len());

        // First create all of the witness indices by adding the values into the constraint system
        for (i, val) in self.values.iter() {
            let var = if self.already_assigned_witnesses.contains_key(i) {
                let var = self.already_assigned_witnesses.get(i).unwrap();
                if let FpVar::Var(allocated) = var {
                    allocated.variable
                } else {
                    return Err(SynthesisError::Unsatisfiable);
                }
            } else if self.public_inputs.contains(i.0.try_into().unwrap()) {
                cs.new_witness_variable(|| Ok(*val))?
            } else {
                cs.new_witness_variable(|| Ok(*val))?
            };
            variables.push(var);
        }

        // Now iterate each gate and add it to the constraint system
        for gate in self.gates {
            let mut arith_gate = LinearCombination::<ConstraintF>::new();

            // Process mul terms
            for mul_term in gate.mul_terms {
                let coeff = mul_term.0;
                let left_val = self.values[&mul_term.1];
                let right_val = self.values[&mul_term.2];

                let out_val = left_val * right_val;
                let out_var = FpVar::<ConstraintF>::new_witness(cs.clone(), || Ok(out_val))?;
                // out var can't be a type different from FpVar::Var
                if let FpVar::Var(allocated) = out_var {
                    arith_gate += (coeff.into_repr(), allocated.variable);
                }
            }

            // Process Add terms
            for add_term in gate.linear_combinations {
                let coeff = add_term.0;
                let add_var = &variables[add_term.1.as_usize()];
                arith_gate += (coeff.into_repr(), *add_var);
            }

            // Process constant term
            arith_gate += (gate.q_c.into_repr(), Variable::One);

            cs.enforce_r1cs_constraint(|| lc!() + Variable::One, || arith_gate, || lc!())?;
        }

        Ok(())
    }
}

impl<'a, F: PrimeField>
    From<(
        &Circuit<GenericFieldElement<F>>,
        WitnessMap<GenericFieldElement<F>>,
    )> for AcirCircuitSonobe<'a, F>
{
    fn from(
        circ_val: (
            &Circuit<GenericFieldElement<F>>,
            WitnessMap<GenericFieldElement<F>>,
        ),
    ) -> AcirCircuitSonobe<'a, F> {
        // Currently non-arithmetic gates are not supported
        // so we extract all of the arithmetic gates only
        let (circuit, witness_map) = circ_val;

        let public_inputs = circuit.public_inputs();
        let arith_gates: Vec<_> = circuit
            .opcodes
            .iter()
            .filter_map(|opcode| {
                if let Opcode::AssertZero(code) = opcode {
                    Some(code.clone())
                } else {
                    None
                }
            })
            .collect();

        let num_variables: usize = circuit.num_vars().try_into().unwrap();

        let values: BTreeMap<Witness, _> = (0..num_variables)
            .map(|witness_index| {
                // Get the value if it exists. If i does not, then we fill it with the zero value
                let witness = Witness(witness_index as u32);
                let value = witness_map
                    .get(&witness)
                    .map_or(F::zero(), |field| field.into_repr());

                (witness, value)
            })
            .collect();

        AcirCircuitSonobe {
            gates: arith_gates,
            values,
            public_inputs,
            already_assigned_witnesses: HashMap::new(),
        }
    }
}
