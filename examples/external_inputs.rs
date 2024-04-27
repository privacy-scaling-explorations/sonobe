#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(clippy::upper_case_acronyms)]

use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as Projective};
use ark_crypto_primitives::{
    crh::{
        poseidon::constraints::{CRHGadget, CRHParametersVar},
        poseidon::CRH,
        CRHScheme, CRHSchemeGadget,
    },
    sponge::{poseidon::PoseidonConfig, Absorb},
};
use ark_ff::PrimeField;
use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::{alloc::AllocVar, fields::FieldVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_std::Zero;
use core::marker::PhantomData;
use std::time::Instant;

use folding_schemes::commitment::{kzg::KZG, pedersen::Pedersen};
use folding_schemes::folding::nova::Nova;
use folding_schemes::frontend::FCircuit;
use folding_schemes::{Error, FoldingScheme};
mod utils;
use folding_schemes::transcript::poseidon::poseidon_test_config;
use utils::init_nova_ivc_params;

/// This is the circuit that we want to fold, it implements the FCircuit trait. The parameter z_i
/// denotes the current state which contains 2 elements, and z_{i+1} denotes the next state which
/// we get by applying the step.
///
/// In this example we set the state to be the previous state together with an external input, and
/// the new state is an array which contains the new state and a zero which will be ignored.
///
/// This is useful for example if we want to fold multiple verifications of signatures, where the
/// circuit F checks the signature and is folded for each of the signatures and public keys. To
/// keep things simpler, the following example does not verify signatures but does a similar
/// approach with a chain of hashes, where each iteration hashes the previous step output (z_i)
/// together with an external input (w_i).
///
///        w_1     w_2     w_3     w_4     
///        │       │       │       │      
///        ▼       ▼       ▼       ▼      
///       ┌─┐     ┌─┐     ┌─┐     ┌─┐     
/// ─────►│F├────►│F├────►│F├────►│F├────►
///  z_1  └─┘ z_2 └─┘ z_3 └─┘ z_4 └─┘ z_5
///
///
/// where each F is:
///    w_i                                        
///     │     ┌────────────────────┐              
///     │     │FCircuit            │              
///     │     │                    │              
///     └────►│ h =Hash(z_i[0],w_i)│              
///           │ │ =Hash(v, w_i)    │              
///  ────────►│ │                  ├───────►      
/// z_i=[v,0] │ └──►z_{i+1}=[h, 0] │ z_{i+1}=[h,0]
///           │                    │              
///           └────────────────────┘
///
/// where each w_i value is set at the external_inputs array.
///
/// The last state z_i is used together with the external input w_i as inputs to compute the new
/// state z_{i+1}.
/// The function F will output the new state in an array of two elements, where the second element
/// is a 0. In other words, z_{i+1} = [F([z_i, w_i]), 0], and the 0 will be replaced by w_{i+1} in
/// the next iteration, so z_{i+2} = [F([z_{i+1}, w_{i+1}]), 0].
#[derive(Clone, Debug)]
pub struct ExternalInputsCircuits<F: PrimeField>
where
    F: Absorb,
{
    _f: PhantomData<F>,
    poseidon_config: PoseidonConfig<F>,
    // external_inputs: Vec<F>,
}
impl<F: PrimeField> FCircuit<F> for ExternalInputsCircuits<F>
where
    F: Absorb,
{
    type Params = PoseidonConfig<F>;

    fn new(params: Self::Params) -> Self {
        Self {
            _f: PhantomData,
            poseidon_config: params,
        }
    }
    fn state_len(&self) -> usize {
        2
    }
    fn external_inputs_len(&self) -> usize {
        1
    }

    /// computes the next state values in place, assigning z_{i+1} into z_i, and computing the new
    /// z_{i+1}
    fn step_native(
        &self,
        _i: usize,
        z_i: Vec<F>,
        external_inputs: Vec<F>,
    ) -> Result<Vec<F>, Error> {
        let input: [F; 2] = [z_i[0], external_inputs[0]];
        let h = CRH::<F>::evaluate(&self.poseidon_config, input).unwrap();
        Ok(vec![h, F::zero()])
    }

    /// generates the constraints for the step of F for the given z_i
    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
        external_inputs: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let crh_params =
            CRHParametersVar::<F>::new_constant(cs.clone(), self.poseidon_config.clone())?;
        let input: [FpVar<F>; 2] = [z_i[0].clone(), external_inputs[0].clone()];
        let h = CRHGadget::<F>::evaluate(&crh_params, &input)?;
        Ok(vec![h, FpVar::<F>::zero()])
    }
}

/// cargo test --example external_inputs
#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::ConstraintSystem;

    // test to check that the ExternalInputsCircuits computes the same values inside and outside the circuit
    #[test]
    fn test_f_circuit() {
        let poseidon_config = poseidon_test_config::<Fr>();

        let cs = ConstraintSystem::<Fr>::new_ref();

        let circuit = ExternalInputsCircuits::<Fr>::new((poseidon_config, vec![Fr::from(3_u32)]));
        let z_i = vec![Fr::from(1_u32), Fr::zero()];
        let external_inputs = vec![Fr::from(3_u32)];

        let z_i1 = circuit.step_native(0, z_i.clone()).unwrap();

        let z_iVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i)).unwrap();
        let external_inputsVar =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(external_inputs)).unwrap();

        let computed_z_i1Var = circuit
            .generate_step_constraints(cs.clone(), 0, z_iVar, external_inputsVar)
            .unwrap();
        assert_eq!(computed_z_i1Var.value().unwrap(), z_i1);
    }
}

/// cargo run --release --example external_inputs
fn main() {
    let num_steps = 5;
    let initial_state = vec![Fr::from(1_u32), Fr::zero()];

    // prepare the external inputs to be used at each folding step
    let external_inputs = vec![
        vec![Fr::from(3_u32)],
        vec![Fr::from(33_u32)],
        vec![Fr::from(73_u32)],
        vec![Fr::from(103_u32)],
        vec![Fr::from(125_u32)],
    ];
    assert_eq!(external_inputs.len(), num_steps);

    let poseidon_config = poseidon_test_config::<Fr>();
    let F_circuit = ExternalInputsCircuits::<Fr>::new(poseidon_config);

    println!("Prepare Nova ProverParams & VerifierParams");
    let (prover_params, verifier_params, _) =
        init_nova_ivc_params::<ExternalInputsCircuits<Fr>>(F_circuit.clone());

    /// The idea here is that eventually we could replace the next line chunk that defines the
    /// `type NOVA = Nova<...>` by using another folding scheme that fulfills the `FoldingScheme`
    /// trait, and the rest of our code would be working without needing to be updated.
    type NOVA = Nova<
        Projective,
        GVar,
        Projective2,
        GVar2,
        ExternalInputsCircuits<Fr>,
        KZG<'static, Bn254>,
        Pedersen<Projective2>,
    >;

    println!("Initialize FoldingScheme");
    let mut folding_scheme = NOVA::init(&prover_params, F_circuit, initial_state.clone()).unwrap();

    // compute a step of the IVC
    for (i, external_inputs_at_step) in external_inputs.iter().enumerate() {
        let start = Instant::now();
        folding_scheme
            .prove_step(external_inputs_at_step.clone())
            .unwrap();
        println!("Nova::prove_step {}: {:?}", i, start.elapsed());
    }
    println!(
        "state at last step (after {} iterations): {:?}",
        num_steps,
        folding_scheme.state()
    );

    let (running_instance, incoming_instance, cyclefold_instance) = folding_scheme.instances();

    println!("Run the Nova's IVC verifier");
    NOVA::verify(
        verifier_params,
        initial_state.clone(),
        folding_scheme.state(), // latest state
        Fr::from(num_steps as u32),
        running_instance,
        incoming_instance,
        cyclefold_instance,
    )
    .unwrap();
}
