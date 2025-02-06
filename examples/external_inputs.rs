#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(clippy::upper_case_acronyms)]

use ark_bn254::{Bn254, Fr, G1Projective as Projective};
use ark_crypto_primitives::{
    crh::{
        poseidon::constraints::{CRHGadget, CRHParametersVar},
        CRHSchemeGadget,
    },
    sponge::{poseidon::PoseidonConfig, Absorb},
};
use ark_ff::PrimeField;
use ark_grumpkin::Projective as Projective2;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use core::marker::PhantomData;
use std::time::Instant;

use folding_schemes::commitment::{kzg::KZG, pedersen::Pedersen};
use folding_schemes::folding::nova::{Nova, PreprocessorParam};
use folding_schemes::frontend::FCircuit;
use folding_schemes::transcript::poseidon::poseidon_canonical_config;
use folding_schemes::{Error, FoldingScheme};

/// This is the circuit that we want to fold, it implements the FCircuit trait. The parameter z_i
/// denotes the current state which contains 1 element, and z_{i+1} denotes the next state which we
/// get by applying the step.
///
/// In this example we set the state to be the previous state together with an external input, and
/// the new state is an array which contains the new state.
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
///  ────────►│ │                  ├───────►      
///   z_i     │ └──►z_{i+1}=[h]    │  z_{i+1}
///           │                    │              
///           └────────────────────┘
///
/// where each w_i value is set at the external_inputs array.
///
/// The last state z_i is used together with the external input w_i as inputs to compute the new
/// state z_{i+1}.
#[derive(Clone, Debug)]
pub struct ExternalInputsCircuit<F: PrimeField>
where
    F: Absorb,
{
    _f: PhantomData<F>,
    poseidon_config: PoseidonConfig<F>,
}
impl<F: PrimeField> FCircuit<F> for ExternalInputsCircuit<F>
where
    F: Absorb,
{
    type Params = PoseidonConfig<F>;
    type ExternalInputs = [F; 1];
    type ExternalInputsVar = [FpVar<F>; 1];

    fn new(params: Self::Params) -> Result<Self, Error> {
        Ok(Self {
            _f: PhantomData,
            poseidon_config: params,
        })
    }
    fn state_len(&self) -> usize {
        1
    }
    /// generates the constraints and returns the next state value for the step of F for the given
    /// z_i and external_inputs
    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
        external_inputs: Self::ExternalInputsVar,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let crh_params =
            CRHParametersVar::<F>::new_constant(cs.clone(), self.poseidon_config.clone())?;
        let hash_input: [FpVar<F>; 2] = [z_i[0].clone(), external_inputs[0].clone()];
        let h = CRHGadget::<F>::evaluate(&crh_params, &hash_input)?;
        Ok(vec![h])
    }
}

/// cargo test --example external_inputs
#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_crypto_primitives::crh::{poseidon::CRH, CRHScheme};
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::ConstraintSystem;

    fn external_inputs_step_native<F: PrimeField + Absorb>(
        z_i: Vec<F>,
        external_inputs: Vec<F>,
        poseidon_config: &PoseidonConfig<F>,
    ) -> Vec<F> {
        let hash_input: [F; 2] = [z_i[0], external_inputs[0]];
        let h = CRH::<F>::evaluate(poseidon_config, hash_input).unwrap();
        vec![h]
    }

    // test to check that the ExternalInputsCircuit computes the same values inside and outside the circuit
    #[test]
    fn test_f_circuit() -> Result<(), Error> {
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let cs = ConstraintSystem::<Fr>::new_ref();

        let circuit = ExternalInputsCircuit::<Fr>::new(poseidon_config.clone())?;
        let z_i = vec![Fr::from(1_u32)];
        let external_inputs = vec![Fr::from(3_u32)];

        let z_i1 =
            external_inputs_step_native(z_i.clone(), external_inputs.clone(), &poseidon_config);

        let z_iVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i))?;
        let external_inputsVar: [FpVar<Fr>; 1] =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(external_inputs))?
                .try_into()
                .unwrap();

        let computed_z_i1Var =
            circuit.generate_step_constraints(cs.clone(), 0, z_iVar, external_inputsVar)?;
        assert_eq!(computed_z_i1Var.value()?, z_i1);
        Ok(())
    }
}

/// cargo run --release --example external_inputs
fn main() -> Result<(), Error> {
    let num_steps = 5;
    let initial_state = vec![Fr::from(1_u32)];

    // prepare the external inputs to be used at each folding step
    let external_inputs = vec![
        [Fr::from(3_u32)],
        [Fr::from(33_u32)],
        [Fr::from(73_u32)],
        [Fr::from(103_u32)],
        [Fr::from(125_u32)],
    ];
    assert_eq!(external_inputs.len(), num_steps);

    let poseidon_config = poseidon_canonical_config::<Fr>();
    let F_circuit = ExternalInputsCircuit::<Fr>::new(poseidon_config.clone())?;

    /// The idea here is that eventually we could replace the next line chunk that defines the
    /// `type N = Nova<...>` by using another folding scheme that fulfills the `FoldingScheme`
    /// trait, and the rest of our code would be working without needing to be updated.
    type N = Nova<
        Projective,
        Projective2,
        ExternalInputsCircuit<Fr>,
        KZG<'static, Bn254>,
        Pedersen<Projective2>,
        false,
    >;

    let mut rng = rand::rngs::OsRng;

    println!("Prepare Nova's ProverParams & VerifierParams");
    let nova_preprocess_params = PreprocessorParam::new(poseidon_config, F_circuit.clone());
    let nova_params = N::preprocess(&mut rng, &nova_preprocess_params)?;

    println!("Initialize FoldingScheme");
    let mut folding_scheme = N::init(&nova_params, F_circuit, initial_state.clone())?;

    // compute a step of the IVC
    for (i, external_inputs_at_step) in external_inputs.iter().enumerate() {
        let start = Instant::now();
        folding_scheme.prove_step(rng, external_inputs_at_step.clone(), None)?;
        println!("Nova::prove_step {}: {:?}", i, start.elapsed());
    }
    println!(
        "state at last step (after {} iterations): {:?}",
        num_steps,
        folding_scheme.state()
    );

    println!("Run the Nova's IVC verifier");
    let ivc_proof = folding_scheme.ivc_proof();
    N::verify(
        nova_params.1, // Nova's verifier params
        ivc_proof,
    )?;
    Ok(())
}
