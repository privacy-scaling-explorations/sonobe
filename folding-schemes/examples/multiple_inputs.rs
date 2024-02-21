#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(clippy::upper_case_acronyms)]

use ark_ff::PrimeField;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use core::marker::PhantomData;
use std::time::Instant;

use ark_pallas::{constraints::GVar, Fr, Projective};
use ark_vesta::{constraints::GVar as GVar2, Projective as Projective2};

use folding_schemes::commitment::pedersen::Pedersen;
use folding_schemes::folding::nova::{get_r1cs, Nova, ProverParams, VerifierParams};
use folding_schemes::frontend::FCircuit;
use folding_schemes::transcript::poseidon::poseidon_test_config;
use folding_schemes::{Error, FoldingScheme};

/// This is the circuit that we want to fold, it implements the FCircuit trait. The parameter z_i
/// denotes the current state which contains 5 elements, and z_{i+1} denotes the next state which
/// we get by applying the step.
/// In this example we set z_i and z_{i+1} to have five elements, and at each step we do different
/// operations on each of them.
#[derive(Clone, Copy, Debug)]
pub struct MultipleAddFCircuit<F: PrimeField> {
    _f: PhantomData<F>,
}
impl<F: PrimeField> FCircuit<F> for MultipleAddFCircuit<F> {
    type Params = ();

    fn new(_params: Self::Params) -> Self {
        Self { _f: PhantomData }
    }
    fn state_len(self) -> usize {
        5
    }

    /// computes the next state values in place, assigning z_{i+1} into z_i, and computing the new
    /// z_{i+1}
    fn step_native(self, z_i: Vec<F>) -> Result<Vec<F>, Error> {
        let a = z_i[0] + F::from(4_u32);
        let b = z_i[1] + F::from(40_u32);
        let c = z_i[2] * F::from(4_u32);
        let d = z_i[3] * F::from(40_u32);
        let e = z_i[4] + F::from(100_u32);

        Ok(vec![a, b, c, d, e])
    }

    /// generates the constraints for the step of F for the given z_i
    fn generate_step_constraints(
        self,
        cs: ConstraintSystemRef<F>,
        z_i: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let four = FpVar::<F>::new_constant(cs.clone(), F::from(4u32))?;
        let fourty = FpVar::<F>::new_constant(cs.clone(), F::from(40u32))?;
        let onehundred = FpVar::<F>::new_constant(cs.clone(), F::from(100u32))?;
        let a = z_i[0].clone() + four.clone();
        let b = z_i[1].clone() + fourty.clone();
        let c = z_i[2].clone() * four;
        let d = z_i[3].clone() * fourty;
        let e = z_i[4].clone() + onehundred;

        Ok(vec![a, b, c, d, e])
    }
}

/// cargo test --example simple
#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_relations::r1cs::ConstraintSystem;

    // test to check that the MultipleAddFCircuit computes the same values inside and outside the circuit
    #[test]
    fn test_add_f_circuit() {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let circuit = MultipleAddFCircuit::<Fr>::new(());
        let z_i = vec![
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
        ];

        let z_i1 = circuit.step_native(z_i.clone()).unwrap();

        let z_iVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i)).unwrap();
        let computed_z_i1Var = circuit
            .generate_step_constraints(cs.clone(), z_iVar.clone())
            .unwrap();
        assert_eq!(computed_z_i1Var.value().unwrap(), z_i1);
    }
}

// This method computes the Prover & Verifier parameters for the example. For a real world use case
// those parameters should be generated carefuly (both the PoseidonConfig and the PedersenParams)
#[allow(clippy::type_complexity)]
fn nova_setup<FC: FCircuit<Fr>>(
    F_circuit: FC,
) -> (
    ProverParams<Projective, Projective2, Pedersen<Projective>, Pedersen<Projective2>>,
    VerifierParams<Projective, Projective2>,
) {
    let mut rng = ark_std::test_rng();
    let poseidon_config = poseidon_test_config::<Fr>();

    // get the CM & CF_CM len
    let (r1cs, cf_r1cs) =
        get_r1cs::<Projective, GVar, Projective2, GVar2, FC>(&poseidon_config, F_circuit).unwrap();
    let cm_len = r1cs.A.n_rows;
    let cf_cm_len = cf_r1cs.A.n_rows;

    let pedersen_params = Pedersen::<Projective>::new_params(&mut rng, cm_len);
    let cf_pedersen_params = Pedersen::<Projective2>::new_params(&mut rng, cf_cm_len);

    let prover_params =
        ProverParams::<Projective, Projective2, Pedersen<Projective>, Pedersen<Projective2>> {
            poseidon_config: poseidon_config.clone(),
            cm_params: pedersen_params,
            cf_cm_params: cf_pedersen_params,
        };
    let verifier_params = VerifierParams::<Projective, Projective2> {
        poseidon_config: poseidon_config.clone(),
        r1cs,
        cf_r1cs,
    };
    (prover_params, verifier_params)
}

/// cargo run --release --example multiple_inputs
fn main() {
    let num_steps = 10;
    let initial_state = vec![
        Fr::from(1_u32),
        Fr::from(1_u32),
        Fr::from(1_u32),
        Fr::from(1_u32),
        Fr::from(1_u32),
    ];

    let F_circuit = MultipleAddFCircuit::<Fr>::new(());

    println!("Prepare Nova ProverParams & VerifierParams");
    let (prover_params, verifier_params) = nova_setup::<MultipleAddFCircuit<Fr>>(F_circuit);

    /// The idea here is that eventually we could replace the next line chunk that defines the
    /// `type NOVA = Nova<...>` by using another folding scheme that fulfills the `FoldingScheme`
    /// trait, and the rest of our code would be working without needing to be updated.
    type NOVA = Nova<
        Projective,
        GVar,
        Projective2,
        GVar2,
        MultipleAddFCircuit<Fr>,
        Pedersen<Projective>,
        Pedersen<Projective2>,
    >;

    println!("Initialize FoldingScheme");
    let mut folding_scheme = NOVA::init(&prover_params, F_circuit, initial_state.clone()).unwrap();

    // compute a step of the IVC
    for i in 0..num_steps {
        let start = Instant::now();
        folding_scheme.prove_step().unwrap();
        println!("Nova::prove_step {}: {:?}", i, start.elapsed());
    }

    let (running_instance, incomming_instance, cyclefold_instance) = folding_scheme.instances();

    println!("Run the Nova's IVC verifier");
    NOVA::verify(
        verifier_params,
        initial_state.clone(),
        folding_scheme.state(), // latest state
        Fr::from(num_steps as u32),
        running_instance,
        incomming_instance,
        cyclefold_instance,
    )
    .unwrap();
}
