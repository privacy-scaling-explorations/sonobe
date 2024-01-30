#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(clippy::upper_case_acronyms)]

use ark_crypto_primitives::crh::{
    sha256::{
        constraints::{Sha256Gadget, UnitVar},
        Sha256,
    },
    CRHScheme, CRHSchemeGadget,
};
use ark_crypto_primitives::sponge::poseidon::{find_poseidon_ark_and_mds, PoseidonConfig};
use ark_ff::{BigInteger, PrimeField, ToConstraintField};
use ark_r1cs_std::{fields::fp::FpVar, ToBytesGadget, ToConstraintFieldGadget};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use core::marker::PhantomData;
use std::time::Instant;

use ark_pallas::{constraints::GVar, Fr, Projective};
use ark_vesta::{constraints::GVar as GVar2, Projective as Projective2};

use folding_schemes::commitment::pedersen::Pedersen;
use folding_schemes::folding::nova::{get_both_r1cs, Nova, ProverParams, VerifierParams};
use folding_schemes::frontend::FCircuit;
use folding_schemes::{Error, FoldingScheme};

/// This is the circuit that we want to fold, it implements the FCircuit trait
#[derive(Clone, Copy, Debug)]
pub struct Sha256FCircuit<F: PrimeField> {
    _f: PhantomData<F>,
}
impl<F: PrimeField> FCircuit<F> for Sha256FCircuit<F> {
    type Params = ();
    fn new(_params: Self::Params) -> Self {
        Self { _f: PhantomData }
    }
    fn step_native(self, z_i: Vec<F>) -> Result<Vec<F>, Error> {
        let out_bytes = Sha256::evaluate(&(), z_i[0].into_bigint().to_bytes_le()).unwrap();
        let out: Vec<F> = out_bytes.to_field_elements().unwrap();

        Ok(vec![out[0]])
    }
    fn generate_step_constraints(
        self,
        _cs: ConstraintSystemRef<F>,
        z_i: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let unit_var = UnitVar::default();
        let out_bytes = Sha256Gadget::evaluate(&unit_var, &z_i[0].to_bytes()?)?;
        let out = out_bytes.0.to_constraint_field()?;
        Ok(vec![out[0].clone()])
    }
}

pub fn poseidon_test_config<F: PrimeField>() -> PoseidonConfig<F> {
    let full_rounds = 8;
    let partial_rounds = 31;
    let alpha = 5;
    let rate = 2;

    let (ark, mds) = find_poseidon_ark_and_mds::<F>(
        F::MODULUS_BIT_SIZE as u64,
        rate,
        full_rounds,
        partial_rounds,
        0,
    );

    PoseidonConfig::new(
        full_rounds as usize,
        partial_rounds as usize,
        alpha,
        mds,
        ark,
        rate,
        1,
    )
}

/// cargo test --example simple
#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_relations::r1cs::ConstraintSystem;

    // test to check that the Sha256FCircuit computes the same values inside and outside the circuit
    #[test]
    fn test_sha256_f_circuit() {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let circuit = Sha256FCircuit::<Fr>::new(());
        let z_i = vec![Fr::from(1_u32)];

        let z_i1 = circuit.step_native(z_i.clone()).unwrap();

        let z_iVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i)).unwrap();
        let computed_z_i1Var = circuit
            .generate_step_constraints(cs.clone(), z_iVar.clone())
            .unwrap();
        assert_eq!(computed_z_i1Var.value().unwrap(), z_i1);
    }
}

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
        get_both_r1cs::<Projective, GVar, Projective2, GVar2, FC>(&poseidon_config, F_circuit)
            .unwrap();
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

/// cargo run --release --example simple
fn main() {
    let num_steps = 10;
    let initial_state = vec![Fr::from(1_u32)];

    let F_circuit = Sha256FCircuit::<Fr>::new(());

    println!("Prepare Nova ProverParams & VerifierParams");
    let (prover_params, verifier_params) = nova_setup::<Sha256FCircuit<Fr>>(F_circuit);

    // The idea here is that eventually we could replace the next line chunk that defines the
    // `type NOVA = Nova<...>` by using another folding scheme that fulfills the `FoldingScheme`
    // trait, and the rest of our code would be working without needing to be updated.
    type NOVA = Nova<
        Projective,
        GVar,
        Projective2,
        GVar2,
        Sha256FCircuit<Fr>,
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
        initial_state,
        folding_scheme.state(), // latest state
        Fr::from(num_steps as u32),
        running_instance,
        incomming_instance,
        cyclefold_instance,
    )
    .unwrap();
}
