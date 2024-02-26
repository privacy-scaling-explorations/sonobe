#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(clippy::upper_case_acronyms)]
#![allow(dead_code)]
use ark_pallas::{constraints::GVar, Fr, Projective};
use ark_vesta::{constraints::GVar as GVar2, Projective as Projective2};

use folding_schemes::commitment::pedersen::Pedersen;
use folding_schemes::folding::nova::{get_r1cs, ProverParams, VerifierParams};
use folding_schemes::frontend::FCircuit;
use folding_schemes::transcript::poseidon::poseidon_test_config;

// This method computes the Prover & Verifier parameters for the example.
// Warning: this method is only for testing purposes. For a real world use case those parameters
// should be generated carefully (both the PoseidonConfig and the PedersenParams).
#[allow(clippy::type_complexity)]
pub(crate) fn test_nova_setup<FC: FCircuit<Fr>>(
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
fn main() {}
