use criterion::*;

use ark_bn254::{constraints::GVar as bn_GVar, Fr as bn_Fr, G1Projective as bn_G};
use ark_grumpkin::{constraints::GVar as grumpkin_GVar, Projective as grumpkin_G};
use ark_pallas::{constraints::GVar as pallas_GVar, Fr as pallas_Fr, Projective as pallas_G};
use ark_vesta::{constraints::GVar as vesta_GVar, Projective as vesta_G};

use folding_schemes::{
    commitment::pedersen::Pedersen,
    folding::{hypernova::HyperNova, nova::PreprocessorParam},
    frontend::{utils::CustomFCircuit, FCircuit},
    transcript::poseidon::poseidon_canonical_config,
};

mod common;
use common::bench_ivc_opt;

fn bench_hypernova_ivc(c: &mut Criterion) {
    let poseidon_config = poseidon_canonical_config::<pallas_Fr>();

    // iterate over the powers of n
    for n in [0_usize, 14, 16, 18, 19, 20, 21, 22].iter() {
        let fcircuit_size = 1 << n; // 2^n
        let fcircuit = CustomFCircuit::<pallas_Fr>::new(fcircuit_size).unwrap();
        let prep_param = PreprocessorParam::new(poseidon_config.clone(), fcircuit);

        bench_ivc_opt::<
            pallas_G,
            vesta_G,
            HyperNova<
                pallas_G,
                pallas_GVar,
                vesta_G,
                vesta_GVar,
                CustomFCircuit<pallas_Fr>,
                Pedersen<pallas_G>,
                Pedersen<vesta_G>,
                1,
                1,
                false,
            >,
        >(
            c,
            "HyperNova - Pallas-Vesta curves".to_string(),
            *n,
            prep_param,
        )
        .unwrap();
    }

    let poseidon_config = poseidon_canonical_config::<bn_Fr>();
    for n in [0_usize, 14, 16, 18, 19, 20, 21, 22].iter() {
        let fcircuit_size = 1 << n; // 2^n
        let fcircuit = CustomFCircuit::<bn_Fr>::new(fcircuit_size).unwrap();
        let prep_param = PreprocessorParam::new(poseidon_config.clone(), fcircuit);

        bench_ivc_opt::<
            bn_G,
            grumpkin_G,
            HyperNova<
                bn_G,
                bn_GVar,
                grumpkin_G,
                grumpkin_GVar,
                CustomFCircuit<bn_Fr>,
                Pedersen<bn_G>,
                Pedersen<grumpkin_G>,
                1,
                1,
                false,
            >,
        >(
            c,
            "HyperNova - BN254-Grumpkin curves".to_string(),
            *n,
            prep_param,
        )
        .unwrap();
    }
}

criterion_group!(benches, bench_hypernova_ivc);
criterion_main!(benches);
