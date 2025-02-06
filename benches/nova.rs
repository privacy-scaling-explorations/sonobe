use criterion::*;
use pprof::criterion::{Output, PProfProfiler};

use ark_bn254::{Fr as bn_Fr, G1Projective as bn_G};
use ark_grumpkin::Projective as grumpkin_G;
use ark_pallas::{Fr as pallas_Fr, Projective as pallas_G};
use ark_vesta::Projective as vesta_G;

use folding_schemes::{
    commitment::pedersen::Pedersen,
    folding::nova::{Nova, PreprocessorParam},
    frontend::{utils::CustomFCircuit, FCircuit},
    transcript::poseidon::poseidon_canonical_config,
};

mod common;
use common::bench_ivc_opt;

fn bench_nova_ivc(c: &mut Criterion) {
    let poseidon_config = poseidon_canonical_config::<pallas_Fr>();

    // iterate over the powers of n
    for n in [0_usize, 14, 16, 18, 19, 20, 21, 22].iter() {
        let fcircuit_size = 1 << n; // 2^n
        let fcircuit = CustomFCircuit::<pallas_Fr>::new(fcircuit_size).unwrap();
        let prep_param = PreprocessorParam::new(poseidon_config.clone(), fcircuit);

        bench_ivc_opt::<
            pallas_G,
            vesta_G,
            Nova<
                pallas_G,
                vesta_G,
                CustomFCircuit<pallas_Fr>,
                Pedersen<pallas_G>,
                Pedersen<vesta_G>,
                false,
            >,
        >(c, "Nova - Pallas-Vesta curves".to_string(), *n, prep_param)
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
            Nova<
                bn_G,
                grumpkin_G,
                CustomFCircuit<bn_Fr>,
                Pedersen<bn_G>,
                Pedersen<grumpkin_G>,
                false,
            >,
        >(
            c,
            "Nova - BN254-Grumpkin curves".to_string(),
            *n,
            prep_param,
        )
        .unwrap();
    }
}

criterion_group! {
    name = benches;
    config = Criterion::default().with_profiler(PProfProfiler::new(100, Output::Flamegraph(None)));
    targets = bench_nova_ivc
}
criterion_main!(benches);
