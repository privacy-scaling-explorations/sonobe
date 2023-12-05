use ark_crypto_primitives::sponge::poseidon::{find_poseidon_ark_and_mds, PoseidonConfig};
use ark_ff::Field;
use ark_ff::PrimeField;
use ark_pallas::{Fr, Projective};
use ark_poly::{DenseMultilinearExtension, MultilinearExtension};

use folding_schemes::utils::sum_check::SumCheckGeneric;
use folding_schemes::{
    sum_check_unstable,
    transcript::{poseidon::PoseidonTranscript, Transcript},
    utils::virtual_polynomial::VirtualPolynomial,
};
use std::sync::Arc;
use std::time::Duration;

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

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

fn criterion_benchmark(c: &mut Criterion) {
    let mut rng = ark_std::test_rng();
    let transcript_config = poseidon_test_config();
    let n_vars = 25;
    let poly = DenseMultilinearExtension::<Fr>::rand(n_vars, &mut rng);
    let virtual_poly = VirtualPolynomial::new_from_mle(&Arc::new(poly.clone()), Fr::ONE);

    c.bench_with_input(
        BenchmarkId::new("sumcheck unstable [prove]", "some polynomial"),
        &poly,
        |b, poly| {
            b.iter(|| {
                let mut prover_transcript =
                    PoseidonTranscript::<Projective>::new(&transcript_config);
                let mut verifier_transcript =
                    PoseidonTranscript::<Projective>::new(&transcript_config);
                let mut sumcheck = sum_check_unstable::SumCheck::<Projective>::new(poly);
                sumcheck.prove(&mut prover_transcript).unwrap();
                sumcheck.verify(&mut verifier_transcript).unwrap();
            })
        },
    );

    c.bench_with_input(
        BenchmarkId::new("sumcheck hyperplonk [prove]", "some polynomial"),
        &virtual_poly,
        |b, virtual_poly| {
            b.iter(|| {
                let mut poseidon_transcript_prove: PoseidonTranscript<Projective> =
                    PoseidonTranscript::<Projective>::new(&transcript_config);
                let sum_check =
                    folding_schemes::sum_check::SumCheck::<
                        Projective,
                        PoseidonTranscript<Projective>,
                    >::prove(virtual_poly, &mut poseidon_transcript_prove)
                    .unwrap();
                let claimed_sum = folding_schemes::sum_check::SumCheck::<
                    Projective,
                    PoseidonTranscript<Projective>,
                >::extract_sum(&sum_check);
                let mut poseidon_transcript_verify: PoseidonTranscript<Projective> =
                    PoseidonTranscript::<Projective>::new(&transcript_config);
                let _res_verify = folding_schemes::sum_check::SumCheck::<
                    Projective,
                    PoseidonTranscript<Projective>,
                >::verify(
                    claimed_sum,
                    &sum_check,
                    &virtual_poly.aux_info,
                    &mut poseidon_transcript_verify,
                );
            })
        },
    );
}

criterion_group!(
    name = benches;
    config = Criterion::default()
        .measurement_time(Duration::from_secs(30))
        .sample_size(100);
    targets = criterion_benchmark
);
criterion_main!(benches);
