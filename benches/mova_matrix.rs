use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_pallas::{Fr, Projective};
use ark_std::{log2, UniformRand};
use criterion::{criterion_group, criterion_main, Criterion};
use folding_schemes::commitment::pedersen::Pedersen;
use folding_schemes::commitment::CommitmentScheme;
use folding_schemes::folding::nova::nifs::mova_matrix::{RelaxedCommittedRelation, Witness, NIFS};
use folding_schemes::transcript::poseidon::poseidon_canonical_config;
use folding_schemes::Curve;
use matrex::Matrix;
use rand::{Rng, RngCore};
use std::time::{Duration, Instant};

const NUM_OF_PRECONDITION_FOLDS: &[usize] = &[1, 10, 20, 40];

fn random_sparse_matrix<C: Curve>(n: usize, rng: &mut impl RngCore) -> Matrix<C::ScalarField> {
    let elements = (0..n)
        .map(|row| {
            (
                row * n + rand::thread_rng().gen_range(0..n),
                C::ScalarField::rand(rng),
            )
        })
        .collect();
    Matrix::sparse_from_vec(elements, n, n).unwrap()
}

// Helper functions
fn get_instances<C: Curve, CS: CommitmentScheme<C>>(
    num: usize,
    n: usize,
    rng: &mut impl RngCore,
    params: &CS::ProverParams,
) -> Vec<(Witness<C>, RelaxedCommittedRelation<C>)> {
    (0..num)
        .map(|_| -> (Witness<C>, RelaxedCommittedRelation<C>) {
            // A matrix
            let a = random_sparse_matrix::<C>(n, rng);
            // B matrix
            let b = random_sparse_matrix::<C>(n, rng);
            // C = A * B matrix
            let c = (a.clone() * &b).unwrap();
            // Error matrix initialized to 0s
            let e = Matrix::zero(n, n);
            // Random challenge
            let rE = (0..2 * log2(n))
                .map(|_| C::ScalarField::rand(rng))
                .collect();
            // Witness
            let witness = Witness::new::<false>(a, b, c, e);
            let instance = witness.commit::<CS, false>(params, rE).unwrap();
            (witness, instance)
        })
        .collect()
}

fn bench_mova_matrix(c: &mut Criterion) {
    let mut group = c.benchmark_group("mova_matrix_sequential_folding");
    let mut rng = ark_std::test_rng();
    let mat_dim = 4; // 4x4 matrices

    for count in NUM_OF_PRECONDITION_FOLDS {
        group
            .measurement_time(Duration::from_secs(20 * (*count as u64)))
            .bench_function(&format!("{count}"), |b| {
                // Set up transcript and commitment scheme
                let (pedersen_params, _) =
                    Pedersen::<Projective>::setup(&mut rng, mat_dim * mat_dim).unwrap();
                let poseidon_config = poseidon_canonical_config::<Fr>();
                let pp_hash = Fr::rand(&mut rng);

                b.iter_custom(|iters| {
                    let mut total_duration = Duration::ZERO;
                    for _ in 0..iters {
                        let mut instances: Vec<(
                            Witness<Projective>,
                            RelaxedCommittedRelation<Projective>,
                        )> = get_instances::<Projective, Pedersen<Projective>>(
                            count + 1, // we want the number of folds plus one for the acc_instance
                            mat_dim,
                            &mut rng,
                            &pedersen_params,
                        );
                        let mut transcript_p = PoseidonSponge::<Fr>::new(&poseidon_config);
                        let mut acc = instances.pop().unwrap();

                        for _ in 0..*count {
                            let next = instances.pop().unwrap();
                            total_duration += {
                                let timer = Instant::now();
                                let (wit_acc, inst_acc, _) = NIFS::<
                                    Projective,
                                    Pedersen<Projective>,
                                    PoseidonSponge<Fr>,
                                >::prove(
                                    &mut transcript_p,
                                    pp_hash,
                                    &next.0,
                                    &next.1,
                                    &acc.0,
                                    &acc.1,
                                )
                                .unwrap();
                                let time = timer.elapsed();
                                acc = (wit_acc, inst_acc);
                                time
                            };
                        }
                    }
                    total_duration
                });
            });
    }
}

fn custom_criterion() -> Criterion {
    Criterion::default()
        .measurement_time(Duration::from_secs(100))
        .sample_size(10)
}

criterion_group! {
    name = benches;
    config = custom_criterion();
    targets = bench_mova_matrix
}
criterion_main!(benches);
