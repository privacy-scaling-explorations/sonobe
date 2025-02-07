use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_pallas::{Fr, Projective};
use ark_std::{log2, UniformRand};
use criterion::{criterion_group, criterion_main, Criterion};
use folding_schemes::commitment::pedersen::Pedersen;
use folding_schemes::commitment::CommitmentScheme;
use folding_schemes::folding::nova::nifs::mova_matrix::{RelaxedCommittedRelation, Witness, NIFS};
use folding_schemes::transcript::poseidon::poseidon_canonical_config;
use folding_schemes::utils::vec::{mat_mat_mul_dense};
use folding_schemes::Curve;
use rand::RngCore;
use std::time::Duration;

const NUM_OF_PRECONDITION_FOLDS: &[usize] = &[1, 10, 100, 1000];

fn get_instances<C: Curve, CS: CommitmentScheme<C>>(
    num: usize,
    n: usize,
    rng: &mut impl RngCore,
    params: &CS::ProverParams,
) -> Vec<(Witness<C>, RelaxedCommittedRelation<C>)> {
    (0..num)
        .map(|_| -> (Witness<C>, RelaxedCommittedRelation<C>) {
            // A matrix
            let a: Vec<C::ScalarField> = (0..n * n).map(|_| C::ScalarField::rand(rng)).collect();
            // B matrix
            let b: Vec<C::ScalarField> = (0..n * n).map(|_| C::ScalarField::rand(rng)).collect();
            // C = A * B matrix
            let c: Vec<C::ScalarField> = mat_mat_mul_dense(&a, &b).unwrap();
            // Error matrix initialized to 0s
            let e: Vec<C::ScalarField> = (0..n * n).map(|_| C::ScalarField::from(0)).collect();
            // Random challenge
            let r_e = (0..2 * log2(n))
                .map(|_| C::ScalarField::rand(rng))
                .collect();
            // Witness
            let witness = Witness::new::<false>(a, b, c, e);
            let instance = witness.commit::<CS, false>(params, r_e).unwrap();
            (witness, instance)
        })
        .collect()
}

fn bench_mova_matrix(c: &mut Criterion) {
    let mut group = c.benchmark_group("mova_matrix_single_fold");
    let mut rng = ark_std::test_rng();
    let mat_dim = 4; // 4x4 matrices

    // Set up transcript and commitment scheme
    let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, mat_dim * mat_dim).unwrap();
    let poseidon_config = poseidon_canonical_config::<Fr>();
    let mut transcript_p = PoseidonSponge::<Fr>::new(&poseidon_config);
    let pp_hash = Fr::rand(&mut rng);

    for count in NUM_OF_PRECONDITION_FOLDS {
        let mut instances: Vec<(Witness<Projective>, RelaxedCommittedRelation<Projective>)> =
            get_instances::<Projective, Pedersen<Projective>>(
                count + 1, // we want the number of folds plus one for the acc_instance
                mat_dim,
                &mut rng,
                &pedersen_params,
            );

        // Keep track of the accumulated state
        let mut current_acc_wit = instances.remove(0).0;
        let mut current_acc_inst = instances.remove(0).1;
        group.bench_function("Placeholder ID", |b| {
            b.iter(|| {
                for (next_w, next_i) in instances.clone() {
                    // Fold
                    let (wit_acc, inst_acc, _, _) =
                        NIFS::<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>::prove(
                            &mut transcript_p,
                            pp_hash,
                            &next_w,
                            &next_i,
                            &current_acc_wit,
                            &current_acc_inst,
                        )
                        .unwrap();

                    // Update state for next iteration
                    current_acc_wit = wit_acc;
                    current_acc_inst = inst_acc;
                }
            })
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
