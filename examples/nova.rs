use std::time::Instant;
use ark_crypto_primitives::sponge::Absorb;
use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_ec::CurveGroup;
use ark_ff::{BigInteger, PrimeField};
use folding_schemes::ccs::r1cs::R1CS;
use folding_schemes::commitment::CommitmentScheme;
use folding_schemes::folding::nova::{CommittedInstance, Witness};
use folding_schemes::folding::nova::circuits::ChallengeGadget;
use folding_schemes::folding::nova::nifs::NIFS;
use folding_schemes::transcript::poseidon::poseidon_canonical_config;
use folding_schemes::commitment::pedersen::{Params as PedersenParams, Pedersen};
use folding_schemes::utils::vec::{dense_matrix_to_sparse, SparseMatrix};
use ark_pallas::{Fr, Projective};
use ark_std::UniformRand;
use folding_schemes::folding::nova::traits::NovaR1CS;
use std::mem;
use std::mem::size_of_val;


fn main(){
    println!("starting");
    let r1cs = get_test_r1cs();
    let z = get_test_z(3);
    let (w, x) = r1cs.split_z(&z);

    let mut rng = ark_std::test_rng();
    let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, r1cs.A.n_cols).unwrap();

    let mut running_instance_w = Witness::<Projective>::new(w.clone(), r1cs.A.n_rows);
    let mut running_committed_instance = running_instance_w
        .commit::<Pedersen<Projective>>(&pedersen_params, x)
        .unwrap();

    let incoming_instance_z = get_test_z( 4);
    let (w, x) = r1cs.split_z(&incoming_instance_z);
    let incoming_instance_w = Witness::<Projective>::new(w.clone(), r1cs.A.n_rows);
    let incoming_committed_instance = incoming_instance_w
        .commit::<Pedersen<Projective>>(&pedersen_params, x)
        .unwrap();

    let r = Fr::rand(&mut rng); // folding challenge would come from the RO

    let start = Instant::now();
    // NIFS.P
    let (T, cmT) = NIFS::<Projective, Pedersen<Projective>>::compute_cmT(
        &pedersen_params,
        &r1cs,
        &running_instance_w,
        &running_committed_instance,
        &incoming_instance_w,
        &incoming_committed_instance,
    )
        .unwrap();
    let result = NIFS::<Projective, Pedersen<Projective>>::fold_instances(
        r,
        &running_instance_w,
        &running_committed_instance,
        &incoming_instance_w,
        &incoming_committed_instance,
        &T,
        cmT,
    ).unwrap();
    println!("Nova prove time {:?}", start.elapsed());
    println!("Nova bytes used {:?}", size_of_val(&result));

    let (folded_w, _) = result;

    let folded_committed_instance = NIFS::<Projective, Pedersen<Projective>>::verify(
        r,
        &running_committed_instance,
        &incoming_committed_instance,
        &cmT,
    );
    r1cs.check_relaxed_instance_relation(&folded_w, &folded_committed_instance)
        .unwrap();
}


#[allow(clippy::type_complexity)]
pub(crate) fn prepare_simple_fold_inputs<C>() -> (
    PedersenParams<C>,
    PoseidonConfig<C::ScalarField>,
    R1CS<C::ScalarField>,
    Witness<C>,           // w1
    CommittedInstance<C>, // ci1
    Witness<C>,           // w2
    CommittedInstance<C>, // ci2
    Witness<C>,           // w3
    CommittedInstance<C>, // ci3
    Vec<C::ScalarField>,  // T
    C,                    // cmT
    Vec<bool>,            // r_bits
    C::ScalarField,       // r_Fr
)
    where
        C: CurveGroup,
        <C as CurveGroup>::BaseField: PrimeField,
        C::ScalarField: Absorb,
{
    let r1cs = get_test_r1cs();
    let z1 = get_test_z(3);
    let z2 = get_test_z(4);
    let (w1, x1) = r1cs.split_z(&z1);
    let (w2, x2) = r1cs.split_z(&z2);

    let w1 = Witness::<C>::new(w1.clone(), r1cs.A.n_rows);
    let w2 = Witness::<C>::new(w2.clone(), r1cs.A.n_rows);

    let mut rng = ark_std::test_rng();
    let (pedersen_params, _) = Pedersen::<C>::setup(&mut rng, r1cs.A.n_cols).unwrap();

    // compute committed instances
    let ci1 = w1
        .commit::<Pedersen<C>>(&pedersen_params, x1.clone())
        .unwrap();
    let ci2 = w2
        .commit::<Pedersen<C>>(&pedersen_params, x2.clone())
        .unwrap();

    // NIFS.P
    let (T, cmT) =
        NIFS::<C, Pedersen<C>>::compute_cmT(&pedersen_params, &r1cs, &w1, &ci1, &w2, &ci2)
            .unwrap();

    let poseidon_config = poseidon_canonical_config::<C::ScalarField>();

    let r_bits = ChallengeGadget::<C>::get_challenge_native(
        &poseidon_config,
        ci1.clone(),
        ci2.clone(),
        cmT,
    )
        .unwrap();
    let r_Fr = C::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits)).unwrap();

    let (w3, ci3) =
        NIFS::<C, Pedersen<C>>::fold_instances(r_Fr, &w1, &ci1, &w2, &ci2, &T, cmT).unwrap();

    (
        pedersen_params,
        poseidon_config,
        r1cs,
        w1,
        ci1,
        w2,
        ci2,
        w3,
        ci3,
        T,
        cmT,
        r_bits,
        r_Fr,
    )
}

pub fn get_test_r1cs<F: PrimeField>() -> R1CS<F> {
    // R1CS for: x^3 + x + 5 = y (example from article
    // https://www.vitalik.ca/general/2016/12/10/qap.html )
    let A = to_F_matrix::<F>(vec![
        vec![0, 1, 0, 0, 0, 0],
        vec![0, 0, 0, 1, 0, 0],
        vec![0, 1, 0, 0, 1, 0],
        vec![5, 0, 0, 0, 0, 1],
    ]);
    let B = to_F_matrix::<F>(vec![
        vec![0, 1, 0, 0, 0, 0],
        vec![0, 1, 0, 0, 0, 0],
        vec![1, 0, 0, 0, 0, 0],
        vec![1, 0, 0, 0, 0, 0],
    ]);
    let C = to_F_matrix::<F>(vec![
        vec![0, 0, 0, 1, 0, 0],
        vec![0, 0, 0, 0, 1, 0],
        vec![0, 0, 0, 0, 0, 1],
        vec![0, 0, 1, 0, 0, 0],
    ]);

    R1CS::<F> { l: 1, A, B, C }
}

pub fn get_test_z<F: PrimeField>(input: usize) -> Vec<F> {
    // z = (1, io, w)
    to_F_vec(vec![
        1,
        input,                             // io
        input * input * input + input + 5, // x^3 + x + 5
        input * input,                     // x^2
        input * input * input,             // x^2 * x
        input * input * input + input,     // x^3 + x
    ])
}

pub fn to_F_matrix<F: PrimeField>(M: Vec<Vec<usize>>) -> SparseMatrix<F> {
    dense_matrix_to_sparse(to_F_dense_matrix(M))
}
pub fn to_F_dense_matrix<F: PrimeField>(M: Vec<Vec<usize>>) -> Vec<Vec<F>> {
    M.iter()
        .map(|m| m.iter().map(|r| F::from(*r as u64)).collect())
        .collect()
}
pub fn to_F_vec<F: PrimeField>(z: Vec<usize>) -> Vec<F> {
    z.iter().map(|c| F::from(*c as u64)).collect()
}


