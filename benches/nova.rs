use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use criterion::*;

use ark_bn254::{constraints::GVar as bn_GVar, Fr as bn_Fr, G1Projective as bn_G};
use ark_grumpkin::{constraints::GVar as grumpkin_GVar, Projective as grumpkin_G};
use ark_pallas::{constraints::GVar as pallas_GVar, Fr as pallas_Fr, Projective as pallas_G};
use ark_vesta::{constraints::GVar as vesta_GVar, Projective as vesta_G};

use folding_schemes::{
    commitment::pedersen::Pedersen,
    folding::nova::{Nova, PreprocessorParam},
    frontend::{utils::CustomFCircuit, FCircuit},
    transcript::poseidon::poseidon_canonical_config,
    Error, FoldingScheme,
};

fn bench_nova_ivc(c: &mut Criterion) {
    bench_nova_ivc_opt::<
        pallas_G,
        vesta_G,
        Nova<
            pallas_G,
            pallas_GVar,
            vesta_G,
            vesta_GVar,
            CustomFCircuit<pallas_Fr>,
            Pedersen<pallas_G>,
            Pedersen<vesta_G>,
            false,
        >,
    >(c, "Nova - Pallas-Vesta curves".to_string())
    .unwrap();

    bench_nova_ivc_opt::<
        bn_G,
        grumpkin_G,
        Nova<
            bn_G,
            bn_GVar,
            grumpkin_G,
            grumpkin_GVar,
            CustomFCircuit<bn_Fr>,
            Pedersen<bn_G>,
            Pedersen<grumpkin_G>,
            false,
        >,
    >(c, "Nova - BN254-Grumpkin curves".to_string())
    .unwrap();
}
fn bench_nova_ivc_opt<
    C1: CurveGroup,
    C2: CurveGroup,
    FS: FoldingScheme<
        C1,
        C2,
        CustomFCircuit<C1::ScalarField>,
        PreprocessorParam = PreprocessorParam<
            C1,
            C2,
            CustomFCircuit<C1::ScalarField>,
            Pedersen<C1>,
            Pedersen<C2>,
            false,
        >,
    >,
>(
    c: &mut Criterion,
    name: String,
) -> Result<(), Error>
where
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    C2::BaseField: PrimeField,
{
    // iterate over the powers of n
    for n in [10, 14, 15, 16, 17, 18, 19, 20].iter() {
        let fcircuit_size = 1 << n; // 2^n

        let f_circuit = CustomFCircuit::<C1::ScalarField>::new(fcircuit_size)?;

        let poseidon_config = poseidon_canonical_config::<C1::ScalarField>();
        let mut rng = rand::rngs::OsRng;

        // prepare the Nova prover & verifier params
        let prep_param: FS::PreprocessorParam =
            PreprocessorParam::new(poseidon_config.clone(), f_circuit);
        let fs_params = FS::preprocess(&mut rng, &prep_param)?;

        let z_0 = vec![C1::ScalarField::from(3_u32)];
        let mut fs = FS::init(&fs_params, f_circuit, z_0)?;

        // warmup steps
        for _ in 0..5 {
            fs.prove_step(rng, vec![], None)?;
        }

        let mut group = c.benchmark_group(format!(
            "{} - FCircuit: {} (2^{}) constraints",
            name, fcircuit_size, n
        ));
        group.significance_level(0.1).sample_size(10);
        group.bench_function("prove_step", |b| {
            b.iter(|| fs.prove_step(rng, vec![], None).unwrap())
        });

        // verify the IVCProof
        let ivc_proof = fs.ivc_proof();
        group.bench_function("verify", |b| {
            b.iter(|| FS::verify(fs_params.1.clone(), ivc_proof.clone()).unwrap())
        });
        group.finish();
    }
    Ok(())
}

criterion_group!(benches, bench_nova_ivc);
criterion_main!(benches);
