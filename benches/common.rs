use criterion::*;

use folding_schemes::{
    frontend::{utils::CustomFCircuit, FCircuit},
    Error, FoldingScheme, SonobeCurve,
};

pub(crate) fn bench_ivc_opt<
    C1: SonobeCurve<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    C2: SonobeCurve,
    FS: FoldingScheme<C1, C2, CustomFCircuit<C1::ScalarField>>,
>(
    c: &mut Criterion,
    name: String,
    n: usize,
    prep_param: FS::PreprocessorParam,
) -> Result<(), Error> {
    let fcircuit_size = 1 << n; // 2^n

    let f_circuit = CustomFCircuit::<C1::ScalarField>::new(fcircuit_size)?;

    let mut rng = rand::rngs::OsRng;

    // prepare the FS prover & verifier params
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
        b.iter(|| -> Result<_, _> { black_box(fs.clone()).prove_step(rng, vec![], None) })
    });

    // verify the IVCProof
    let ivc_proof = fs.ivc_proof();
    group.bench_function("verify", |b| {
        b.iter(|| -> Result<_, _> {
            FS::verify(black_box(fs_params.1.clone()), black_box(ivc_proof.clone()))
        })
    });
    group.finish();
    Ok(())
}
