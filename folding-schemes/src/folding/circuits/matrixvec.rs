/// Matrix-vector product protocol
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_poly::{
    univariate::{DenseOrSparsePolynomial, DensePolynomial},
    DenseUVPolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial,
};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    bits::uint8::UInt8,
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, nonnative::NonNativeFieldVar, FieldVar},
    groups::GroupOpsBounds,
    prelude::CurveVar,
    ToBitsGadget, ToBytesGadget,
};
use ark_relations::r1cs::SynthesisError;
use ark_std::Zero;
use core::marker::PhantomData;

use super::CF;
use crate::commitment::{
    pedersen::{Params as PedersenParams, Pedersen, PedersenGadget},
    CommitmentProver,
};
use crate::transcript::Transcript;
use crate::utils::vec::{mat_vec_mul_sparse, SparseMatrix};
use crate::Error;

// pub struct Proof<C: CurveGroup> {
//     wip: C,
// }

pub struct MatrixVecGadget<C: CurveGroup, GC: CurveVar<C, CF<C>>> {
    _c: PhantomData<C>,
    _gc: PhantomData<GC>,
}

impl<C, GC> MatrixVecGadget<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF<C>>,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    /// Compute polynomials A_i(X) that interpolate each column of the matrix A.
    /// Return the commitments to the polynomials A_i(X)
    pub fn setup(
        pedersen_params: &PedersenParams<C>,
        A: SparseMatrix<C::ScalarField>,
    ) -> Result<Vec<C>, Error> {
        // let A = A_sparse.to_dense(); // WIP, will get columns directly from cs
        // get columns
        let mut cols: Vec<Vec<C::ScalarField>> =
            vec![vec![C::ScalarField::zero(); A.n_rows]; A.n_cols];
        for (row_i, row) in A.coeffs.iter().enumerate() {
            for (value, col_i) in row.iter() {
                cols[*col_i][row_i] = *value;
            }
        }
        // println!("cols");
        let mut cms = vec![C::zero(); A.n_cols];
        let D =
            GeneralEvaluationDomain::<C::ScalarField>::new(A.n_cols).ok_or(Error::NewDomainFail)?;
        for (i, col) in cols.iter().enumerate() {
            // print_vec(col);
            let A_i = Evaluations::from_vec_and_domain(col.clone(), D).interpolate();
            let r = C::ScalarField::zero(); // blinding factor
            let cm_i = Pedersen::<C>::commit(&pedersen_params, A_i.coeffs(), &r).unwrap();
            cms[i] = cm_i;
        }
        Ok(cms)
    }
    pub fn prove(
        pedersen_params: &PedersenParams<C>,
        // transcript: &mut impl Transcript<C>,
        A: &SparseMatrix<C::ScalarField>,
        z: &[C::ScalarField],
    ) -> Result<(Vec<C::ScalarField>, C), Error> {
        let y = mat_vec_mul_sparse(&A, &z)?;
        let r = C::ScalarField::zero(); // blinding factor
        let D =
            GeneralEvaluationDomain::<C::ScalarField>::new(A.n_cols).ok_or(Error::NewDomainFail)?;
        let y_poly = Evaluations::from_vec_and_domain(y.clone(), D).interpolate();
        let cm_y = Pedersen::<C>::commit(&pedersen_params, y_poly.coeffs(), &r).unwrap();
        // let cm_y = Pedersen::<C>::commit(&pedersen_params, &y, &r).unwrap();
        // let v = y_poly.evaluate(challenge);
        // let proof = Pedersen::<C>::prove(&pedersen_params, transcript, &cm_y, &y_poly.coeffs(), &r)
        //     .unwrap();
        // Ok((y, cm_y, proof))
        Ok((y, cm_y))
    }
    pub fn check_native(
        pedersen_params: &PedersenParams<C>,
        // transcript: &mut impl Transcript<C>,
        // r: C::ScalarField, // random challenge
        cms: Vec<C>, // commitments to polynomials interpolated from A matrix columns
        z: Vec<C::ScalarField>,
        y: Vec<C::ScalarField>, // claimed to be equal to A * z
                                // cm_y: C,
                                // proof: Proof<C>,
    ) -> Result<(), Error> {
        if cms.len() != z.len() {
            return Err(Error::PedersenParamsLen(cms.len(), z.len()));
        }
        let cm_p = C::msm_unchecked(
            &cms.iter()
                .map(|cm| cm.into_affine())
                .collect::<Vec<C::Affine>>(),
            &z,
        );

        let D =
            GeneralEvaluationDomain::<C::ScalarField>::new(z.len()).ok_or(Error::NewDomainFail)?;
        let y_poly = Evaluations::from_vec_and_domain(y.clone(), D).interpolate();
        let cm_y_computed =
            Pedersen::<C>::commit(&pedersen_params, &y_poly, &C::ScalarField::zero()).unwrap();
        assert_eq!(cm_y_computed, cm_p); // probably the unique check needed
        Ok(())
    }
    pub fn check_gadget(
        pedersen_gs: Vec<GC>,
        cms: Vec<GC>,
        z: Vec<NonNativeFieldVar<C::ScalarField, CF<C>>>,
        y: Vec<NonNativeFieldVar<C::ScalarField, CF<C>>>,
    ) -> Result<(), SynthesisError> {
        // cm_p = <cm_A, z>
        let mut cm_p = GC::zero();
        for (i, z_i) in z.iter().enumerate() {
            let bits = z_i.to_bits_le()?;
            cm_p += cms[i].scalar_mul_le(bits.iter())?;
        }
        // pedersen commitment (without blinding)
        let mut cm_y = GC::zero();
        for (i, y_i) in y.iter().enumerate() {
            let bits = y_i.to_bits_le()?;
            cm_y += pedersen_gs[i].scalar_mul_le(bits.iter())?;
        }
        // cm_y.enforce_equal(&cm_p)?;
        cm_p.enforce_equal(&cm_y)?;
        Ok(())
    }
}

fn print_matrix<F: PrimeField>(M: &SparseMatrix<F>) {
    for row in M.to_dense().iter() {
        print_vec(row);
    }
}
fn print_vec<F: PrimeField>(vF: &Vec<F>) {
    let mut v: Vec<String> = vec!["".to_string(); vF.len()];
    for (i, val) in vF.iter().enumerate() {
        v[i] = val.into_bigint().to_string();
    }
    println!("{:?}", v);
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget};
    use ark_relations::r1cs::{
        ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError,
    };
    use ark_std::One;
    use ark_vesta::{constraints::GVar as GVar2, Projective as Projective2};

    use crate::ccs::r1cs::{extract_r1cs, extract_w_x};
    use crate::folding::nova::cyclefold::CycleFoldCircuit;
    use crate::frontend::{
        tests::{CubicFCircuit, WrapperCircuit},
        FCircuit,
    };
    use crate::utils::vec::tests::{to_F_matrix, to_F_vec};

    #[test]
    fn test_matrixvecgadget_small_matrix() {
        let A = to_F_matrix::<Fr>(vec![
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 1, 0, 0, 1, 0],
            vec![5, 0, 0, 0, 0, 1],
        ]);
        let z = to_F_vec(vec![1, 3, 35, 9, 27, 30]);

        test_matrixvec_gadget::<Projective, GVar>(&A, &z);
        test_naive_matrixvec::<Fr, Fq>(&A, &z);
    }

    // cargo test --release folding::circuits::matrixvec::tests::test_matrixvecgadget_cyclefold_matrices -- --nocapture
    #[test]
    fn test_matrixvecgadget_cyclefold_matrices() {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let circuit = CycleFoldCircuit::<Projective2, GVar2>::empty();
        circuit.generate_constraints(cs.clone()).unwrap();
        assert_eq!(cs.num_constraints(), 3758);

        cs.finalize();
        let cs = cs.into_inner().unwrap();
        let r1cs = extract_r1cs::<Fr>(&cs);
        let (w, x) = extract_w_x::<Fr>(&cs);
        let z = [vec![Fr::one()], x, w].concat();

        test_matrixvec_gadget::<Projective, GVar>(&r1cs.A, &z);
        test_naive_matrixvec::<Fr, Fq>(&r1cs.A, &z);
    }

    use ark_crypto_primitives::sponge::Absorb;
    use ark_ec::{CurveGroup, Group};
    fn test_matrixvec_gadget<C: CurveGroup, GC: CurveVar<C, CF<C>>>(
        A: &SparseMatrix<C::ScalarField>,
        z: &Vec<C::ScalarField>,
    ) where
        C: CurveGroup,
        GC: CurveVar<C, CF<C>>,
        <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
        <C as Group>::ScalarField: Absorb,
        for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
    {
        let mut rng = ark_std::test_rng();
        let n = z.len(); // WIP
        let pedersen_params = Pedersen::<C>::new_params(&mut rng, n);

        // print_matrix(&A);
        type MV<C, GC> = MatrixVecGadget<C, GC>;
        let cms_A = MV::setup(&pedersen_params, A.clone()).unwrap();

        // prover, y = A * z
        let (y, cm_y) = MV::prove(&pedersen_params, A, z).unwrap();

        MV::check_native(&pedersen_params, cms_A.clone(), z.clone(), y.clone()).unwrap();

        // check in circuit over Fq
        let cs = ConstraintSystem::<C::BaseField>::new_ref();

        let D = GeneralEvaluationDomain::<C::ScalarField>::new(z.len()).unwrap();
        let y_poly = Evaluations::from_vec_and_domain(y.clone(), D).interpolate();

        let pedersen_gsVar =
            Vec::<GC>::new_witness(cs.clone(), || Ok(pedersen_params.generators.clone())).unwrap();
        let cms_AVar = Vec::<GC>::new_witness(cs.clone(), || Ok(cms_A.clone())).unwrap();
        let zVar: Vec<NonNativeFieldVar<C::ScalarField, CF<C>>> =
            Vec::new_witness(cs.clone(), || Ok(z.clone())).unwrap();
        let yVar: Vec<NonNativeFieldVar<C::ScalarField, CF<C>>> =
            // Vec::new_witness(cs.clone(), || Ok(y.clone())).unwrap();
            Vec::new_witness(cs.clone(), || Ok(y_poly.coeffs())).unwrap(); // TODO

        MV::check_gadget(pedersen_gsVar, cms_AVar, zVar, yVar).unwrap();
        println!(
            "matrixvec_gadget, num_constraints: {}",
            cs.num_constraints()
        );
        assert!(cs.is_satisfied().unwrap());
    }

    fn test_naive_matrixvec<F: PrimeField, CF: PrimeField>(A: &SparseMatrix<F>, z: &Vec<F>) {
        // check in circuit over Fq
        let cs = ConstraintSystem::<CF>::new_ref();

        // set A as circuit constants
        let AVar =
            crate::utils::gadgets::SparseMatrixVar::<F, CF, NonNativeFieldVar<F,CF>>::new_constant(cs.clone(), A).unwrap();
        // set z as witness (private inputs)
        let zVar: Vec<NonNativeFieldVar<F, CF>> =
            Vec::new_witness(cs.clone(), || Ok(z.clone())).unwrap();

        let _Az = crate::utils::gadgets::mat_vec_mul_sparse(AVar, zVar);

        println!("naive_matrixvec, num_constraints: {}", cs.num_constraints());
        assert!(cs.is_satisfied().unwrap());
    }
}
