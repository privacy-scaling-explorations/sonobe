use ark_ec::CurveGroup;
use ark_ff::{Field, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use core::{borrow::Borrow, marker::PhantomData};

use crate::ccs::r1cs::RelaxedR1CS;
use crate::utils::vec::SparseMatrix;

pub type ConstraintF<C> = <<C as CurveGroup>::BaseField as Field>::BasePrimeField;

#[derive(Debug, Clone)]
pub struct RelaxedR1CSGadget<F: PrimeField> {
    _f: PhantomData<F>,
}
impl<F: PrimeField> RelaxedR1CSGadget<F> {
    /// performs the RelaxedR1CS check (Az∘Bz==uCz+E)
    pub fn check(rel_r1cs: RelaxedR1CSVar<F>, z: Vec<FpVar<F>>) -> Result<(), SynthesisError> {
        let Az = mat_vec_mul_sparse(rel_r1cs.A, z.clone());
        let Bz = mat_vec_mul_sparse(rel_r1cs.B, z.clone());
        let Cz = mat_vec_mul_sparse(rel_r1cs.C, z.clone());
        let uCz = vec_scalar_mul(&Cz, &rel_r1cs.u);
        let uCzE = vec_add(&uCz, &rel_r1cs.E);
        let AzBz = hadamard(&Az, &Bz);
        for i in 0..AzBz.len() {
            AzBz[i].enforce_equal(&uCzE[i].clone())?;
        }
        Ok(())
    }
}

fn mat_vec_mul_sparse<F: PrimeField>(m: SparseMatrixVar<F>, v: Vec<FpVar<F>>) -> Vec<FpVar<F>> {
    let mut res = vec![FpVar::<F>::zero(); m.n_rows];
    for (row_i, row) in m.coeffs.iter().enumerate() {
        for (value, col_i) in row.iter() {
            res[row_i] += value * v[*col_i].clone();
        }
    }
    res
}
pub fn vec_add<F: PrimeField>(a: &Vec<FpVar<F>>, b: &Vec<FpVar<F>>) -> Vec<FpVar<F>> {
    assert_eq!(a.len(), b.len());
    let mut r: Vec<FpVar<F>> = vec![FpVar::<F>::zero(); a.len()];
    for i in 0..a.len() {
        r[i] = a[i].clone() + b[i].clone();
    }
    r
}
pub fn vec_scalar_mul<F: PrimeField>(vec: &Vec<FpVar<F>>, c: &FpVar<F>) -> Vec<FpVar<F>> {
    let mut result = vec![FpVar::<F>::zero(); vec.len()];
    for (i, a) in vec.iter().enumerate() {
        result[i] = a.clone() * c;
    }
    result
}
pub fn hadamard<F: PrimeField>(a: &Vec<FpVar<F>>, b: &Vec<FpVar<F>>) -> Vec<FpVar<F>> {
    assert_eq!(a.len(), b.len());
    let mut r: Vec<FpVar<F>> = vec![FpVar::<F>::zero(); a.len()];
    for i in 0..a.len() {
        r[i] = a[i].clone() * b[i].clone();
    }
    r
}

#[derive(Debug, Clone)]
pub struct SparseMatrixVar<F: PrimeField> {
    pub n_rows: usize,
    pub n_cols: usize,
    // same format as the native SparseMatrix (which follows ark_relations::r1cs::Matrix format
    pub coeffs: Vec<Vec<(FpVar<F>, usize)>>,
}

impl<F> AllocVar<SparseMatrix<F>, F> for SparseMatrixVar<F>
where
    F: PrimeField,
{
    fn new_variable<T: Borrow<SparseMatrix<F>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let mut coeffs: Vec<Vec<(FpVar<F>, usize)>> = Vec::new();
            for row in val.borrow().coeffs.iter() {
                let mut rowVar: Vec<(FpVar<F>, usize)> = Vec::new();
                for &(value, col_i) in row.iter() {
                    let coeffVar = FpVar::<F>::new_variable(cs.clone(), || Ok(value), mode)?;
                    rowVar.push((coeffVar, col_i));
                }
                coeffs.push(rowVar);
            }

            Ok(Self {
                n_rows: val.borrow().n_rows,
                n_cols: val.borrow().n_cols,
                coeffs,
            })
        })
    }
}

#[derive(Debug, Clone)]
pub struct RelaxedR1CSVar<F: PrimeField> {
    pub A: SparseMatrixVar<F>,
    pub B: SparseMatrixVar<F>,
    pub C: SparseMatrixVar<F>,
    pub u: FpVar<F>,
    pub E: Vec<FpVar<F>>,
}

impl<F> AllocVar<RelaxedR1CS<F>, F> for RelaxedR1CSVar<F>
where
    F: PrimeField,
{
    fn new_variable<T: Borrow<RelaxedR1CS<F>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let A = SparseMatrixVar::<F>::new_constant(cs.clone(), &val.borrow().A)?;
            let B = SparseMatrixVar::<F>::new_constant(cs.clone(), &val.borrow().B)?;
            let C = SparseMatrixVar::<F>::new_constant(cs.clone(), &val.borrow().C)?;
            let E = Vec::<FpVar<F>>::new_variable(cs.clone(), || Ok(val.borrow().E.clone()), mode)?;
            let u = FpVar::<F>::new_variable(cs.clone(), || Ok(val.borrow().u), mode)?;

            Ok(Self { A, B, C, E, u })
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_crypto_primitives::crh::{
        sha256::{
            constraints::{Sha256Gadget, UnitVar},
            Sha256,
        },
        CRHScheme, CRHSchemeGadget,
    };
    use ark_ff::BigInteger;
    use ark_pallas::Fr;
    use ark_r1cs_std::{alloc::AllocVar, bits::uint8::UInt8};
    use ark_relations::r1cs::{
        ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError,
    };
    use ark_std::One;

    use crate::ccs::r1cs::{
        tests::{get_test_r1cs, get_test_z},
        R1CS,
    };
    use crate::frontend::arkworks::{extract_r1cs_and_z, tests::TestCircuit};

    #[test]
    fn test_relaxed_r1cs_small_gadget_handcrafted() {
        let r1cs: R1CS<Fr> = get_test_r1cs();
        let rel_r1cs = r1cs.relax();
        let z = get_test_z(3);

        let cs = ConstraintSystem::<Fr>::new_ref();

        let zVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z)).unwrap();
        let rel_r1csVar = RelaxedR1CSVar::<Fr>::new_witness(cs.clone(), || Ok(rel_r1cs)).unwrap();

        RelaxedR1CSGadget::<Fr>::check(rel_r1csVar, zVar).unwrap();
        assert!(cs.is_satisfied().unwrap());
        dbg!(cs.num_constraints());
    }

    // gets as input a circuit that implements the ConstraintSynthesizer trait, and that has been
    // initialized.
    fn test_relaxed_r1cs_gadget<CS: ConstraintSynthesizer<Fr>>(circuit: CS) {
        let cs = ConstraintSystem::<Fr>::new_ref();

        circuit.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        assert!(cs.is_satisfied().unwrap());

        // num constraints of the original circuit
        dbg!(cs.num_constraints());

        let cs = cs.into_inner().unwrap();

        let (r1cs, z) = extract_r1cs_and_z::<Fr>(&cs);
        r1cs.check_relation(&z).unwrap();

        let relaxed_r1cs = r1cs.relax();
        relaxed_r1cs.check_relation(&z).unwrap();

        // set new CS for the circuit that checks the RelaxedR1CS of our original circuit
        let cs = ConstraintSystem::<Fr>::new_ref();
        // prepare the inputs for our circuit
        let zVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z)).unwrap();
        let rel_r1csVar =
            RelaxedR1CSVar::<Fr>::new_witness(cs.clone(), || Ok(relaxed_r1cs)).unwrap();

        RelaxedR1CSGadget::<Fr>::check(rel_r1csVar, zVar).unwrap();
        assert!(cs.is_satisfied().unwrap());

        // num constraints of the circuit that checks the RelaxedR1CS of the original circuit
        dbg!(cs.num_constraints());
    }

    #[test]
    fn test_relaxed_r1cs_small_gadget_arkworks() {
        let x = Fr::from(5_u32);
        let y = x * x * x + x + Fr::from(5_u32);
        let circuit = TestCircuit::<Fr> { x, y };
        test_relaxed_r1cs_gadget(circuit);
    }

    struct Sha256TestCircuit<F: PrimeField> {
        _f: PhantomData<F>,
        pub x: Vec<u8>,
        pub y: Vec<u8>,
    }
    impl<F: PrimeField> ConstraintSynthesizer<F> for Sha256TestCircuit<F> {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let x = Vec::<UInt8<F>>::new_witness(cs.clone(), || Ok(self.x))?;
            let y = Vec::<UInt8<F>>::new_input(cs.clone(), || Ok(self.y))?;

            let unitVar = UnitVar::default();
            let comp_y = <Sha256Gadget<F> as CRHSchemeGadget<Sha256, F>>::evaluate(&unitVar, &x)?;
            comp_y.0.enforce_equal(&y)?;
            Ok(())
        }
    }
    #[test]
    fn test_relaxed_r1cs_medium_gadget_arkworks() {
        let x = Fr::from(5_u32).into_bigint().to_bytes_le();
        let y = <Sha256 as CRHScheme>::evaluate(&(), x.clone()).unwrap();

        let circuit = Sha256TestCircuit::<Fr> {
            _f: PhantomData,
            x,
            y,
        };
        test_relaxed_r1cs_gadget(circuit);
    }

    // circuit that has the numer of constraints specified in the `n_constraints` parameter. Note
    // that the generated circuit will have very sparse matrices, so the resulting constraints
    // number of the RelaxedR1CS gadget must take that into account.
    struct CustomTestCircuit<F: PrimeField> {
        _f: PhantomData<F>,
        pub n_constraints: usize,
        pub x: F,
        pub y: F,
    }
    impl<F: PrimeField> ConstraintSynthesizer<F> for CustomTestCircuit<F> {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let x = FpVar::<F>::new_witness(cs.clone(), || Ok(self.x))?;
            let y = FpVar::<F>::new_input(cs.clone(), || Ok(self.y))?;

            let mut comp_y = FpVar::<F>::new_witness(cs.clone(), || Ok(F::one()))?;
            for _ in 0..self.n_constraints - 1 {
                comp_y *= x.clone();
            }

            comp_y.enforce_equal(&y)?;
            Ok(())
        }
    }
    #[test]
    fn test_relaxed_r1cs_custom_circuit() {
        let n_constraints = 10_000;
        let x = Fr::from(5_u32);
        let mut y = Fr::one();
        for _ in 0..n_constraints - 1 {
            y *= x;
        }

        let circuit = CustomTestCircuit::<Fr> {
            _f: PhantomData,
            n_constraints,
            x,
            y,
        };
        test_relaxed_r1cs_gadget(circuit);
    }
}
