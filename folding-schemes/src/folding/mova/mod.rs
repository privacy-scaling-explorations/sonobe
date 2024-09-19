use crate::commitment::CommitmentScheme;
use crate::transcript::AbsorbNonNative;
use crate::utils::mle::dense_vec_to_dense_mle;
use crate::utils::vec::is_zero_vec;
use crate::Error;
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_poly::MultilinearExtension;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{log2, One, UniformRand, Zero};
use rand::RngCore;

/// Implements the scheme described in [Mova](https://eprint.iacr.org/2024/1220.pdf)
mod nifs;
mod pointvsline;
mod traits;

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommittedInstance<C: CurveGroup> {
    // Random evaluation point for the E
    pub rE: Vec<C::ScalarField>,
    // MLE of E
    pub mleE: C::ScalarField,
    pub u: C::ScalarField,
    pub cmW: C,
    pub x: Vec<C::ScalarField>,
}
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Witness<C: CurveGroup> {
    pub E: Vec<C::ScalarField>,
    pub W: Vec<C::ScalarField>,
    pub rW: C::ScalarField,
}

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct InstanceWitness<C: CurveGroup> {
    pub ci: CommittedInstance<C>,
    pub w: Witness<C>,
}

impl<C: CurveGroup> Witness<C>
where
    <C as Group>::ScalarField: Absorb,
{
    pub fn new<const H: bool>(w: Vec<C::ScalarField>, e_len: usize, mut rng: impl RngCore) -> Self {
        let rW = if H {
            C::ScalarField::rand(&mut rng)
        } else {
            C::ScalarField::zero()
        };

        Self {
            E: vec![C::ScalarField::zero(); e_len],
            W: w,
            rW,
        }
    }

    pub fn dummy(w_len: usize, e_len: usize) -> Self {
        let rW  = C::ScalarField::zero();
        let w = vec![C::ScalarField::zero(); w_len];

        Self {
            E: vec![C::ScalarField::zero(); e_len],
            W: w,
            rW,
        }
    }

    pub fn commit<CS: CommitmentScheme<C>>(
        &self,
        params: &CS::ProverParams,
        x: Vec<C::ScalarField>,
        rE: Vec<C::ScalarField>,
    ) -> Result<CommittedInstance<C>, Error> {
        let mut mleE = C::ScalarField::zero();
        if !is_zero_vec::<C::ScalarField>(&self.E) {
            let E = dense_vec_to_dense_mle(log2(self.E.len()) as usize, &self.E);
            mleE = E.evaluate(&rE).ok_or(Error::NotExpectedLength(
                rE.len(),
                log2(self.E.len()) as usize,
            ))?;
        }
        let cmW = CS::commit(params, &self.W, &self.rW)?;
        Ok(CommittedInstance {
            rE,
            mleE,
            u: C::ScalarField::one(),
            cmW,
            x,
        })
    }
}

impl<C: CurveGroup> Absorb for CommittedInstance<C>
where
    C::ScalarField: Absorb,
{
    fn to_sponge_bytes(&self, _dest: &mut Vec<u8>) {
        // This is never called
        unimplemented!()
    }

    fn to_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        self.u.to_sponge_field_elements(dest);
        self.x.to_sponge_field_elements(dest);
        self.rE.to_sponge_field_elements(dest);
        self.mleE.to_sponge_field_elements(dest);
        // We cannot call `to_native_sponge_field_elements(dest)` directly, as
        // `to_native_sponge_field_elements` needs `F` to be `C::ScalarField`,
        // but here `F` is a generic `PrimeField`.
        self.cmW
            .to_native_sponge_field_elements_as_vec()
            .to_sponge_field_elements(dest);
    }
}
