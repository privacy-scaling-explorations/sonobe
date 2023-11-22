use ark_ec::CurveGroup;

use crate::transcript::Transcript;

pub trait SumCheck<C: CurveGroup, T: Transcript<C>> {
    fn prove();
    fn verify();    
}
