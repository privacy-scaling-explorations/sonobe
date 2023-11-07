// used for r, so when computing r^2 it does not overflow the field
pub const N_BITS_CHALLENGE: usize = 128;
// used for committed instances hash, so when going to the other curve of the cycle it does not
// overflow the scalar field
pub const N_BITS_HASH: usize = 250;
