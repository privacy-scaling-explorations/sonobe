pub fn main(x: pub [Field; 1]) -> pub Field {
  let hash = mimc::mimc_bn254(x);
  hash
}
