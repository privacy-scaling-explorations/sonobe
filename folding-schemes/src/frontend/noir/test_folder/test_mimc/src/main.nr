use dep::std;

pub fn main(x: pub [Field; 1]) -> pub Field {
  let hash = std::hash::mimc::mimc_bn254(x);
  hash
}
