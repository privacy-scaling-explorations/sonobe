pub fn bit_decompose(input: u64, n: usize) -> Vec<bool> {
    let mut res = Vec::with_capacity(n);
    let mut i = input;
    for _ in 0..n {
        res.push(i & 1 == 1);
        i >>= 1;
    }
    res
}
