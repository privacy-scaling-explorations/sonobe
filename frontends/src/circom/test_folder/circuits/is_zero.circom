pragma circom 2.0.0;
// From: https://github.com/iden3/circomlib/blob/master/circuits/comparators.circom

template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}