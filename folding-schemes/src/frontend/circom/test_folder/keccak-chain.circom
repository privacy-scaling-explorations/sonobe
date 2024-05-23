pragma circom 2.0.0;

include "./keccak256-circom/circuits/keccak.circom";

template KeccakChain () {
    signal input ivc_input[8];
    signal output ivc_output[8];   

    component keccak = Keccak(8, 8);

    for (var i=0; i<8; i++) {
        keccak.in[i] <== ivc_input[i];
    }
    for (var i=0; i<8; i++) {
    	ivc_output[i] <== keccak.out[i];
    }
}

component main { public [ivc_input] } = KeccakChain();