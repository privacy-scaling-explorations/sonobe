pragma circom 2.0.3;

include "./circuits/is_zero.circom";

template NoExternalInputs () {
    signal input ivc_input[3];
    signal output ivc_output[3];

    component check_input = IsZero();
    check_input.in <== ivc_input[0];
    check_input.out === 0;

    signal temp1;
    signal temp2;
    
    temp1 <== ivc_input[0] * ivc_input[1];
    temp2 <== temp1 * ivc_input[2];
    ivc_output[0] <== temp1 * ivc_input[0];
    ivc_output[1] <== temp1 * ivc_input[1] + temp1;
    ivc_output[2] <== temp1 * ivc_input[2] + temp2;
}

component main {public [ivc_input]} = NoExternalInputs();
