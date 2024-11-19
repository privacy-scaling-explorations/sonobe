pragma circom 2.0.3;

include "./circuits/is_zero.circom";

template WithExternalInputs () {
    signal input ivc_input[1];
    signal input external_inputs[2];
    signal output ivc_output[1];

    component check_input = IsZero();
    check_input.in <== ivc_input[0];
    check_input.out === 0;

    signal temp1;
    signal temp2;
    
    temp1 <== ivc_input[0] * ivc_input[0];
    temp2 <== ivc_input[0] * external_inputs[0];
    ivc_output[0] <== temp1 * ivc_input[0] + temp2 + external_inputs[1];
}

component main {public [ivc_input]} = WithExternalInputs();