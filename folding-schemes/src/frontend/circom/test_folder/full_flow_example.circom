pragma circom 2.0.3;

/*
    z_{i+1} == z_i^3 + z_i * external_input[0] + external_input[1]
*/
template FullFlowExample () {
    signal input ivc_input[1]; // IVC state
    signal input external_inputs[2]; // not state

    signal output ivc_output[1]; // next IVC state

    signal temp1;
    signal temp2;
    
    temp1 <== ivc_input[0] * ivc_input[0];
    temp2 <== ivc_input[0] * external_inputs[0];
    ivc_output[0] <== temp1 * ivc_input[0] + temp2 + external_inputs[1];
}

component main {public [ivc_input]} = FullFlowExample();