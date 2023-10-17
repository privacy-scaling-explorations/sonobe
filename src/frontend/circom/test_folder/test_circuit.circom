pragma circom 2.0.3;

template Example () {
    signal input step_in;
    signal output step_out;   
    signal temp;
    
    temp <== step_in * step_in;
    step_out <== temp * step_in + step_in + 5;
    step_out === 35; 
}

component main = Example();
