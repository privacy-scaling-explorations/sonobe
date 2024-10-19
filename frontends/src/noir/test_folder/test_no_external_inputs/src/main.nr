fn main(public_inputs: pub [Field; 2]) -> pub [Field; 2]{
     let a_pub = public_inputs[0];
     let b_pub = public_inputs[1];
     let out_1 = a_pub * a_pub;
     let out_2 = b_pub * b_pub;

     [out_1, out_2]
}

