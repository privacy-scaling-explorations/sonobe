fn main(public_inputs: pub [Field; 2], private_inputs: [Field; 2]) -> pub [Field; 2]{
     let a_pub = public_inputs[0];
     let b_pub = public_inputs[1];
     let c_private = private_inputs[0];
     let d_private = private_inputs[1];

     let out_1 = a_pub * c_private;
     let out_2 = b_pub * d_private;

     [out_1, out_2]
}
