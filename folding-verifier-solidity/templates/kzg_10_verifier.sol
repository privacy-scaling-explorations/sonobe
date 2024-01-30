// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "./BN254.sol";

contract KZG10 {

    uint256[2] G_1 = [
            {{ g1.0[0] }},
            {{ g1.0[1] }}
    ];
    uint256[2][2] G_2 = [
        [
            {{ g2.0[0] }},
            {{ g2.0[1] }},
        ],
        [
            {{ g2.1[0] }},
            {{ g2.1[1] }},
        ]
    ];
    uint256[2][2] VK = [
        [
            {{ vk.0[0] }},
            {{ vk.0[1] }}
        ],
        [
            {{ vk.1[0] }},
            {{ vk.1[1] }}
        ]
    ];

    uint256[2][{{ g1_crs_len }}] G1_CRS;

    {% for (i, point) in g1_crs.iter().enumerate() %}
        G1_CRS[{{ i }}] = [ 
            {{ point.0[0] }},
            {{ point.0[1] }}
        ];
    {% endfor %}    

    /**
     * @notice  Verifies a single point evaluation proof. Function name follows `ark-poly`.
     * @dev     To avoid ops in G_2, we slightly tweak how the verification is done.
     * @param   c  G_1 point commitment to polynomial.
     * @param   pi G_1 point proof.
     * @param   x  Value to prove evaluation of polynomial at.
     * @param   y  Evaluation poly(x).
     * @return  result Indicates if KZG proof is correct.
     */
    function check(uint256[2] calldata c, uint256[2] calldata pi, uint256 x, uint256 y)
        external
        view
        returns (bool result)
    {
        //
        // we want to:
        //      1. avoid gas intensive ops in G2
        //      2. format the pairing check in line with what the evm opcode expects.
        //
        // we can do this by tweaking the KZG check to be:
        //
        //          e(pi, vk - x * g2) = e(c - y * g1, g2) [initial check]
        //          e(pi, vk - x * g2) * e(c - y * g1, g2)^{-1} = 1
        //          e(pi, vk - x * g2) * e(-c + y * g1, g2) = 1 [bilinearity of pairing for all subsequent steps]
        //          e(pi, vk) * e(pi, -x * g2) * e(-c + y * g1, g2) = 1
        //          e(pi, vk) * e(-x * pi, g2) * e(-c + y * g1, g2) = 1
        //          e(pi, vk) * e(x * -pi - c + y * g1, g2) = 1 [done]
        //                        |_   rhs_pairing  _|
        //
        uint256[2] memory rhs_pairing =
            BN254.add(BN254.mulScalar(BN254.negate(pi), x), BN254.add(BN254.negate(c), BN254.mulScalar(G_1, y)));
        return BN254.pairing(pi, VK, rhs_pairing, G_2);
    }

    function evalPolyAt(uint256[] memory _coefficients, uint256 _index) public pure returns (uint256) {
        uint256 m = BN254.BN254_SCALAR_FIELD;
        uint256 result = 0;
        uint256 powerOfX = 1;

        for (uint256 i = 0; i < _coefficients.length; i++) {
            uint256 coeff = _coefficients[i];
            assembly {
                result := addmod(result, mulmod(powerOfX, coeff, m), m)
                powerOfX := mulmod(powerOfX, _index, m)
            }
        }
        return result;
    }

    /**
     * @notice  Ensures that z(x) == 0 and l(x) == y for all x in x_vals and y in y_vals. It returns the commitment to z(x) and l(x).
     * @param   z_coeffs  coefficients of the zero polynomial z(x) = (x - x_1)(x - x_2)...(x - x_n).
     * @param   l_coeffs  coefficients of the lagrange polynomial l(x).
     * @param   x_vals  x values to evaluate the polynomials at.
     * @param   y_vals  y values to which l(x) should evaluate to.
     * @return  uint256[2]  commitment to z(x).
     * @return  uint256[2]  commitment to l(x).
     */
    function checkAndCommitAuxPolys(
        uint256[] memory z_coeffs,
        uint256[] memory l_coeffs,
        uint256[] memory x_vals,
        uint256[] memory y_vals
    ) public view returns (uint256[2] memory, uint256[2] memory) {
        // z(x) is of degree len(x_vals), it is a product of linear polynomials (x - x_i)
        // l(x) is of degree len(x_vals) - 1
        uint256[2] memory z_commit;
        uint256[2] memory l_commit;
        for (uint256 i = 0; i < x_vals.length; i++) {
            z_commit = BN254.add(z_commit, BN254.mulScalar(G1_CRS[i], z_coeffs[i])); // update commitment to z(x)
            l_commit = BN254.add(l_commit, BN254.mulScalar(G1_CRS[i], l_coeffs[i])); // update commitment to l(x)

            uint256 eval_z = evalPolyAt(z_coeffs, x_vals[i]);
            uint256 eval_l = evalPolyAt(l_coeffs, x_vals[i]);

            require(eval_z == 0, "checkAndCommitAuxPolys: wrong zero poly");
            require(eval_l == y_vals[i], "checkAndCommitAuxPolys: wrong lagrange poly");
        }
        // z(x) has len(x_vals) + 1 coeffs, we add to the commmitment the last coeff of z(x)
        z_commit = BN254.add(z_commit, BN254.mulScalar(G1_CRS[z_coeffs.length - 1], z_coeffs[z_coeffs.length - 1]));

        return (z_commit, l_commit);
    }

    /**
     * @notice  Verifies a batch of point evaluation proofs. Function name follows `ark-poly`.
     * @dev     To avoid ops in G_2, we slightly tweak how the verification is done.
     * @param   c  G1 point commitment to polynomial.
     * @param   pi  G2 point proof.
     * @param   x_vals  Values to prove evaluation of polynomial at.
     * @param   y_vals  Evaluation poly(x).
     * @param   l_coeffs  Coefficients of the lagrange polynomial.
     * @param   z_coeffs  Coefficients of the zero polynomial z(x) = (x - x_1)(x - x_2)...(x - x_n).
     * @return  result  Indicates if KZG proof is correct.
     */
    function batchCheck(
        uint256[2] calldata c,
        uint256[2][2] calldata pi,
        uint256[] calldata x_vals,
        uint256[] calldata y_vals,
        uint256[] calldata l_coeffs,
        uint256[] calldata z_coeffs
    ) external view returns (bool result) {
        //
        // we want to:
        //      1. avoid gas intensive ops in G2
        //      2. format the pairing check in line with what the evm opcode expects.
        //
        // we can do this by tweaking the KZG check to be:
        //
        //          e(z(r) * g1, pi) * e(g1, l(r) * g2) = e(c, g2) [initial check]
        //          e(z(r) * g1, pi) * e(l(r) * g1, g2) * e(c, g2)^{-1} = 1 [bilinearity of pairing]
        //          e(z(r) * g1, pi) * e(l(r) * g1 - c, g2) = 1 [done]
        //
        (uint256[2] memory z_commit, uint256[2] memory l_commit) =
            checkAndCommitAuxPolys(z_coeffs, l_coeffs, x_vals, y_vals);
        uint256[2] memory neg_commit = BN254.negate(c);
        return BN254.pairing(z_commit, pi, BN254.add(l_commit, neg_commit), G_2);
    }
}
