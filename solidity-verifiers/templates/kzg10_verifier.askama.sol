/**
 * @author  Privacy and Scaling Explorations team - pse.dev
 * @dev     Contains utility functions for ops in BN254; in G_1 mostly.
 * @notice  Forked from https://github.com/weijiekoh/libkzg.
 * Among others, a few of the changes we did on this fork were:
 * - Templating the pragma version
 * - Removing type wrappers and use uints instead
 * - Performing changes on arg types
 * - Update some of the `require` statements 
 * - Use the bn254 scalar field instead of checking for overflow on the babyjub prime
 * - In batch checking, we compute auxiliary polynomials and their commitments at the same time.
 */
contract KZG10Verifier {

    // prime of field F_p over which y^2 = x^3 + 3 is defined
    uint256 public constant BN254_PRIME_FIELD =
        21888242871839275222246405745257275088696311157297823662689037894645226208583;
    uint256 public constant BN254_SCALAR_FIELD =
        21888242871839275222246405745257275088548364400416034343698204186575808495617;

    /**
     * @notice  Performs scalar multiplication in G_1.
     * @param   p  G_1 point to multiply
     * @param   s  Scalar to multiply by
     * @return  r  G_1 point p multiplied by scalar s
     */
    function mulScalar(uint256[2] memory p, uint256 s) internal view returns (uint256[2] memory r) {
        uint256[3] memory input;
        input[0] = p[0];
        input[1] = p[1];
        input[2] = s;
        bool success;
        assembly {
            success := staticcall(sub(gas(), 2000), 7, input, 0x60, r, 0x40)
            switch success
            case 0 { invalid() }
        }
        require(success, "bn254: scalar mul failed");
    }

    /**
     * @notice  Negates a point in G_1.
     * @param   p  G_1 point to negate
     * @return  uint256[2]  G_1 point -p
     */
    function negate(uint256[2] memory p) internal pure returns (uint256[2] memory) {
        if (p[0] == 0 && p[1] == 0) {
            return p;
        }
        return [p[0], BN254_PRIME_FIELD - (p[1] % BN254_PRIME_FIELD)];
    }

    /**
     * @notice  Adds two points in G_1.
     * @param   p1  G_1 point 1
     * @param   p2  G_1 point 2
     * @return  r  G_1 point p1 + p2
     */
    function add(uint256[2] memory p1, uint256[2] memory p2) internal view returns (uint256[2] memory r) {
        bool success;
        uint256[4] memory input = [p1[0], p1[1], p2[0], p2[1]];
        assembly {
            success := staticcall(sub(gas(), 2000), 6, input, 0x80, r, 0x40)
            switch success
            case 0 { invalid() }
        }

        require(success, "bn254: point add failed");
    }

    /**
     * @notice  Computes the pairing check e(p1, p2) * e(p3, p4) == 1
     * @dev     Note that G_2 points a*i + b are encoded as two elements of F_p, (a, b)
     * @param   a_1  G_1 point 1
     * @param   a_2  G_2 point 1
     * @param   b_1  G_1 point 2
     * @param   b_2  G_2 point 2
     * @return  result  true if pairing check is successful
     */
    function pairing(uint256[2] memory a_1, uint256[2][2] memory a_2, uint256[2] memory b_1, uint256[2][2] memory b_2)
        internal
        view
        returns (bool result)
    {
        uint256[12] memory input = [
            a_1[0],
            a_1[1],
            a_2[0][1], // imaginary part first
            a_2[0][0],
            a_2[1][1], // imaginary part first
            a_2[1][0],
            b_1[0],
            b_1[1],
            b_2[0][1], // imaginary part first
            b_2[0][0],
            b_2[1][1], // imaginary part first
            b_2[1][0]
        ];

        uint256[1] memory out;
        bool success;

        assembly {
            success := staticcall(sub(gas(), 2000), 8, input, 0x180, out, 0x20)
            switch success
            case 0 { invalid() }
        }

        require(success, "bn254: pairing failed");

        return out[0] == 1;
    }

    uint256[2] G_1 = [
            {{ g1.0[0] }},
            {{ g1.0[1] }}
    ];
    uint256[2][2] G_2 = [
        [
            {{ g2.0[0][0] }},
            {{ g2.0[0][1] }}
        ],
        [
            {{ g2.0[1][0] }},
            {{ g2.0[1][1] }}
        ]
    ];
    uint256[2][2] VK = [
        [
            {{ vk.0[0][0] }},
            {{ vk.0[0][1] }}
        ],
        [
            {{ vk.0[1][0] }},
            {{ vk.0[1][1] }}
        ]
    ];

    {% if g1_crs_len>0 %} // only enabled if g1_crs_len>0, for batch_check
    uint256[2][{{ g1_crs_len }}] G1_CRS = [
    {%- for (i, point) in g1_crs.iter().enumerate() %}
        [ 
            {{ point.0[0] }},
            {{ point.0[1] }}
        {% if loop.last -%}
        ]
        {%- else -%}
        ],
        {%- endif -%}
    {% endfor -%}    
    ];
    {%~ endif %}

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
        public
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
            add(mulScalar(negate(pi), x), add(negate(c), mulScalar(G_1, y)));
        return pairing(pi, VK, rhs_pairing, G_2);
    }

    function evalPolyAt(uint256[] memory _coefficients, uint256 _index) public pure returns (uint256) {
        uint256 m = BN254_SCALAR_FIELD;
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

    {% if g1_crs_len>0 %} // only enabled if g1_crs_len>0, for batch_check
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
            z_commit = add(z_commit, mulScalar(G1_CRS[i], z_coeffs[i])); // update commitment to z(x)
            l_commit = add(l_commit, mulScalar(G1_CRS[i], l_coeffs[i])); // update commitment to l(x)

            uint256 eval_z = evalPolyAt(z_coeffs, x_vals[i]);
            uint256 eval_l = evalPolyAt(l_coeffs, x_vals[i]);

            require(eval_z == 0, "checkAndCommitAuxPolys: wrong zero poly");
            require(eval_l == y_vals[i], "checkAndCommitAuxPolys: wrong lagrange poly");
        }
        // z(x) has len(x_vals) + 1 coeffs, we add to the commitment the last coeff of z(x)
        z_commit = add(z_commit, mulScalar(G1_CRS[z_coeffs.length - 1], z_coeffs[z_coeffs.length - 1]));

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
    ) public view returns (bool result) {
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
        uint256[2] memory neg_commit = negate(c);
        return pairing(z_commit, pi, add(l_commit, neg_commit), G_2);
    }
    {%~ endif %}
}
