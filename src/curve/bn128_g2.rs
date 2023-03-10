use plonky2_ecdsa::curve::curve_types::{AffinePoint, Curve};
use plonky2_field::types::Field;
use serde::{Deserialize, Serialize};

use crate::field::bn128_base::Bn128Base;
use crate::field::bn128_scalar::Bn128Scalar;
use crate::field::extension::quadratic::QuadraticExtension;

#[derive(Debug, Copy, Clone, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub struct Bn128G2;

// https://ethereum.github.io/yellowpaper/paper.pdf
// E.1. zkSNARK Related Precompiled Contracts
// Y^2 = X^3 + 3(i + 9)^-1
impl Curve for Bn128G2 {
    type BaseField = QuadraticExtension<Bn128Base>;
    type ScalarField = Bn128Scalar;

    // 0x2b149d40ceb8aaae 81be18991be06ac3 b5b4c5e559dbefa3 3267e6dc24a138e5
    //   0x9713b03af0fed4 cd2cafadeed8fdf4 a74fa084e52d1852 e4a2bd0685c315d2
    const A: QuadraticExtension<Bn128Base> =
        QuadraticExtension::<Bn128Base>([Bn128Base::ZERO, Bn128Base::ZERO]);
    const B: QuadraticExtension<Bn128Base> = QuadraticExtension::<Bn128Base>([
        Bn128Base([
            0x3267e6dc24a138e5,
            0xb5b4c5e559dbefa3,
            0x81be18991be06ac3,
            0x2b149d40ceb8aaae,
        ]),
        Bn128Base([
            0xe4a2bd0685c315d2,
            0xa74fa084e52d1852,
            0xcd2cafadeed8fdf4,
            0x9713b03af0fed4,
        ]),
    ]);
    const GENERATOR_AFFINE: AffinePoint<Self> = AffinePoint {
        x: BN128G2_GENERATOR_X,
        y: BN128G2_GENERATOR_Y,
        zero: false,
    };
}

// 0x1800deef121f1e76 426a00665e5c4479 674322d4f75edadd 46debd5cd992f6ed
// 0x198e9393920d483a 7260bfb731fb5d25 f1aa493335a9e712 97e485b7aef312c2
// 0x12c85ea5db8c6deb 4aab71808dcb408f e3d1e7690c43d37b 4ce6cc0166fa7daa
//  0x90689d0585ff075 ec9e99ad690c3395 bc4b313370b38ef3 55acdadcd122975b
const BN128G2_GENERATOR_X: QuadraticExtension<Bn128Base> = QuadraticExtension::<Bn128Base>([
    Bn128Base([
        0x46debd5cd992f6ed,
        0x674322d4f75edadd,
        0x426a00665e5c4479,
        0x1800deef121f1e76,
    ]),
    Bn128Base([
        0x97e485b7aef312c2,
        0xf1aa493335a9e712,
        0x7260bfb731fb5d25,
        0x198e9393920d483a,
    ]),
]);
const BN128G2_GENERATOR_Y: QuadraticExtension<Bn128Base> = QuadraticExtension::<Bn128Base>([
    Bn128Base([
        0x4ce6cc0166fa7daa,
        0xe3d1e7690c43d37b,
        0x4aab71808dcb408f,
        0x12c85ea5db8c6deb,
    ]),
    Bn128Base([
        0x55acdadcd122975b,
        0xbc4b313370b38ef3,
        0xec9e99ad690c3395,
        0x90689d0585ff075,
    ]),
]);

#[cfg(test)]
mod tests {
    use crate::curve::bn128_g2::Bn128G2;
    use crate::field::bn128_scalar::Bn128Scalar;
    use num::BigUint;
    use plonky2_ecdsa::curve::curve_types::{AffinePoint, Curve, ProjectivePoint};
    use plonky2_field::types::{Field, PrimeField};

    #[test]
    fn test_generator() {
        let g = Bn128G2::GENERATOR_AFFINE;
        assert!(g.is_valid());

        let neg_g = AffinePoint::<Bn128G2> {
            x: g.x,
            y: -g.y,
            zero: g.zero,
        };
        assert!(neg_g.is_valid());
    }

    #[test]
    fn test_naive_multiplication() {
        let g = Bn128G2::GENERATOR_PROJECTIVE;
        let ten = Bn128Scalar::from_canonical_u64(10);
        let product = mul_naive(ten, g);
        let sum = g + g + g + g + g + g + g + g + g + g;
        assert_eq!(product, sum);
    }

    #[test]
    fn test_g1_multiplication() {
        let lhs = Bn128Scalar::from_noncanonical_biguint(BigUint::from_slice(&[
            1111, 2222, 3333, 4444, 5555, 6666, 7777, 8888,
        ]));
        assert_eq!(
            Bn128G2::convert(lhs) * Bn128G2::GENERATOR_PROJECTIVE,
            mul_naive(lhs, Bn128G2::GENERATOR_PROJECTIVE)
        );
    }

    /// A simple, somewhat inefficient implementation of multiplication which is used as a reference
    /// for correctness.
    fn mul_naive(lhs: Bn128Scalar, rhs: ProjectivePoint<Bn128G2>) -> ProjectivePoint<Bn128G2> {
        let mut g = rhs;
        let mut sum = ProjectivePoint::ZERO;
        for limb in lhs.to_canonical_biguint().to_u64_digits().iter() {
            for j in 0..64 {
                if (limb >> j & 1u64) != 0u64 {
                    sum = sum + g;
                }
                g = g.double();
            }
        }
        sum
    }
}
