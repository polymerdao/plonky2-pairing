use plonky2_ecdsa::curve::curve_types::{AffinePoint, Curve};
use plonky2_field::types::Field;
use serde::{Deserialize, Serialize};

use crate::field::bn128_base::Bn128Base;
use crate::field::bn128_scalar::Bn128Scalar;

#[derive(Debug, Copy, Clone, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub struct G1;

// https://ethereum.github.io/yellowpaper/paper.pdf
// E.1. zkSNARK Related Precompiled Contracts
// Y^2 = X^3 + 3
impl Curve for G1 {
    type BaseField = Bn128Base;
    type ScalarField = Bn128Scalar;

    const A: Bn128Base = Bn128Base::ZERO;
    const B: Bn128Base = Bn128Base([
        0x7a17caa950ad28d7,
        0x1f6ac17ae15521b9,
        0x334bea4e696bd284,
        0x2a1f6744ce179d8e,
    ]);
    const INV_TWO: Self::BaseField = todo!();
    const GENERATOR_AFFINE: AffinePoint<Self> = AffinePoint {
        x: BN128_GENERATOR_X,
        y: BN128_GENERATOR_Y,
        zero: false,
    };
}

const BN128_GENERATOR_X: Bn128Base = Bn128Base::ONE;
const BN128_GENERATOR_Y: Bn128Base = Bn128Base::TWO;

#[cfg(test)]
mod tests {
    use crate::curve::g1::G1;
    use crate::field::bn128_scalar::Bn128Scalar;
    use num::BigUint;
    use plonky2_ecdsa::curve::curve_types::{AffinePoint, Curve, ProjectivePoint};
    use plonky2_field::types::{Field, PrimeField};

    #[test]
    fn test_generator() {
        let g = G1::GENERATOR_AFFINE;
        assert!(g.is_valid());

        let neg_g = AffinePoint::<G1> {
            x: g.x,
            y: -g.y,
            zero: g.zero,
        };
        assert!(neg_g.is_valid());
    }

    #[test]
    fn test_naive_multiplication() {
        let g = G1::GENERATOR_PROJECTIVE;
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
            G1::convert(lhs) * G1::GENERATOR_PROJECTIVE,
            mul_naive(lhs, G1::GENERATOR_PROJECTIVE)
        );
    }

    /// A simple, somewhat inefficient implementation of multiplication which is used as a reference
    /// for correctness.
    fn mul_naive(lhs: Bn128Scalar, rhs: ProjectivePoint<G1>) -> ProjectivePoint<G1> {
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
