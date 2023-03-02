use crate::field::bn128_base::Bn128Base;
use crate::field::bn128_scalar::Bn128Scalar;
use plonky2::field::types::Field;
use serde::{Deserialize, Serialize};

use plonky2_ecdsa::curve::curve_types::{AffinePoint, Curve};

#[derive(Debug, Copy, Clone, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub struct Bn128;

impl Curve for Bn128 {
    type BaseField = Bn128Base;
    type ScalarField = Bn128Scalar;

    const A: Bn128Base = Bn128Base::ZERO;
    const B: Bn128Base = Bn128Base([3, 0, 0, 0]);
    const GENERATOR_AFFINE: AffinePoint<Self> = AffinePoint {
        x: BN128_GENERATOR_X,
        y: BN128_GENERATOR_Y,
        zero: false,
    };
}

const BN128_GENERATOR_X: Bn128Base = Bn128Base([1, 0, 0, 0]);

const BN128_GENERATOR_Y: Bn128Base = Bn128Base([2, 0, 0, 0]);

#[cfg(test)]
mod tests {
    use crate::field::bn128_scalar::Bn128Scalar;
    use num::BigUint;
    use plonky2::field::types::{Field, PrimeField};

    use crate::curve::bn128::Bn128;
    use plonky2_ecdsa::curve::curve_types::{AffinePoint, Curve, ProjectivePoint};

    #[test]
    fn test_generator() {
        let g = Bn128::GENERATOR_AFFINE;
        assert!(g.is_valid());

        let neg_g = AffinePoint::<Bn128> {
            x: g.x,
            y: -g.y,
            zero: g.zero,
        };
        assert!(neg_g.is_valid());
    }

    #[test]
    fn test_naive_multiplication() {
        let g = Bn128::GENERATOR_PROJECTIVE;
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
            Bn128::convert(lhs) * Bn128::GENERATOR_PROJECTIVE,
            mul_naive(lhs, Bn128::GENERATOR_PROJECTIVE)
        );
    }

    /// A simple, somewhat inefficient implementation of multiplication which is used as a reference
    /// for correctness.
    fn mul_naive(lhs: Bn128Scalar, rhs: ProjectivePoint<Bn128>) -> ProjectivePoint<Bn128> {
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
