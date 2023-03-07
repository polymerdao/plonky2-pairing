use core::fmt::{self, Debug, Display, Formatter};
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use num::bigint::BigUint;
use num::traits::Pow;
use serde::{Deserialize, Serialize};

use plonky2_field::extension::{Extendable, FieldExtension, Frobenius, OEF};
use plonky2_field::types::{Field, Sample};

#[derive(Copy, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SexticExtension<F: Extendable<6>>(pub [F; 6]);

impl<F: Extendable<6>> Default for SexticExtension<F> {
    fn default() -> Self {
        Self::ZERO
    }
}

impl<F: Extendable<6>> OEF<6> for SexticExtension<F> {
    const W: F = F::W;
    const DTH_ROOT: F = F::DTH_ROOT;
}

impl<F: Extendable<6>> Frobenius<6> for SexticExtension<F> {}

impl<F: Extendable<6>> FieldExtension<6> for SexticExtension<F> {
    type BaseField = F;

    fn to_basefield_array(&self) -> [F; 6] {
        self.0
    }

    fn from_basefield_array(arr: [F; 6]) -> Self {
        Self(arr)
    }

    fn from_basefield(x: F) -> Self {
        x.into()
    }
}

impl<F: Extendable<6>> From<F> for SexticExtension<F> {
    fn from(x: F) -> Self {
        Self([x, F::ZERO, F::ZERO, F::ZERO, F::ZERO, F::ZERO])
    }
}

impl<F: Extendable<6>> Sample for SexticExtension<F> {
    #[inline]
    fn sample<R>(rng: &mut R) -> Self
    where
        R: rand::RngCore + ?Sized,
    {
        Self::from_basefield_array([
            F::sample(rng),
            F::sample(rng),
            F::sample(rng),
            F::sample(rng),
            F::sample(rng),
            F::sample(rng),
        ])
    }
}

impl<F: Extendable<6>> Field for SexticExtension<F> {
    const ZERO: Self = Self([F::ZERO; 6]);
    const ONE: Self = Self([F::ONE, F::ZERO, F::ZERO, F::ZERO, F::ZERO, F::ZERO]);
    const TWO: Self = Self([F::TWO, F::ZERO, F::ZERO, F::ZERO, F::ZERO, F::ZERO]);
    const NEG_ONE: Self = Self([F::NEG_ONE, F::ZERO, F::ZERO, F::ZERO, F::ZERO, F::ZERO]);

    // `p^4 - 1 = (p - 1)(p + 1)(p^2 + 1)`. The `p - 1` term has a two-adicity of `F::TWO_ADICITY`.
    // As long as `F::TWO_ADICITY >= 2`, `p` can be written as `4n + 1`, so `p + 1` can be written as
    // `2(2n + 1)`, which has a 2-adicity of 1. A similar argument can show that `p^2 + 1` also has
    // a 2-adicity of 1.
    const TWO_ADICITY: usize = F::TWO_ADICITY + 2;
    const CHARACTERISTIC_TWO_ADICITY: usize = F::CHARACTERISTIC_TWO_ADICITY;

    const MULTIPLICATIVE_GROUP_GENERATOR: Self = Self(F::EXT_MULTIPLICATIVE_GROUP_GENERATOR);
    const POWER_OF_TWO_GENERATOR: Self = Self(F::EXT_POWER_OF_TWO_GENERATOR);

    const BITS: usize = F::BITS * 6;

    fn order() -> BigUint {
        F::order().pow(6u32)
    }
    fn characteristic() -> BigUint {
        F::characteristic()
    }

    // Algorithm 11.3.4 in Handbook of Elliptic and Hyperelliptic Curve Cryptography.
    fn try_inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        let a_pow_p = self.frobenius();
        let a_pow_p_plus_1 = a_pow_p * *self;
        let a_pow_p3_plus_p2 = a_pow_p_plus_1.repeated_frobenius(2);
        let a_pow_p5_plus_p4 = a_pow_p3_plus_p2.repeated_frobenius(2);
        let a_pow_r_minus_1 = a_pow_p5_plus_p4 * a_pow_p3_plus_p2 * a_pow_p;
        let a_pow_r = a_pow_r_minus_1 * *self;
        debug_assert!(FieldExtension::<6>::is_in_basefield(&a_pow_r));

        Some(FieldExtension::<6>::scalar_mul(
            &a_pow_r_minus_1,
            a_pow_r.0[0].inverse(),
        ))
    }

    fn from_noncanonical_biguint(n: BigUint) -> Self {
        F::from_noncanonical_biguint(n).into()
    }

    fn from_canonical_u64(n: u64) -> Self {
        F::from_canonical_u64(n).into()
    }

    fn from_noncanonical_u128(n: u128) -> Self {
        F::from_noncanonical_u128(n).into()
    }
}

impl<F: Extendable<6>> Display for SexticExtension<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} + {}*a + {}*a^2 + {}*a^3 + {}*a^4 + {}*a^5",
            self.0[0], self.0[1], self.0[2], self.0[3], self.0[4], self.0[5]
        )
    }
}

impl<F: Extendable<6>> Debug for SexticExtension<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<F: Extendable<6>> Neg for SexticExtension<F> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self([
            -self.0[0], -self.0[1], -self.0[2], -self.0[3], -self.0[4], -self.0[5],
        ])
    }
}

impl<F: Extendable<6>> Add for SexticExtension<F> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self([
            self.0[0] + rhs.0[0],
            self.0[1] + rhs.0[1],
            self.0[2] + rhs.0[2],
            self.0[3] + rhs.0[3],
            self.0[4] + rhs.0[4],
            self.0[5] + rhs.0[5],
        ])
    }
}

impl<F: Extendable<6>> AddAssign for SexticExtension<F> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<F: Extendable<6>> Sum for SexticExtension<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, x| acc + x)
    }
}

impl<F: Extendable<6>> Sub for SexticExtension<F> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self([
            self.0[0] - rhs.0[0],
            self.0[1] - rhs.0[1],
            self.0[2] - rhs.0[2],
            self.0[3] - rhs.0[3],
            self.0[4] - rhs.0[4],
            self.0[5] - rhs.0[5],
        ])
    }
}

impl<F: Extendable<6>> SubAssign for SexticExtension<F> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<F: Extendable<6>> Mul for SexticExtension<F> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let Self([a0, a1, a2, a3, a4, a5]) = self;
        let Self([b0, b1, b2, b3, b4, b5]) = rhs;

        let c0 = a0 * b0 + <Self as OEF<6>>::W * (a1 * b5 + a2 * b4 + a3 * b3 + a4 * b2 + a5 * b1);
        let c1 = a0 * b1 + a1 * b0 + <Self as OEF<6>>::W * (a2 * b5 + a3 * b4 + a4 * b3 + a5 * b2);
        let c2 = a0 * b2 + a1 * b1 + a2 * b0 + <Self as OEF<6>>::W * (a3 * b5 + a4 * b4 + a5 * b3);
        let c3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 + <Self as OEF<6>>::W * (a4 * b5 + a5 * b4);
        let c4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0 + <Self as OEF<6>>::W * a5 * b5;
        let c5 = a0 * b5 + a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1 + a5 * b0;

        Self([c0, c1, c2, c3, c4, c5])
    }
}

impl<F: Extendable<6>> MulAssign for SexticExtension<F> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<F: Extendable<6>> Product for SexticExtension<F> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ONE, |acc, x| acc * x)
    }
}

impl<F: Extendable<6>> Div for SexticExtension<F> {
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inverse()
    }
}

impl<F: Extendable<6>> DivAssign for SexticExtension<F> {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

#[cfg(test)]
mod tests {
    mod bn128 {
        use crate::{test_field_arithmetic, test_field_extension};

        test_field_extension!(crate::field::bn128_base::Bn128Base, 6);
        test_field_arithmetic!(
            crate::field::extension::sextic::SexticExtension<
                crate::field::bn128_base::Bn128Base,
            >
        );
    }
}
