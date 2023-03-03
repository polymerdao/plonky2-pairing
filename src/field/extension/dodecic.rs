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
pub struct DodecicExtension<F: Extendable<12>>(pub [F; 12]);

impl<F: Extendable<12>> Default for DodecicExtension<F> {
    fn default() -> Self {
        Self::ZERO
    }
}

impl<F: Extendable<12>> OEF<12> for DodecicExtension<F> {
    const W: F = F::W;
    const DTH_ROOT: F = F::DTH_ROOT;
}

impl<F: Extendable<12>> Frobenius<12> for DodecicExtension<F> {}

impl<F: Extendable<12>> FieldExtension<12> for DodecicExtension<F> {
    type BaseField = F;

    fn to_basefield_array(&self) -> [F; 12] {
        self.0
    }

    fn from_basefield_array(arr: [F; 12]) -> Self {
        Self(arr)
    }

    fn from_basefield(x: F) -> Self {
        x.into()
    }
}

impl<F: Extendable<12>> From<F> for DodecicExtension<F> {
    fn from(x: F) -> Self {
        Self([
            x,
            F::ZERO,
            F::ZERO,
            F::ZERO,
            F::ZERO,
            F::ZERO,
            F::ZERO,
            F::ZERO,
            F::ZERO,
            F::ZERO,
            F::ZERO,
            F::ZERO,
        ])
    }
}

impl<F: Extendable<12>> Sample for DodecicExtension<F> {
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
            F::sample(rng),
            F::sample(rng),
            F::sample(rng),
            F::sample(rng),
            F::sample(rng),
            F::sample(rng),
        ])
    }
}

impl<F: Extendable<12>> Field for DodecicExtension<F> {
    const ZERO: Self = Self([F::ZERO; 12]);
    const ONE: Self = Self([
        F::ONE,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
    ]);
    const TWO: Self = Self([
        F::TWO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
    ]);
    const NEG_ONE: Self = Self([
        F::NEG_ONE,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
    ]);

    // `p^5 - 1 = (p - 1)(p^4 + p^3 + p^2 + p + 1)`. The `p - 1` term
    // has a two-adicity of `F::TWO_ADICITY` and the term `p^4 + p^3 +
    // p^2 + p + 1` is odd since it is the sum of an odd number of odd
    // terms. Hence the two-adicity of `p^5 - 1` is the same as for
    // `p - 1`.
    const TWO_ADICITY: usize = F::TWO_ADICITY;
    const CHARACTERISTIC_TWO_ADICITY: usize = F::CHARACTERISTIC_TWO_ADICITY;

    const MULTIPLICATIVE_GROUP_GENERATOR: Self = Self(F::EXT_MULTIPLICATIVE_GROUP_GENERATOR);
    const POWER_OF_TWO_GENERATOR: Self = Self(F::EXT_POWER_OF_TWO_GENERATOR);

    const BITS: usize = F::BITS * 12;

    fn order() -> BigUint {
        F::order().pow(12u32)
    }
    fn characteristic() -> BigUint {
        F::characteristic()
    }

    // Algorithm 11.3.4 in Handbook of Elliptic and Hyperelliptic Curve Cryptography.
    fn try_inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        // Writing 'a' for self:
        let d = self.frobenius(); // d = a^p
        let e = d * d.frobenius(); // e = a^(p + p^2)
        let f = d * e.frobenius(); // f = a^(p + p^2 + p^3)
        let g = d * f.frobenius(); // g = a^(p + p^2 + p^3 + p^4)
        let h = g.repeated_frobenius(3); // g = a^(p^4 + p^5 + p^6 + p^7)
        let i = h.repeated_frobenius(4); // h = a^(p^8 + p^9 + p^10 + p^11)
        let j = f * h * i; // j = a^(p + p^2 + ... + p^11)

        // f contains a^(r-1) and a^r is in the base field.
        debug_assert!(FieldExtension::<12>::is_in_basefield(&(*self * f)));

        // g = a^r is in the base field, so only compute that
        // coefficient rather than the full product. The equation is
        // extracted from Mul::mul(...) below.
        let Self([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]) = *self;
        let Self([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]) = f;
        let g = a0 * b0
            + <Self as OEF<12>>::W
                * (a1 * b11
                    + a2 * b10
                    + a3 * b9
                    + a4 * b8
                    + a5 * b7
                    + a6 * b6
                    + a7 * b5
                    + a8 * b4
                    + a9 * b3
                    + a10 * b2
                    + a11 * b2);

        Some(FieldExtension::<12>::scalar_mul(&f, g.inverse()))
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

impl<F: Extendable<12>> Display for DodecicExtension<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} + {}*a + {}*a^2 + {}*a^3 + {}*a^4",
            self.0[0], self.0[1], self.0[2], self.0[3], self.0[4]
        )
    }
}

impl<F: Extendable<12>> Debug for DodecicExtension<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<F: Extendable<12>> Neg for DodecicExtension<F> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self([
            -self.0[0],
            -self.0[1],
            -self.0[2],
            -self.0[3],
            -self.0[4],
            -self.0[5],
            -self.0[6],
            -self.0[7],
            -self.0[8],
            -self.0[9],
            -self.0[10],
            -self.0[11],
        ])
    }
}

impl<F: Extendable<12>> Add for DodecicExtension<F> {
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
            self.0[6] + rhs.0[6],
            self.0[7] + rhs.0[7],
            self.0[8] + rhs.0[8],
            self.0[9] + rhs.0[9],
            self.0[10] + rhs.0[10],
            self.0[11] + rhs.0[11],
        ])
    }
}

impl<F: Extendable<12>> AddAssign for DodecicExtension<F> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<F: Extendable<12>> Sum for DodecicExtension<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, x| acc + x)
    }
}

impl<F: Extendable<12>> Sub for DodecicExtension<F> {
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
            self.0[6] - rhs.0[6],
            self.0[7] - rhs.0[7],
            self.0[8] - rhs.0[8],
            self.0[9] - rhs.0[9],
            self.0[10] - rhs.0[10],
            self.0[11] - rhs.0[11],
        ])
    }
}

impl<F: Extendable<12>> SubAssign for DodecicExtension<F> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<F: Extendable<12>> Mul for DodecicExtension<F> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let Self([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]) = self;
        let Self([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]) = rhs;
        let w = <Self as OEF<12>>::W;

        let c0 = a0 * b0
            + w * (a1 * b11
                + a2 * b10
                + a3 * b9
                + a4 * b8
                + a5 * b7
                + a6 * b6
                + a7 * b5
                + a8 * b4
                + a9 * b3
                + a10 * b2
                + a11 * b1);
        let c1 = a0 * b1
            + a1 * b0
            + w * (a2 * b11
                + a3 * b10
                + a4 * b9
                + a5 * b8
                + a6 * b7
                + a7 * b6
                + a8 * b5
                + a9 * b4
                + a10 * b3
                + a11 * b2);
        let c2 = a0 * b2
            + a1 * b1
            + a2 * b0
            + w * (a3 * b11
                + a4 * b10
                + a5 * b9
                + a6 * b8
                + a7 * b7
                + a8 * b6
                + a9 * b5
                + a10 * b4
                + a11 * b3);
        let c3 = a0 * b3
            + a1 * b2
            + a2 * b1
            + a3 * b0
            + w * (a4 * b11
                + a5 * b10
                + a6 * b9
                + a7 * b8
                + a8 * b7
                + a9 * b6
                + a10 * b5
                + a11 * b4);
        let c4 = a0 * b4
            + a1 * b3
            + a2 * b2
            + a3 * b1
            + a4 * b0
            + w * (a5 * b11 + a6 * b10 + a7 * b9 + a8 * b8 + a9 * b7 + a10 * b6 + a11 * b5);
        let c5 = a0 * b5
            + a1 * b4
            + a2 * b3
            + a3 * b2
            + a4 * b1
            + a5 * b0
            + w * (a6 * b11 + a7 * b10 + a8 * b9 + a9 * b8 + a10 * b7 + a11 * b6);
        let c6 = a0 * b6
            + a1 * b5
            + a2 * b4
            + a3 * b3
            + a4 * b2
            + a5 * b1
            + a6 * b0
            + w * (a7 * b11 + a8 * b10 + a9 * b9 + a10 * b8 + a11 * b7);
        let c7 = a0 * b7
            + a1 * b6
            + a2 * b5
            + a3 * b4
            + a4 * b3
            + a5 * b2
            + a6 * b1
            + a7 * b0
            + w * (a8 * b11 + a9 * b10 + a10 * b9 + a11 * b8);
        let c8 = a0 * b8
            + a1 * b7
            + a2 * b6
            + a3 * b5
            + a4 * b4
            + a5 * b3
            + a6 * b2
            + a7 * b1
            + a8 * b0
            + w * (a9 * b11 + a10 * b10 + a11 * b9);
        let c9 = a0 * b9
            + a1 * b8
            + a2 * b7
            + a3 * b6
            + a4 * b5
            + a5 * b4
            + a6 * b3
            + a7 * b2
            + a8 * b1
            + a9 * b0
            + w * (a10 * b11 + a11 * b10);
        let c10 = a0 * b10
            + a1 * b9
            + a2 * b8
            + a3 * b7
            + a4 * b6
            + a5 * b5
            + a6 * b4
            + a7 * b3
            + a8 * b2
            + a9 * b1
            + a10 * b0
            + w * a11 * b11;
        let c11 = a0 * b11
            + a1 * b10
            + a2 * b9
            + a3 * b8
            + a4 * b7
            + a5 * b6
            + a6 * b5
            + a7 * b4
            + a8 * b3
            + a9 * b2
            + a10 * b1
            + a11 * b0;

        Self([c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11])
    }
}

impl<F: Extendable<12>> MulAssign for DodecicExtension<F> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<F: Extendable<12>> Product for DodecicExtension<F> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ONE, |acc, x| acc * x)
    }
}

impl<F: Extendable<12>> Div for DodecicExtension<F> {
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inverse()
    }
}

impl<F: Extendable<12>> DivAssign for DodecicExtension<F> {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

#[cfg(test)]
mod tests {
    mod bn128 {
        use crate::{test_field_arithmetic, test_field_extension};

        test_field_extension!(crate::field::bn128_base::Bn128Base, 12);
        test_field_arithmetic!(
            crate::field::extension::dodecic::DodecicExtension<
                crate::field::bn128_base::Bn128Base,
            >
        );
    }
}
