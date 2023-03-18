use core::fmt::{self, Debug, Display, Formatter};
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use num::bigint::BigUint;
use num::traits::Pow;
use serde::{Deserialize, Serialize};

use plonky2_field::extension::{Extendable, FieldExtension, Frobenius, OEF};
use plonky2_field::types::{Field, Sample};

use crate::field::extension::sextic::SexticExtension;

// [F; 12] = Ext<6> + Ext<6>
#[derive(Copy, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct DodecicExtension<F: Extendable<12> + Extendable<6> + Extendable<2>>(pub [F; 12]);

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> Default for DodecicExtension<F> {
    fn default() -> Self {
        Self::ZERO
    }
}

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> OEF<12> for DodecicExtension<F> {
    const W: F = Extendable::<12>::W;
    const DTH_ROOT: F = Extendable::<12>::DTH_ROOT;
}

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> Frobenius<12> for DodecicExtension<F> {}

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> FieldExtension<12> for DodecicExtension<F> {
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

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> From<F> for DodecicExtension<F> {
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

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> Sample for DodecicExtension<F> {
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

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> Field for DodecicExtension<F> {
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
    const MONTGOMERY_INV: Self = todo!();

    // `p^5 - 1 = (p - 1)(p^4 + p^3 + p^2 + p + 1)`. The `p - 1` term
    // has a two-adicity of `F::TWO_ADICITY` and the term `p^4 + p^3 +
    // p^2 + p + 1` is odd since it is the sum of an odd number of odd
    // terms. Hence the two-adicity of `p^5 - 1` is the same as for
    // `p - 1`.
    const TWO_ADICITY: usize = F::TWO_ADICITY;
    const CHARACTERISTIC_TWO_ADICITY: usize = F::CHARACTERISTIC_TWO_ADICITY;

    const NONRESIDUE: Self = Self(F::EXT_NONRESIDUE);
    const MULTIPLICATIVE_GROUP_GENERATOR: Self = Self(F::EXT_MULTIPLICATIVE_GROUP_GENERATOR);
    const POWER_OF_TWO_GENERATOR: Self = Self(F::EXT_POWER_OF_TWO_GENERATOR);

    const BITS: usize = F::BITS * 12;

    fn order() -> BigUint {
        F::order().pow(12u32)
    }
    fn characteristic() -> BigUint {
        F::characteristic()
    }

    fn mul_by_nonresidue(&self) -> Self {
        todo!()
    }

    // Algorithm 11.3.4 in Handbook of Elliptic and Hyperelliptic Curve Cryptography.
    fn try_inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        let c0 = SexticExtension([
            self.0[0], self.0[1], self.0[2], self.0[3], self.0[4], self.0[5],
        ]);
        let c1 = SexticExtension([
            self.0[6], self.0[7], self.0[8], self.0[9], self.0[10], self.0[11],
        ]);

        let c0_squared = c0 * c0;
        let c1_squared_mul_by_nonresidue = (c1 * c1).mul_by_nonresidue();
        let t = (c0_squared - c1_squared_mul_by_nonresidue).inverse();

        let r0 = c0 * t;
        let r1 = -c1 * t;

        Some(DodecicExtension([
            r0.0[0], r0.0[1], r0.0[2], r0.0[3], r0.0[4], r0.0[5], r1.0[0], r1.0[1], r1.0[2],
            r1.0[3], r1.0[4], r1.0[5],
        ]))
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

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> Display for DodecicExtension<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} + {}*a + {}*a^2 + {}*a^3 + {}*a^4 + {}*a^5 + {}*a^6 + {}*a^7 + {}*a^8 + {}*a^9 + {}*a^10 + {}*a^11",
            self.0[0], self.0[1], self.0[2], self.0[3], self.0[4],
            self.0[5], self.0[6], self.0[7], self.0[8], self.0[9],
            self.0[10], self.0[11]
        )
    }
}

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> Debug for DodecicExtension<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> Neg for DodecicExtension<F> {
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

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> Add for DodecicExtension<F> {
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

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> AddAssign for DodecicExtension<F> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> Sum for DodecicExtension<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, x| acc + x)
    }
}

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> Sub for DodecicExtension<F> {
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

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> SubAssign for DodecicExtension<F> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> Mul for DodecicExtension<F> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let l0 = SexticExtension([
            self.0[0], self.0[1], self.0[2], self.0[3], self.0[4], self.0[5],
        ]);
        let l1 = SexticExtension([
            self.0[6], self.0[7], self.0[8], self.0[9], self.0[10], self.0[11],
        ]);
        let r0 = SexticExtension([rhs.0[0], rhs.0[1], rhs.0[2], rhs.0[3], rhs.0[4], rhs.0[5]]);
        let r1 = SexticExtension([rhs.0[6], rhs.0[7], rhs.0[8], rhs.0[9], rhs.0[10], rhs.0[11]]);

        let aa = l0 * r0;
        let bb = l1 * r1;

        let c0 = bb.mul_by_nonresidue() + aa;
        let c1 = (l0 + l1) * (r0 + r1) - aa - bb;

        Self([
            c0.0[0], c0.0[1], c0.0[2], c0.0[3], c0.0[4], c0.0[5], c1.0[0], c1.0[1], c1.0[2],
            c1.0[3], c1.0[4], c1.0[5],
        ])
    }
}

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> MulAssign for DodecicExtension<F> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> Product for DodecicExtension<F> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ONE, |acc, x| acc * x)
    }
}

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> Div for DodecicExtension<F> {
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inverse()
    }
}

impl<F: Extendable<12> + Extendable<6> + Extendable<2>> DivAssign for DodecicExtension<F> {
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
