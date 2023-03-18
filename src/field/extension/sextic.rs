use core::fmt::{self, Debug, Display, Formatter};
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use num::bigint::BigUint;
use num::traits::Pow;
use serde::{Deserialize, Serialize};

use plonky2_field::extension::{Extendable, FieldExtension, Frobenius, OEF};
use plonky2_field::types::{Field, Sample};

use crate::field::extension::quadratic::QuadraticExtension;

// [F; 6] = Ext<2> + Ext<2> + Ext<2>
#[derive(Copy, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SexticExtension<F: Extendable<6>>(pub [F; 6]);

impl<F: Extendable<6> + Extendable<2>> Default for SexticExtension<F> {
    fn default() -> Self {
        Self::ZERO
    }
}

impl<F: Extendable<6> + Extendable<2>> OEF<6> for SexticExtension<F> {
    const W: F = Extendable::<6>::W;
    const DTH_ROOT: F = Extendable::<6>::DTH_ROOT;
}

impl<F: Extendable<6> + Extendable<2>> Frobenius<6> for SexticExtension<F> {}

impl<F: Extendable<6> + Extendable<2>> FieldExtension<6> for SexticExtension<F> {
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

impl<F: Extendable<6> + Extendable<2>> From<F> for SexticExtension<F> {
    fn from(x: F) -> Self {
        Self([x, F::ZERO, F::ZERO, F::ZERO, F::ZERO, F::ZERO])
    }
}

impl<F: Extendable<6> + Extendable<2>> Sample for SexticExtension<F> {
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

impl<F: Extendable<6> + Extendable<2>> Field for SexticExtension<F> {
    const ZERO: Self = Self([F::ZERO; 6]);
    const ONE: Self = Self([F::ONE, F::ZERO, F::ZERO, F::ZERO, F::ZERO, F::ZERO]);
    const TWO: Self = Self([F::TWO, F::ZERO, F::ZERO, F::ZERO, F::ZERO, F::ZERO]);
    const NEG_ONE: Self = Self([F::NEG_ONE, F::ZERO, F::ZERO, F::ZERO, F::ZERO, F::ZERO]);
    const MONTGOMERY_INV: Self = todo!();

    const TWO_ADICITY: usize = F::TWO_ADICITY + 2;
    const CHARACTERISTIC_TWO_ADICITY: usize = F::CHARACTERISTIC_TWO_ADICITY;

    const NONRESIDUE: Self = Self(F::EXT_NONRESIDUE);
    const MULTIPLICATIVE_GROUP_GENERATOR: Self = Self(F::EXT_MULTIPLICATIVE_GROUP_GENERATOR);
    const POWER_OF_TWO_GENERATOR: Self = Self(F::EXT_POWER_OF_TWO_GENERATOR);

    const BITS: usize = F::BITS * 6;

    fn order() -> BigUint {
        F::order().pow(6u32)
    }
    fn characteristic() -> BigUint {
        F::characteristic()
    }

    fn mul_by_nonresidue(&self) -> Self {
        let c0 = QuadraticExtension([self.0[4], self.0[5]]).mul_by_nonresidue();
        Self {
            0: [c0.0[0], c0.0[1], self.0[0], self.0[1], self.0[2], self.0[3]],
        }
    }

    // Algorithm 11.3.4 in Handbook of Elliptic and Hyperelliptic Curve Cryptography.
    fn try_inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        let s0 = QuadraticExtension([self.0[0], self.0[1]]);
        let s1 = QuadraticExtension([self.0[2], self.0[3]]);
        let s2 = QuadraticExtension([self.0[4], self.0[5]]);

        let c0 = (s0 * s0) - s1 * s2.mul_by_nonresidue();
        let c1 = (s2 * s2).mul_by_nonresidue() - s0 * s1;
        let c2 = s1 * s1 - s0 * s2;

        let t = ((s2 * c1 + s1 * c2).mul_by_nonresidue() + s0 * c0).inverse();

        let c0 = t * c0;
        let c1 = t * c1;
        let c2 = t * c2;

        Some(Self([c0.0[0], c0.0[1], c1.0[0], c1.0[1], c2.0[0], c2.0[1]]))
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

impl<F: Extendable<6> + Extendable<2>> Display for SexticExtension<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} + {}*a + {}*a^2 + {}*a^3 + {}*a^4 + {}*a^5",
            self.0[0], self.0[1], self.0[2], self.0[3], self.0[4], self.0[5]
        )
    }
}

impl<F: Extendable<6> + Extendable<2>> Debug for SexticExtension<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<F: Extendable<6> + Extendable<2>> Neg for SexticExtension<F> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self([
            -self.0[0], -self.0[1], -self.0[2], -self.0[3], -self.0[4], -self.0[5],
        ])
    }
}

impl<F: Extendable<6> + Extendable<2>> Add for SexticExtension<F> {
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

impl<F: Extendable<6> + Extendable<2>> AddAssign for SexticExtension<F> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<F: Extendable<6> + Extendable<2>> Sum for SexticExtension<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, x| acc + x)
    }
}

impl<F: Extendable<6> + Extendable<2>> Sub for SexticExtension<F> {
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

impl<F: Extendable<6> + Extendable<2>> SubAssign for SexticExtension<F> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<F: Extendable<6> + Extendable<2>> Mul for SexticExtension<F> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let l0 = QuadraticExtension([self.0[0], self.0[1]]);
        let l1 = QuadraticExtension([self.0[2], self.0[3]]);
        let l2 = QuadraticExtension([self.0[4], self.0[5]]);
        let r0 = QuadraticExtension([rhs.0[0], rhs.0[1]]);
        let r1 = QuadraticExtension([rhs.0[2], rhs.0[3]]);
        let r2 = QuadraticExtension([rhs.0[4], rhs.0[5]]);

        let aa = r0 * l0;
        let bb = r1 * l1;
        let cc = r2 * l2;

        let c0 = ((l1 + l2) * (r1 + r2) - bb - cc).mul_by_nonresidue() + aa;
        let c1 = (l0 + l1) * (r0 + r1) - aa - bb + cc.mul_by_nonresidue();
        let c2 = (l0 + l2) * (r0 + r2) - aa + bb - cc;

        Self([c0.0[0], c0.0[1], c1.0[0], c1.0[1], c2.0[0], c2.0[1]])
    }
}

impl<F: Extendable<6> + Extendable<2>> MulAssign for SexticExtension<F> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<F: Extendable<6> + Extendable<2>> Product for SexticExtension<F> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ONE, |acc, x| acc * x)
    }
}

impl<F: Extendable<6> + Extendable<2>> Div for SexticExtension<F> {
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inverse()
    }
}

impl<F: Extendable<6> + Extendable<2>> DivAssign for SexticExtension<F> {
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
