use crate::field::bn128_base::Bn128Base;
use static_assertions::const_assert;
use core::ops::Mul;
use crate::field::extension::quadratic::QuadraticExtension;
use plonky2_field::extension::Extendable;

impl Extendable<2> for Bn128Base {
    type Extension = QuadraticExtension<Self>;

    // Verifiable in Sage with
    // `R.<x> = GF(p)[]; assert (x^2 - 7).is_irreducible()`.
    const W: Self = Self(7);

    // DTH_ROOT = W^((ORDER - 1)/2)
    const DTH_ROOT: Self = Self(18446744069414584320);

    const EXT_MULTIPLICATIVE_GROUP_GENERATOR: [Self; 2] =
        [Self(18081566051660590251), Self(16121475356294670766)];

    const EXT_POWER_OF_TWO_GENERATOR: [Self; 2] = [Self(0), Self(15659105665374529263)];
}

impl Mul for QuadraticExtension<Bn128Base> {
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let Self([a0, a1]) = self;
        let Self([b0, b1]) = rhs;
        let c = ext2_mul([a0.0, a1.0], [b0.0, b1.0]);
        Self(c)
    }
}

/// Multiply a and b considered as elements of GF(p^2).
#[inline(always)]
pub(crate) fn ext2_mul(a: [u64; 2], b: [u64; 2]) -> [Bn128Base; 2] {
    // The code in ext2_add_prods[01] assumes the quadratic extension
    // generator is 7.
    // const_assert!(<Bn128Base as Extendable<2>>::W.0 == 7u64);

    //let c0 = ext2_add_prods0(&a, &b);
    //let c1 = ext2_add_prods1(&a, &b);
    [0, 1]
}
