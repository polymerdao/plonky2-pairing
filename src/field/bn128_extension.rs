use crate::field::bn128_base::Bn128Base;
use crate::field::extension::dodecic::DodecicExtension;
use crate::field::extension::sextic::SexticExtension;
use plonky2_field::extension::quadratic::QuadraticExtension;
use plonky2_field::extension::Extendable;
use plonky2_field::types::Field;

impl Extendable<2> for Bn128Base {
    type Extension = QuadraticExtension<Self>;

    // Verifiable in Sage with
    // `R.<x> = GF(p)[]; assert (x^2 - 3).is_irreducible()`.
    const W: Self = Self([3, 0, 0, 0]);

    // DTH_ROOT = W^((ORDER - 1)/2)
    const DTH_ROOT: Self = Self(Bn128Base::NEG_ONE.0);

    // TODO: the following consts should not be used
    const EXT_MULTIPLICATIVE_GROUP_GENERATOR: [Self; 2] = [Self([0, 0, 0, 0]), Self([0, 0, 0, 0])];
    const EXT_POWER_OF_TWO_GENERATOR: [Self; 2] = [Self([0, 0, 0, 0]), Self([0, 0, 0, 0])];
}

impl Extendable<6> for Bn128Base {
    type Extension = SexticExtension<Self>;

    const W: Self = Self([3, 0, 0, 0]);

    // DTH_ROOT = W^((ORDER - 1)/6)
    const DTH_ROOT: Self = Self([
        0xe4bd44e5607cfd49,
        0xc28f069fbb966e3d,
        0x5e6dd9e7e0acccb0,
        0x30644e72e131a029,
    ]);

    // TODO: the following consts will not be used
    const EXT_MULTIPLICATIVE_GROUP_GENERATOR: [Self; 6] = [Self([0, 0, 0, 0]); 6];
    const EXT_POWER_OF_TWO_GENERATOR: [Self; 6] = [Self([0, 0, 0, 0]); 6];
}

impl Extendable<12> for Bn128Base {
    type Extension = DodecicExtension<Self>;

    // TODO: the following consts will not be used
    const W: Self = Self([0, 0, 0, 0]);
    const DTH_ROOT: Self = Self(Bn128Base::NEG_ONE.0);
    const EXT_MULTIPLICATIVE_GROUP_GENERATOR: [Self; 12] = [Self([0, 0, 0, 0]); 12];
    const EXT_POWER_OF_TWO_GENERATOR: [Self; 12] = [Self([0, 0, 0, 0]); 12];
}
