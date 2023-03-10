use crate::field::bn128_base::Bn128Base;
use crate::field::extension::dodecic::DodecicExtension;
use crate::field::extension::quadratic::QuadraticExtension;
use crate::field::extension::sextic::SexticExtension;
use plonky2_field::extension::Extendable;
use plonky2_field::types::Field;

impl Extendable<2> for Bn128Base {
    type Extension = QuadraticExtension<Self>;

    // Verifiable in Sage with
    const W: Self = Bn128Base::NEG_ONE;

    // DTH_ROOT = W^((ORDER - 1)/2)
    const DTH_ROOT: Self = Self(Bn128Base::NEG_ONE.0);

    // the following consts should not be used
    const EXT_MULTIPLICATIVE_GROUP_GENERATOR: [Self; 2] = todo!();
    const EXT_POWER_OF_TWO_GENERATOR: [Self; 2] = todo!();
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

    // the following consts will not be used
    const EXT_MULTIPLICATIVE_GROUP_GENERATOR: [Self; 6] = todo!();
    const EXT_POWER_OF_TWO_GENERATOR: [Self; 6] = todo!();
}

impl Extendable<12> for Bn128Base {
    type Extension = DodecicExtension<Self>;

    // the following consts will not be used
    const W: Self = todo!();
    const DTH_ROOT: Self = todo!();
    const EXT_MULTIPLICATIVE_GROUP_GENERATOR: [Self; 12] = todo!();
    const EXT_POWER_OF_TWO_GENERATOR: [Self; 12] = todo!();
}
