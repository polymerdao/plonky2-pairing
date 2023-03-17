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

    const EXT_NONRESIDUE: [Self; 2] = [
        Self([
            0xf60647ce410d7ff7,
            0x2f3d6f4dd31bd011,
            0x2943337e3940c6d1,
            0x1d9598e8a7e39857,
        ]),
        Self([
            0xd35d438dc58f0d9d,
            0x0a78eb28f5c70b3d,
            0x666ea36f7879462c,
            0x0e0a77c19a07df2f,
        ]),
    ];

    // the following consts should not be used
    const EXT_MULTIPLICATIVE_GROUP_GENERATOR: [Self; 2] = todo!();
    const EXT_POWER_OF_TWO_GENERATOR: [Self; 2] = todo!();
}

impl Extendable<6> for Bn128Base {
    type Extension = SexticExtension<Self>;

    // the following consts will not be used
    const W: Self = todo!();
    const DTH_ROOT: Self = todo!();
    const EXT_NONRESIDUE: [Self; 6] = todo!();
    const EXT_MULTIPLICATIVE_GROUP_GENERATOR: [Self; 6] = todo!();
    const EXT_POWER_OF_TWO_GENERATOR: [Self; 6] = todo!();
}

impl Extendable<12> for Bn128Base {
    type Extension = DodecicExtension<Self>;

    // the following consts will not be used
    const EXT_NONRESIDUE: [Self; 12] = todo!();
    const W: Self = todo!();
    const DTH_ROOT: Self = todo!();
    const EXT_MULTIPLICATIVE_GROUP_GENERATOR: [Self; 12] = todo!();
    const EXT_POWER_OF_TWO_GENERATOR: [Self; 12] = todo!();
}