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
    const FROBENIUS_COEFFS_EXT6_C1: [Self; 6] = [
        Self([
            13075984984163199792,
            3782902503040509012,
            8791150885551868305,
            1825854335138010348,
        ]),
        Self([
            7963664994991228759,
            12257807996192067905,
            13179524609921305146,
            2767831111890561987,
        ]),
        Self([
            3697675806616062876,
            9065277094688085689,
            6918009208039626314,
            2775033306905974752,
        ]),
        Self([0, 0, 0, 0]),
        Self([
            14532872967180610477,
            12903226530429559474,
            1868623743233345524,
            2316889217940299650,
        ]),
        Self([
            12447993766991532972,
            4121872836076202828,
            7630813605053367399,
            740282956577754197,
        ]),
    ];
    const FROBENIUS_COEFFS_EXT6_C2: [Self; 6] = [
        Self([
            8314163329781907090,
            11942187022798819835,
            11282677263046157209,
            1576150870752482284,
        ]),
        Self([
            6763840483288992073,
            7118829427391486816,
            4016233444936635065,
            2630958277570195709,
        ]),
        Self([
            8183898218631979349,
            12014359695528440611,
            12263358156045030468,
            3187210487005268291,
        ]),
        Self([0, 0, 0, 0]),
        Self([
            4938922280314430175,
            13823286637238282975,
            15589480384090068090,
            481952561930628184,
        ]),
        Self([
            3105754162722846417,
            11647802298615474591,
            13057042392041828081,
            1660844386505564338,
        ]),
    ];
    const FROBENIUS_COEFFS_EXT12_C1: [Self; 6] = [
        Self([
            12653890742059813127,
            14585784200204367754,
            1278438861261381767,
            212598772761311868,
        ]),
        Self([
            11683091849979440498,
            14992204589386555739,
            15866167890766973222,
            1200023580730561873,
        ]),
        Self([
            14595462726357228530,
            17349508522658994025,
            1017833795229664280,
            299787779797702374,
        ]),
        Self([0, 0, 0, 0]),
        Self([
            3914496794763385213,
            790120733010914719,
            7322192392869644725,
            581366264293887267,
        ]),
        Self([
            12817045492518885689,
            4440270538777280383,
            11178533038884588256,
            2767537931541304486,
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
    const FROBENIUS_COEFFS_EXT6_C1: [Self; 6] = todo!();
    const FROBENIUS_COEFFS_EXT6_C2: [Self; 6] = todo!();
    const FROBENIUS_COEFFS_EXT12_C1: [Self; 6] = todo!();
    const EXT_MULTIPLICATIVE_GROUP_GENERATOR: [Self; 6] = todo!();
    const EXT_POWER_OF_TWO_GENERATOR: [Self; 6] = todo!();
}

impl Extendable<12> for Bn128Base {
    type Extension = DodecicExtension<Self>;

    // the following consts will not be used
    const EXT_NONRESIDUE: [Self; 12] = todo!();
    const FROBENIUS_COEFFS_EXT6_C1: [Self; 6] = todo!();
    const FROBENIUS_COEFFS_EXT6_C2: [Self; 6] = todo!();
    const FROBENIUS_COEFFS_EXT12_C1: [Self; 6] = todo!();
    const W: Self = todo!();
    const DTH_ROOT: Self = todo!();
    const EXT_MULTIPLICATIVE_GROUP_GENERATOR: [Self; 12] = todo!();
    const EXT_POWER_OF_TWO_GENERATOR: [Self; 12] = todo!();
}
