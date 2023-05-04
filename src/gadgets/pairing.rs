use crate::field::extension::quadratic::QuadraticExtension;
use crate::gadgets::g1::AffinePointTarget;
use crate::gadgets::g2::{AffinePointTargetG2, CircuitBuilderCurveG2};
use crate::gadgets::nonnative_fp12::{CircuitBuilderNonNativeExt12, NonNativeTargetExt12};
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_ecdsa::curve::curve_types::Curve;
use plonky2_field::extension::Extendable;
use plonky2_field::types::PrimeField;

pub trait CircuitBuilderPairing<F: RichField + Extendable<D>, const D: usize> {
    fn pairing<
        C1: Curve<BaseField = FF>,
        C2: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2> + Extendable<6> + Extendable<12>,
    >(
        &mut self,
        p: &AffinePointTarget<C1>,
        q: &AffinePointTargetG2<FF>,
    ) -> NonNativeTargetExt12<FF>;
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilderPairing<F, D>
    for CircuitBuilder<F, D>
{
    fn pairing<
        C1: Curve<BaseField = FF>,
        C2: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2> + Extendable<6> + Extendable<12>,
    >(
        &mut self,
        p: &AffinePointTarget<C1>,
        q: &AffinePointTargetG2<FF>,
    ) -> NonNativeTargetExt12<FF> {
        let pre = self.precompute::<C2, FF>(q);
        let m = self.miller_loop::<C1, FF>(p, &pre);
        let res = self.final_exponentiation_first_chunk(&m);
        self.final_exponentiation_last_chunk(&res)
    }
}

#[cfg(test)]
mod tests {
    use crate::curve::g1::G1;
    use crate::curve::g2::G2;
    use crate::field::bn128_base::Bn128Base;
    use crate::field::extension::dodecic::DodecicExtension;
    use crate::field::extension::quadratic::QuadraticExtension;
    use crate::gadgets::g1::{AffinePointTarget, CircuitBuilderCurve};
    use crate::gadgets::g2::{CircuitBuilderCurveG2, JacobianPointTargetG2};
    use crate::gadgets::nonnative_fp::CircuitBuilderNonNative;
    use crate::gadgets::nonnative_fp12::CircuitBuilderNonNativeExt12;
    use crate::gadgets::nonnative_fp2::CircuitBuilderNonNativeExt2;
    use crate::gadgets::pairing::CircuitBuilderPairing;
    use anyhow::Result;
    use log::{Level, LevelFilter};
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2::util::timing::TimingTree;
    use plonky2_ecdsa::curve::curve_types::Curve;
    use plonky2_field::types::Sample;

    #[test]
    #[ignore]
    fn test_pairing() -> Result<()> {
        let mut builder = env_logger::Builder::from_default_env();
        builder.format_timestamp(None);
        builder.filter_level(LevelFilter::Info);
        builder.try_init()?;

        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_ecc_config();

        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        type FF = Bn128Base;

        let g1g = G1::GENERATOR_AFFINE;
        let g2g = G2::GENERATOR_AFFINE;
        let x_ff = DodecicExtension::<FF>::rand();
        builder.constant_affine_point(g1g);
        builder.constant_affine_point_g2(g2g);
        builder.constant_nonnative_ext12(x_ff);

        let p = AffinePointTarget::<G1> {
            x: builder.constant_nonnative(Bn128Base([
                18009135459904726766,
                2053664114473314749,
                9535470248130011749,
                3479289040628672906,
            ])),
            y: builder.constant_nonnative(Bn128Base([
                6225675676338262706,
                4510937524066860607,
                11348405336138879847,
                2021255424210394902,
            ])),
        };

        let q = JacobianPointTargetG2 {
            x: builder.constant_nonnative_ext2(QuadraticExtension::<Bn128Base>([
                Bn128Base([
                    2577798519503118397,
                    14034210771057369560,
                    14798801535089424299,
                    1731240919448670153,
                ]),
                Bn128Base([
                    15909499412933957829,
                    12344152745192254056,
                    1185193310574937231,
                    760964259656302494,
                ]),
            ])),
            y: builder.constant_nonnative_ext2(QuadraticExtension::<Bn128Base>([
                Bn128Base([
                    16827884672622421998,
                    756648877887862755,
                    18069298113966277418,
                    2110768940310013157,
                ]),
                Bn128Base([
                    12195099017078129020,
                    6997443175976044100,
                    15957581681657247863,
                    752644145961255405,
                ]),
            ])),
            z: builder.constant_nonnative_ext2(QuadraticExtension::<Bn128Base>([
                Bn128Base([
                    12079780699228388722,
                    791215766957020566,
                    2914756960274132770,
                    2602717870663046513,
                ]),
                Bn128Base([
                    12691905162280913768,
                    89920551545646552,
                    12941976487854615151,
                    2355989044724612682,
                ]),
            ])),
        };
        let q_affine = builder.to_affine_g2::<G2, Bn128Base>(&q);

        let x_expected = builder.constant_nonnative_ext12(DodecicExtension::<Bn128Base>([
            Bn128Base([
                5261791323882946788,
                5969279653909130133,
                13914067258383528210,
                94138518832923322,
            ]),
            Bn128Base([
                16452828235560020136,
                14277920321324140450,
                1808868257472119675,
                34528199959501362,
            ]),
            Bn128Base([
                18153774717408091761,
                4960813716655447740,
                16877776237373176286,
                111333703937892795,
            ]),
            Bn128Base([
                6177369533740206595,
                5540475544632735388,
                18239293933561841014,
                2106733616315301007,
            ]),
            Bn128Base([
                12051797884938972865,
                5452376490073186411,
                13624941770027287332,
                2556206152101805306,
            ]),
            Bn128Base([
                12875218175083744969,
                18411108459922848687,
                16205159152680096724,
                2298321485788462962,
            ]),
            Bn128Base([
                14609934753813766369,
                10831492163493656847,
                9520417608604346386,
                3185244767883521333,
            ]),
            Bn128Base([
                1210469375740710922,
                12695443078599703490,
                15456619824566231090,
                1318481115027774681,
            ]),
            Bn128Base([
                12407907403893432531,
                2577431929064026945,
                13354667077106593055,
                687277024136764940,
            ]),
            Bn128Base([
                16854887897954252879,
                12456401038131277336,
                4434193903233473879,
                1222410746383484321,
            ]),
            Bn128Base([
                14754110002434578184,
                3232557947137383979,
                560992349178873120,
                3162237541859216066,
            ]),
            Bn128Base([
                4982245430574873546,
                2614584005832853337,
                14785904332481227781,
                1602384300921012077,
            ]),
        ]));

        let x = builder.pairing::<G1, G2, Bn128Base>(&p, &q_affine);
        builder.connect_nonnative_ext12(&x_expected, &x);

        let timing = TimingTree::new("build", Level::Info);
        let data = builder.build::<C>();
        timing.print();
        let timing = TimingTree::new("prove", Level::Info);
        let proof = data.prove(pw).unwrap();
        timing.print();
        let timing = TimingTree::new("verify", Level::Info);
        let res = data.verify(proof);
        timing.print();

        res
    }
}
