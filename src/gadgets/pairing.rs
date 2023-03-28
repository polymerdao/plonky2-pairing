use crate::field::extension::dodecic::DodecicExtension;
use crate::field::extension::quadratic::QuadraticExtension;
use crate::gadgets::g1::AffinePointTarget;
use crate::gadgets::g2::AffinePointTargetG2;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_ecdsa::curve::curve_types::Curve;
use plonky2_field::extension::Extendable;
use plonky2_field::types::PrimeField;

pub trait CircuitBuilderPairing<F: RichField + Extendable<D>, const D: usize> {
    fn pairing<
        C1: Curve,
        C2: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2> + Extendable<6> + Extendable<12>,
    >(
        &mut self,
        p: &AffinePointTarget<C1>,
        q: &AffinePointTargetG2<FF>,
    ) -> DodecicExtension<FF>;
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilderPairing<F, D>
    for CircuitBuilder<F, D>
{
    fn pairing<
        C1: Curve,
        C2: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2> + Extendable<6> + Extendable<12>,
    >(
        &mut self,
        p: &AffinePointTarget<C1>,
        q: &AffinePointTargetG2<FF>,
    ) -> DodecicExtension<FF> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use crate::curve::g1::G1;
    use crate::curve::g2::G2;
    use crate::field::bn128_base::Bn128Base;
    use crate::field::extension::dodecic::DodecicExtension;
    use crate::gadgets::g1::CircuitBuilderCurve;
    use crate::gadgets::g2::CircuitBuilderCurveG2;
    use crate::gadgets::nonnative_fp12::CircuitBuilderNonNativeExt12;
    use anyhow::Result;
    use log::{Level, LevelFilter};
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2_ecdsa::curve::curve_types::Curve;
    use plonky2_field::types::Sample;

    #[test]
    fn test_pairing() -> Result<()> {
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

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof)
    }
}
