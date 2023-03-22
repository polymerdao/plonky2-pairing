#[cfg(test)]
mod tests {
    use core::ops::Neg;

    use crate::curve::g1::G1;
    use crate::field::bn128_base::Bn128Base;
    use crate::field::bn128_scalar::Bn128Scalar;
    use crate::gadgets::curve::CircuitBuilderCurve;
    use crate::gadgets::nonnative_fp::CircuitBuilderNonNative;
    use anyhow::Result;
    use plonky2::field::types::{Field, Sample};
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2_ecdsa::curve::curve_types::{AffinePoint, Curve, CurveScalar};

    #[test]
    fn test_curve_point_is_valid() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_ecc_config();

        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let g = G1::GENERATOR_AFFINE;
        let g_target = builder.constant_affine_point(g);
        let neg_g_target = builder.curve_neg(&g_target);

        builder.curve_assert_valid(&g_target);
        builder.curve_assert_valid(&neg_g_target);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof)
    }

    #[test]
    #[should_panic]
    fn test_curve_point_is_not_valid() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_ecc_config();

        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let g = G1::GENERATOR_AFFINE;
        let not_g = AffinePoint::<G1> {
            x: g.x,
            y: g.y + Bn128Base::ONE,
            zero: g.zero,
        };
        let not_g_target = builder.constant_affine_point(not_g);

        builder.curve_assert_valid(&not_g_target);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof).unwrap()
    }

    #[test]
    fn test_curve_double() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_ecc_config();

        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let g = G1::GENERATOR_AFFINE;
        let g_target = builder.constant_affine_point(g);
        let neg_g_target = builder.curve_neg(&g_target);

        let double_g = g.double();
        let double_g_expected = builder.constant_affine_point(double_g);
        builder.curve_assert_valid(&double_g_expected);

        let double_neg_g = (-g).double();
        let double_neg_g_expected = builder.constant_affine_point(double_neg_g);
        builder.curve_assert_valid(&double_neg_g_expected);

        let double_g_actual = builder.curve_double(&g_target);
        let double_neg_g_actual = builder.curve_double(&neg_g_target);
        builder.curve_assert_valid(&double_g_actual);
        builder.curve_assert_valid(&double_neg_g_actual);

        builder.connect_affine_point(&double_g_expected, &double_g_actual);
        builder.connect_affine_point(&double_neg_g_expected, &double_neg_g_actual);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof)
    }

    #[test]
    fn test_curve_add() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_ecc_config();

        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let g = G1::GENERATOR_AFFINE;
        let double_g = g.double();
        let g_plus_2g = (g + double_g).to_affine();
        let g_plus_2g_expected = builder.constant_affine_point(g_plus_2g);
        builder.curve_assert_valid(&g_plus_2g_expected);

        let g_target = builder.constant_affine_point(g);
        let double_g_target = builder.curve_double(&g_target);
        let g_plus_2g_actual = builder.curve_add(&g_target, &double_g_target);
        builder.curve_assert_valid(&g_plus_2g_actual);

        builder.connect_affine_point(&g_plus_2g_expected, &g_plus_2g_actual);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof)
    }

    #[test]
    fn test_curve_conditional_add() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_ecc_config();

        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let g = G1::GENERATOR_AFFINE;
        let double_g = g.double();
        let g_plus_2g = (g + double_g).to_affine();
        let g_plus_2g_expected = builder.constant_affine_point(g_plus_2g);

        let g_expected = builder.constant_affine_point(g);
        let double_g_target = builder.curve_double(&g_expected);
        let t = builder._true();
        let f = builder._false();
        let g_plus_2g_actual = builder.curve_conditional_add(&g_expected, &double_g_target, t);
        let g_actual = builder.curve_conditional_add(&g_expected, &double_g_target, f);

        builder.connect_affine_point(&g_plus_2g_expected, &g_plus_2g_actual);
        builder.connect_affine_point(&g_expected, &g_actual);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof)
    }

    #[test]
    #[ignore]
    fn test_curve_mul() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_ecc_config();

        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let g = G1::GENERATOR_PROJECTIVE.to_affine();
        let five = Bn128Scalar::from_canonical_usize(5);
        let neg_five = five.neg();
        let neg_five_scalar = CurveScalar::<G1>(neg_five);
        let neg_five_g = (neg_five_scalar * g.to_projective()).to_affine();
        let neg_five_g_expected = builder.constant_affine_point(neg_five_g);
        builder.curve_assert_valid(&neg_five_g_expected);

        let g_target = builder.constant_affine_point(g);
        let neg_five_target = builder.constant_nonnative(neg_five);
        let neg_five_g_actual = builder.curve_scalar_mul(&g_target, &neg_five_target);
        builder.curve_assert_valid(&neg_five_g_actual);

        builder.connect_affine_point(&neg_five_g_expected, &neg_five_g_actual);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof)
    }

    #[test]
    #[ignore]
    fn test_curve_random() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_ecc_config();

        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let rando = (CurveScalar(Bn128Scalar::rand()) * G1::GENERATOR_PROJECTIVE).to_affine();
        let randot = builder.constant_affine_point(rando);

        let two_target = builder.constant_nonnative(Bn128Scalar::TWO);
        let randot_doubled = builder.curve_double(&randot);
        let randot_times_two = builder.curve_scalar_mul(&randot, &two_target);
        builder.connect_affine_point(&randot_doubled, &randot_times_two);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof)
    }
}
