use crate::field::extension::quadratic::QuadraticExtension;
use crate::gadgets::nonnative_fp2::{CircuitBuilderNonNativeExt2, NonNativeTargetExt2};
use core::fmt::Debug;
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_ecdsa::curve::curve_types::{AffinePoint, Curve};
use plonky2_field::types::{Field, PrimeField};

/// A Target representing an affine point on the curve `C`. We use incomplete arithmetic for efficiency,
/// so we assume these points are not zero.
#[derive(Clone, Debug)]
pub struct AffinePointTargetG2<FF: Field> {
    pub x: NonNativeTargetExt2<FF>,
    pub y: NonNativeTargetExt2<FF>,
}

pub trait CircuitBuilderCurveG2<F: RichField + Extendable<D>, const D: usize> {
    fn constant_affine_point_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        point: AffinePoint<C>,
    ) -> AffinePointTargetG2<FF>;

    fn connect_affine_point_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        lhs: &AffinePointTargetG2<FF>,
        rhs: &AffinePointTargetG2<FF>,
    );
    //
    // fn add_virtual_affine_point_target_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(&mut self) -> AffinePointTargetG2<FF>;
    //
    fn curve_assert_valid_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p: &AffinePointTargetG2<FF>,
    );

    fn curve_neg_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
        &mut self,
        p: &AffinePointTargetG2<FF>,
    ) -> AffinePointTargetG2<FF>;
    //
    // fn curve_conditional_neg_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
    //     &mut self,
    //     p: &AffinePointTargetG2<FF>,
    //     b: BoolTarget,
    // ) -> AffinePointTargetG2<FF>;
    //
    // fn curve_double_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(&mut self, p: &AffinePointTargetG2<FF>) -> AffinePointTargetG2<FF>;
    //
    // fn curve_repeated_double_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
    //     &mut self,
    //     p: &AffinePointTargetG2<FF>,
    //     n: usize,
    // ) -> AffinePointTargetG2<FF>;
    //
    // /// Add two points, which are assumed to be non-equal.
    // fn curve_add_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
    //     &mut self,
    //     p1: &AffinePointTargetG2<FF>,
    //     p2: &AffinePointTargetG2<FF>,
    // ) -> AffinePointTargetG2<FF>;
    //
    // fn curve_conditional_add_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
    //     &mut self,
    //     p1: &AffinePointTargetG2<FF>,
    //     p2: &AffinePointTargetG2<FF>,
    //     b: BoolTarget,
    // ) -> AffinePointTargetG2<FF>;
    //
    // fn curve_scalar_mul_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
    //     &mut self,
    //     p: &AffinePointTargetG2<FF>,
    //     n: &NonNativeTarget<C::ScalarField>,
    // ) -> AffinePointTargetG2<FF>;
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilderCurveG2<F, D>
    for CircuitBuilder<F, D>
{
    fn constant_affine_point_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        point: AffinePoint<C>,
    ) -> AffinePointTargetG2<FF> {
        debug_assert!(!point.zero);
        AffinePointTargetG2 {
            x: self.constant_nonnative_ext2(point.x),
            y: self.constant_nonnative_ext2(point.y),
        }
    }

    fn connect_affine_point_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        lhs: &AffinePointTargetG2<FF>,
        rhs: &AffinePointTargetG2<FF>,
    ) {
        self.connect_nonnative_ext2(&lhs.x, &rhs.x);
        self.connect_nonnative_ext2(&lhs.y, &rhs.y);
    }

    //
    // fn add_virtual_affine_point_target_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(&mut self) -> AffinePointTargetG2<FF> {
    //     let x = self.add_virtual_nonnative_target();
    //     let y = self.add_virtual_nonnative_target();
    //
    //     AffinePointTargetG2 { x, y }
    // }
    //
    fn curve_assert_valid_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p: &AffinePointTargetG2<FF>,
    ) {
        let b = self.constant_nonnative_ext2(C::B);

        let y_squared = self.mul_nonnative_ext2(&p.y, &p.y);
        let x_squared = self.mul_nonnative_ext2(&p.x, &p.x);
        let x_cubed = self.mul_nonnative_ext2(&x_squared, &p.x);
        let rhs = self.add_nonnative_ext2(&x_cubed, &b);

        self.connect_nonnative_ext2(&y_squared, &rhs);
    }

    fn curve_neg_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p: &AffinePointTargetG2<FF>,
    ) -> AffinePointTargetG2<FF> {
        let neg_y = self.neg_nonnative_ext2(&p.y);
        AffinePointTargetG2 {
            x: p.x.clone(),
            y: neg_y,
        }
    }

    // fn curve_conditional_neg_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
    //     &mut self,
    //     p: &AffinePointTargetG2<FF>,
    //     b: BoolTarget,
    // ) -> AffinePointTargetG2<FF> {
    //     AffinePointTargetG2 {
    //         x: p.x.clone(),
    //         y: self.nonnative_conditional_neg(&p.y, b),
    //     }
    // }
    //
    // fn curve_double_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(&mut self, p: &AffinePointTargetG2<FF>) -> AffinePointTargetG2<FF> {
    //     let AffinePointTargetG2 { x, y } = p;
    //     let double_y = self.add_nonnative(y, y);
    //     let inv_double_y = self.inv_nonnative(&double_y);
    //     let x_squared = self.mul_nonnative(x, x);
    //     let double_x_squared = self.add_nonnative(&x_squared, &x_squared);
    //     let triple_x_squared = self.add_nonnative(&double_x_squared, &x_squared);
    //
    //     let a = self.constant_nonnative(C::A);
    //     let triple_xx_a = self.add_nonnative(&triple_x_squared, &a);
    //     let lambda = self.mul_nonnative(&triple_xx_a, &inv_double_y);
    //     let lambda_squared = self.mul_nonnative(&lambda, &lambda);
    //     let x_double = self.add_nonnative(x, x);
    //
    //     let x3 = self.sub_nonnative(&lambda_squared, &x_double);
    //
    //     let x_diff = self.sub_nonnative(x, &x3);
    //     let lambda_x_diff = self.mul_nonnative(&lambda, &x_diff);
    //
    //     let y3 = self.sub_nonnative(&lambda_x_diff, y);
    //
    //     AffinePointTargetG2 { x: x3, y: y3 }
    // }
    //
    // fn curve_repeated_double_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
    //     &mut self,
    //     p: &AffinePointTargetG2<FF>,
    //     n: usize,
    // ) -> AffinePointTargetG2<FF> {
    //     let mut result = p.clone();
    //
    //     for _ in 0..n {
    //         result = self.curve_double(&result);
    //     }
    //
    //     result
    // }
    //
    // fn curve_add_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
    //     &mut self,
    //     p1: &AffinePointTargetG2<FF>,
    //     p2: &AffinePointTargetG2<FF>,
    // ) -> AffinePointTargetG2<FF> {
    //     let AffinePointTargetG2 { x: x1, y: y1 } = p1;
    //     let AffinePointTargetG2 { x: x2, y: y2 } = p2;
    //
    //     let u = self.sub_nonnative(y2, y1);
    //     let v = self.sub_nonnative(x2, x1);
    //     let v_inv = self.inv_nonnative(&v);
    //     let s = self.mul_nonnative(&u, &v_inv);
    //     let s_squared = self.mul_nonnative(&s, &s);
    //     let x_sum = self.add_nonnative(x2, x1);
    //     let x3 = self.sub_nonnative(&s_squared, &x_sum);
    //     let x_diff = self.sub_nonnative(x1, &x3);
    //     let prod = self.mul_nonnative(&s, &x_diff);
    //     let y3 = self.sub_nonnative(&prod, y1);
    //
    //     AffinePointTargetG2 { x: x3, y: y3 }
    // }
    //
    // fn curve_conditional_add_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
    //     &mut self,
    //     p1: &AffinePointTargetG2<FF>,
    //     p2: &AffinePointTargetG2<FF>,
    //     b: BoolTarget,
    // ) -> AffinePointTargetG2<FF> {
    //     let not_b = self.not(b);
    //     let sum = self.curve_add(p1, p2);
    //     let x_if_true = self.mul_nonnative_by_bool(&sum.x, b);
    //     let y_if_true = self.mul_nonnative_by_bool(&sum.y, b);
    //     let x_if_false = self.mul_nonnative_by_bool(&p1.x, not_b);
    //     let y_if_false = self.mul_nonnative_by_bool(&p1.y, not_b);
    //
    //     let x = self.add_nonnative(&x_if_true, &x_if_false);
    //     let y = self.add_nonnative(&y_if_true, &y_if_false);
    //
    //     AffinePointTargetG2 { x, y }
    // }
    //
    // fn curve_scalar_mul_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
    //     &mut self,
    //     p: &AffinePointTargetG2<FF>,
    //     n: &NonNativeTarget<C::ScalarField>,
    // ) -> AffinePointTargetG2<FF> {
    //     let bits = self.split_nonnative_to_bits(n);
    //
    //     let rando = (CurveScalar(C::ScalarField::rand()) * C::GENERATOR_PROJECTIVE).to_affine();
    //     let randot = self.constant_affine_point(rando);
    //     // Result starts at `rando`, which is later subtracted, because we don't support arithmetic with the zero point.
    //     let mut result = self.add_virtual_affine_point_target();
    //     self.connect_affine_point(&randot, &result);
    //
    //     let mut two_i_times_p = self.add_virtual_affine_point_target();
    //     self.connect_affine_point(p, &two_i_times_p);
    //
    //     for &bit in bits.iter() {
    //         let not_bit = self.not(bit);
    //
    //         let result_plus_2_i_p = self.curve_add(&result, &two_i_times_p);
    //
    //         let new_x_if_bit = self.mul_nonnative_by_bool(&result_plus_2_i_p.x, bit);
    //         let new_x_if_not_bit = self.mul_nonnative_by_bool(&result.x, not_bit);
    //         let new_y_if_bit = self.mul_nonnative_by_bool(&result_plus_2_i_p.y, bit);
    //         let new_y_if_not_bit = self.mul_nonnative_by_bool(&result.y, not_bit);
    //
    //         let new_x = self.add_nonnative(&new_x_if_bit, &new_x_if_not_bit);
    //         let new_y = self.add_nonnative(&new_y_if_bit, &new_y_if_not_bit);
    //
    //         result = AffinePointTargetG2 { x: new_x, y: new_y };
    //
    //         two_i_times_p = self.curve_double(&two_i_times_p);
    //     }
    //
    //     // Subtract off result's intial value of `rando`.
    //     let neg_r = self.curve_neg(&randot);
    //     result = self.curve_add(&result, &neg_r);
    //
    //     result
    // }
}

#[cfg(test)]
mod tests {
    use crate::curve::g2::G2;
    use crate::field::bn128_base::Bn128Base;
    use crate::gadgets::g2::CircuitBuilderCurveG2;
    use anyhow::Result;
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2_ecdsa::curve::curve_types::Curve;

    #[test]
    fn test_curve_point_is_valid() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_ecc_config();

        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let g = G2::GENERATOR_AFFINE;
        let g_target = builder.constant_affine_point_g2(g);
        let neg_g_target = builder.curve_neg_g2::<G2, Bn128Base>(&g_target);

        builder.curve_assert_valid_g2::<G2, Bn128Base>(&g_target);
        builder.curve_assert_valid_g2::<G2, Bn128Base>(&neg_g_target);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof)
    }
}
