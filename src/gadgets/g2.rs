use crate::field::extension::dodecic::DodecicExtension;
use crate::field::extension::quadratic::QuadraticExtension;
use crate::gadgets::g1::AffinePointTarget;
use crate::gadgets::nonnative_fp::{CircuitBuilderNonNative, NonNativeTarget};
use crate::gadgets::nonnative_fp12::{CircuitBuilderNonNativeExt12, NonNativeTargetExt12};
use crate::gadgets::nonnative_fp2::{CircuitBuilderNonNativeExt2, NonNativeTargetExt2};
use core::fmt::Debug;
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::BoolTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_ecdsa::curve::curve_types::{AffinePoint, Curve, CurveScalar};
use plonky2_field::types::{Field, PrimeField, Sample};

const ATE_LOOP_COUNT: [u64; 4] = [
    0x9d797039be763ba8,
    0x0000000000000001,
    0x0000000000000000,
    0x0000000000000000,
];

/// A Target representing an affine point on the curve `C`. We use incomplete arithmetic for efficiency,
/// so we assume these points are not zero.
#[derive(Clone, Debug)]
pub struct AffinePointTargetG2<FF: Field> {
    pub x: NonNativeTargetExt2<FF>,
    pub y: NonNativeTargetExt2<FF>,
}

pub struct JacobianPointTargetG2<FF: Field> {
    pub x: NonNativeTargetExt2<FF>,
    pub y: NonNativeTargetExt2<FF>,
    pub z: NonNativeTargetExt2<FF>,
}

#[derive(Clone, Debug)]
pub struct EllCoefficientsTarget<FF: Field> {
    pub ell_0: NonNativeTargetExt2<FF>,
    pub ell_vw: NonNativeTargetExt2<FF>,
    pub ell_vv: NonNativeTargetExt2<FF>,
}

#[derive(Clone, Debug)]
pub struct G2PreComputeTarget<FF: Field> {
    pub q: AffinePointTargetG2<FF>,
    pub coeffs: Vec<EllCoefficientsTarget<FF>>,
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

    fn add_virtual_affine_point_target_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
    ) -> AffinePointTargetG2<FF>;

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

    fn curve_conditional_neg_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p: &AffinePointTargetG2<FF>,
        b: BoolTarget,
    ) -> AffinePointTargetG2<FF>;

    fn curve_double_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p: &AffinePointTargetG2<FF>,
    ) -> AffinePointTargetG2<FF>;

    fn curve_repeated_double_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p: &AffinePointTargetG2<FF>,
        n: usize,
    ) -> AffinePointTargetG2<FF>;

    /// Add two points, which are assumed to be non-equal.
    fn curve_add_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
        &mut self,
        p1: &AffinePointTargetG2<FF>,
        p2: &AffinePointTargetG2<FF>,
    ) -> AffinePointTargetG2<FF>;

    fn curve_conditional_add_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p1: &AffinePointTargetG2<FF>,
        p2: &AffinePointTargetG2<FF>,
        b: BoolTarget,
    ) -> AffinePointTargetG2<FF>;

    fn curve_scalar_mul_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p: &AffinePointTargetG2<FF>,
        n: &NonNativeTarget<C::ScalarField>,
    ) -> AffinePointTargetG2<FF>;

    fn precompute<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
        &mut self,
        p: &AffinePointTargetG2<FF>,
    ) -> G2PreComputeTarget<FF>;

    fn to_jacobian_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p: &AffinePointTargetG2<FF>,
    ) -> JacobianPointTargetG2<FF>;

    fn to_affine_g2<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
        &mut self,
        p: &JacobianPointTargetG2<FF>,
    ) -> AffinePointTargetG2<FF>;

    fn doubling_step_for_flipped_miller_loop<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p: &JacobianPointTargetG2<FF>,
    ) -> (JacobianPointTargetG2<FF>, EllCoefficientsTarget<FF>);

    fn mixed_addition_step_for_flipped_miller_loop<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        r: &JacobianPointTargetG2<FF>,
        base: &AffinePointTargetG2<FF>,
    ) -> (JacobianPointTargetG2<FF>, EllCoefficientsTarget<FF>);

    fn mul_by_q<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
        &mut self,
        p: &AffinePointTargetG2<FF>,
    ) -> AffinePointTargetG2<FF>;

    fn miller_loop<
        C: Curve<BaseField = FF>,
        FF: PrimeField + Extendable<2> + Extendable<6> + Extendable<12>,
    >(
        &mut self,
        g1: &AffinePointTarget<C>,
        precomp: &G2PreComputeTarget<FF>,
    ) -> NonNativeTargetExt12<FF>;
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

    fn add_virtual_affine_point_target_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
    ) -> AffinePointTargetG2<FF> {
        let x = self.add_virtual_nonnative_ext2_target();
        let y = self.add_virtual_nonnative_ext2_target();

        AffinePointTargetG2 { x, y }
    }

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

    fn curve_conditional_neg_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p: &AffinePointTargetG2<FF>,
        b: BoolTarget,
    ) -> AffinePointTargetG2<FF> {
        AffinePointTargetG2 {
            x: p.x.clone(),
            y: self.nonnative_conditional_neg_ext2(&p.y, b),
        }
    }

    fn curve_double_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p: &AffinePointTargetG2<FF>,
    ) -> AffinePointTargetG2<FF> {
        let AffinePointTargetG2 { x, y } = p;
        let double_y = self.add_nonnative_ext2(y, y);
        let inv_double_y = self.inv_nonnative_ext2(&double_y);
        let x_squared = self.mul_nonnative_ext2(x, x);
        let double_x_squared = self.add_nonnative_ext2(&x_squared, &x_squared);
        let triple_x_squared = self.add_nonnative_ext2(&double_x_squared, &x_squared);

        let lambda = self.mul_nonnative_ext2(&triple_x_squared, &inv_double_y);
        let lambda_squared = self.mul_nonnative_ext2(&lambda, &lambda);
        let x_double = self.add_nonnative_ext2(x, x);

        let x3 = self.sub_nonnative_ext2(&lambda_squared, &x_double);

        let x_diff = self.sub_nonnative_ext2(x, &x3);
        let lambda_x_diff = self.mul_nonnative_ext2(&lambda, &x_diff);

        let y3 = self.sub_nonnative_ext2(&lambda_x_diff, y);

        AffinePointTargetG2 { x: x3, y: y3 }
    }

    fn curve_repeated_double_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p: &AffinePointTargetG2<FF>,
        n: usize,
    ) -> AffinePointTargetG2<FF> {
        let mut result = p.clone();

        for _ in 0..n {
            result = self.curve_double_g2::<C, FF>(&result);
        }

        result
    }

    fn curve_add_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p1: &AffinePointTargetG2<FF>,
        p2: &AffinePointTargetG2<FF>,
    ) -> AffinePointTargetG2<FF> {
        let AffinePointTargetG2 { x: x1, y: y1 } = p1;
        let AffinePointTargetG2 { x: x2, y: y2 } = p2;

        let u = self.sub_nonnative_ext2(y2, y1);
        let v = self.sub_nonnative_ext2(x2, x1);
        let v_inv = self.inv_nonnative_ext2(&v);
        let s = self.mul_nonnative_ext2(&u, &v_inv);
        let s_squared = self.mul_nonnative_ext2(&s, &s);
        let x_sum = self.add_nonnative_ext2(x2, x1);
        let x3 = self.sub_nonnative_ext2(&s_squared, &x_sum);
        let x_diff = self.sub_nonnative_ext2(x1, &x3);
        let prod = self.mul_nonnative_ext2(&s, &x_diff);
        let y3 = self.sub_nonnative_ext2(&prod, y1);

        AffinePointTargetG2 { x: x3, y: y3 }
    }

    fn curve_conditional_add_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p1: &AffinePointTargetG2<FF>,
        p2: &AffinePointTargetG2<FF>,
        b: BoolTarget,
    ) -> AffinePointTargetG2<FF> {
        let not_b = self.not(b);
        let sum = self.curve_add_g2::<C, FF>(p1, p2);
        let x_if_true = self.mul_nonnative_by_bool_ext2(&sum.x, b);
        let y_if_true = self.mul_nonnative_by_bool_ext2(&sum.y, b);
        let x_if_false = self.mul_nonnative_by_bool_ext2(&p1.x, not_b);
        let y_if_false = self.mul_nonnative_by_bool_ext2(&p1.y, not_b);

        let x = self.add_nonnative_ext2(&x_if_true, &x_if_false);
        let y = self.add_nonnative_ext2(&y_if_true, &y_if_false);

        AffinePointTargetG2 { x, y }
    }

    fn curve_scalar_mul_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p: &AffinePointTargetG2<FF>,
        n: &NonNativeTarget<C::ScalarField>,
    ) -> AffinePointTargetG2<FF> {
        let bits = self.split_nonnative_to_bits(n);

        let rando = (CurveScalar(C::ScalarField::rand()) * C::GENERATOR_PROJECTIVE).to_affine();
        let randot = self.constant_affine_point_g2(rando);
        // Result starts at `rando`, which is later subtracted, because we don't support arithmetic with the zero point.
        let mut result = self.add_virtual_affine_point_target_g2::<C, FF>();
        self.connect_affine_point_g2::<C, FF>(&randot, &result);

        let mut two_i_times_p = self.add_virtual_affine_point_target_g2::<C, FF>();
        self.connect_affine_point_g2::<C, FF>(p, &two_i_times_p);

        for &bit in bits.iter() {
            let not_bit = self.not(bit);

            let result_plus_2_i_p = self.curve_add_g2::<C, FF>(&result, &two_i_times_p);

            let new_x_if_bit = self.mul_nonnative_by_bool_ext2(&result_plus_2_i_p.x, bit);
            let new_x_if_not_bit = self.mul_nonnative_by_bool_ext2(&result.x, not_bit);
            let new_y_if_bit = self.mul_nonnative_by_bool_ext2(&result_plus_2_i_p.y, bit);
            let new_y_if_not_bit = self.mul_nonnative_by_bool_ext2(&result.y, not_bit);

            let new_x = self.add_nonnative_ext2(&new_x_if_bit, &new_x_if_not_bit);
            let new_y = self.add_nonnative_ext2(&new_y_if_bit, &new_y_if_not_bit);

            result = AffinePointTargetG2 { x: new_x, y: new_y };

            two_i_times_p = self.curve_double_g2::<C, FF>(&two_i_times_p);
        }

        // Subtract off result's intial value of `rando`.
        let neg_r = self.curve_neg_g2::<C, FF>(&randot);
        result = self.curve_add_g2::<C, FF>(&result, &neg_r);

        result
    }

    fn precompute<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
        &mut self,
        p: &AffinePointTargetG2<FF>,
    ) -> G2PreComputeTarget<FF> {
        let mut r = self.to_jacobian_g2::<C, FF>(p);
        let mut coeffs = Vec::with_capacity(102);
        let mut found_one = false;

        for j in ATE_LOOP_COUNT.iter().rev() {
            for i in (0..64).rev() {
                if !found_one {
                    // skips the first bit
                    found_one = (j >> i) & 1 == 1;
                    continue;
                }

                let (r0, coeff) = self.doubling_step_for_flipped_miller_loop::<C, FF>(&r);
                r = r0;
                coeffs.push(coeff);

                if (j >> i) & 1 == 1 {
                    let (r0, coeff) =
                        self.mixed_addition_step_for_flipped_miller_loop::<C, FF>(&r, p);
                    r = r0;
                    coeffs.push(coeff);
                }
            }
        }

        let q1 = self.mul_by_q::<C, FF>(&p);
        let mul_by_q = self.mul_by_q::<C, FF>(&q1);
        let q2 = self.curve_neg_g2::<C, FF>(&mul_by_q);

        let (r0, coeff) = self.mixed_addition_step_for_flipped_miller_loop::<C, FF>(&r, &q1);
        r = r0;
        coeffs.push(coeff);
        let (_, coeff) = self.mixed_addition_step_for_flipped_miller_loop::<C, FF>(&r, &q2);
        coeffs.push(coeff);

        G2PreComputeTarget {
            q: p.clone(),
            coeffs,
        }
    }

    fn to_jacobian_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p: &AffinePointTargetG2<FF>,
    ) -> JacobianPointTargetG2<FF> {
        JacobianPointTargetG2 {
            x: p.x.clone(),
            y: p.y.clone(),
            z: self.constant_nonnative_ext2(QuadraticExtension::ONE),
        }
    }

    fn to_affine_g2<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p: &JacobianPointTargetG2<FF>,
    ) -> AffinePointTargetG2<FF> {
        // TODO: temporary hack
        if p.z.c1.value.limbs.len() == 0 {
            return AffinePointTargetG2 {
                x: p.x.clone(),
                y: p.y.clone(),
            };
        }
        let z_inv = self.inv_nonnative_ext2(&p.z);
        let z_inv_squared = self.mul_nonnative_ext2(&z_inv, &z_inv);
        let x = self.mul_nonnative_ext2(&p.x, &z_inv_squared);
        let z_inv_cubed = self.mul_nonnative_ext2(&z_inv_squared, &z_inv);
        let y = self.mul_nonnative_ext2(&p.y, &z_inv_cubed);

        AffinePointTargetG2 { x, y }
    }

    fn doubling_step_for_flipped_miller_loop<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        p: &JacobianPointTargetG2<FF>,
    ) -> (JacobianPointTargetG2<FF>, EllCoefficientsTarget<FF>) {
        let two_inv = self.constant_nonnative(C::INV_TWO.0[0]);
        let mut a = self.mul_nonnative_ext2(&p.x, &p.y);
        a = self.scale_nonnative_ext2(&a, &two_inv);
        let b = self.squared_nonnative_ext2(&p.y);
        let c = self.squared_nonnative_ext2(&p.z);
        let mut d = self.add_nonnative_ext2(&c, &c);
        d = self.add_nonnative_ext2(&d, &c);
        let mut e = self.constant_nonnative_ext2(C::B);
        e = self.mul_nonnative_ext2(&e, &d);
        let mut f = self.add_nonnative_ext2(&e, &e);
        f = self.add_nonnative_ext2(&f, &e);
        let mut g = self.add_nonnative_ext2(&b, &f);
        g = self.scale_nonnative_ext2(&g, &two_inv);
        let mut h = self.add_nonnative_ext2(&p.y, &p.z);
        h = self.squared_nonnative_ext2(&h);
        h = self.sub_nonnative_ext2(&h, &b);
        h = self.sub_nonnative_ext2(&h, &c);
        let i = self.sub_nonnative_ext2(&e, &b);
        let j = self.squared_nonnative_ext2(&p.x);
        let e_sq = self.squared_nonnative_ext2(&e);

        let mut x = self.sub_nonnative_ext2(&b, &f);
        x = self.mul_nonnative_ext2(&a, &x);
        let mut y = self.squared_nonnative_ext2(&g);
        let mut e_sq_3 = self.add_nonnative_ext2(&e_sq, &e_sq);
        e_sq_3 = self.add_nonnative_ext2(&e_sq_3, &e_sq);
        y = self.sub_nonnative_ext2(&y, &e_sq_3);
        let z = self.mul_nonnative_ext2(&b, &h);

        let ell_0 = self.mul_by_nonresidue_nonnative_ext2(&i);
        let ell_vw = self.neg_nonnative_ext2(&h);
        let mut ell_vv = self.add_nonnative_ext2(&j, &j);
        ell_vv = self.add_nonnative_ext2(&ell_vv, &j);

        (
            JacobianPointTargetG2 { x, y, z },
            EllCoefficientsTarget {
                ell_0,
                ell_vw,
                ell_vv,
            },
        )
    }

    fn mixed_addition_step_for_flipped_miller_loop<
        C: Curve<BaseField = QuadraticExtension<FF>>,
        FF: PrimeField + Extendable<2>,
    >(
        &mut self,
        r: &JacobianPointTargetG2<FF>,
        base: &AffinePointTargetG2<FF>,
    ) -> (JacobianPointTargetG2<FF>, EllCoefficientsTarget<FF>) {
        let mut d = self.mul_nonnative_ext2(&r.z, &base.x);
        d = self.sub_nonnative_ext2(&r.x, &d);
        let mut e = self.mul_nonnative_ext2(&r.z, &base.y);
        e = self.sub_nonnative_ext2(&r.y, &e);
        let f = self.squared_nonnative_ext2(&d);
        let g = self.squared_nonnative_ext2(&e);
        let h = self.mul_nonnative_ext2(&d, &f);
        let i = self.mul_nonnative_ext2(&r.x, &f);
        let mut j = self.mul_nonnative_ext2(&r.z, &g);
        j = self.add_nonnative_ext2(&j, &h);
        j = self.sub_nonnative_ext2(&j, &i);
        j = self.sub_nonnative_ext2(&j, &i);
        let x = self.mul_nonnative_ext2(&d, &j);
        let mut y = self.sub_nonnative_ext2(&i, &j);
        y = self.mul_nonnative_ext2(&e, &y);
        let h_y = self.mul_nonnative_ext2(&h, &r.y);
        y = self.sub_nonnative_ext2(&y, &h_y);
        let z = self.mul_nonnative_ext2(&r.z, &h);
        let e_x = self.mul_nonnative_ext2(&e, &base.x);
        let d_y = self.mul_nonnative_ext2(&d, &base.y);
        let mut ell_0 = self.sub_nonnative_ext2(&e_x, &d_y);
        ell_0 = self.mul_by_nonresidue_nonnative_ext2(&ell_0);
        let ell_vv = self.neg_nonnative_ext2(&e);
        let ell_vw = d;
        (
            JacobianPointTargetG2 { x, y, z },
            EllCoefficientsTarget {
                ell_0,
                ell_vv,
                ell_vw,
            },
        )
    }

    fn mul_by_q<C: Curve<BaseField = QuadraticExtension<FF>>, FF: PrimeField + Extendable<2>>(
        &mut self,
        p: &AffinePointTargetG2<FF>,
    ) -> AffinePointTargetG2<FF> {
        let x_frobenius = self.frobenius_map_nonnative_ext2(&p.x, 1);
        let y_frobenius = self.frobenius_map_nonnative_ext2(&p.y, 1);
        let twist_mul_by_q_x = self.constant_nonnative_ext2(C::TWIST_MUL_BY_Q_X);
        let twist_mul_by_q_y = self.constant_nonnative_ext2(C::TWIST_MUL_BY_Q_Y);
        AffinePointTargetG2 {
            x: self.mul_nonnative_ext2(&twist_mul_by_q_x, &x_frobenius),
            y: self.mul_nonnative_ext2(&twist_mul_by_q_y, &y_frobenius),
        }
    }

    fn miller_loop<
        C: Curve<BaseField = FF>,
        FF: PrimeField + Extendable<2> + Extendable<6> + Extendable<12>,
    >(
        &mut self,
        g1: &AffinePointTarget<C>,
        precomp: &G2PreComputeTarget<FF>,
    ) -> NonNativeTargetExt12<FF> {
        let mut f = self.constant_nonnative_ext12(DodecicExtension::ONE);
        let mut idx = 0;
        let mut found_one = false;

        for j in ATE_LOOP_COUNT.iter().rev() {
            for i in (0..64).rev() {
                if !found_one {
                    // skips the first bit
                    found_one = (j >> i) & 1 == 1;
                    continue;
                }

                let c = &precomp.coeffs[idx];
                idx += 1;
                f = self.squared_nonnative_ext12(&f);
                let ell_vw = self.scale_nonnative_ext2(&c.ell_vw, &g1.y);
                let ell_vv = self.scale_nonnative_ext2(&c.ell_vv, &g1.x);
                f = self.mul_by_024(&f, &c.ell_0, &ell_vw, &ell_vv);

                if (j >> i) & 1 == 1 {
                    let c = &precomp.coeffs[idx];
                    idx += 1;
                    let ell_vw = self.scale_nonnative_ext2(&c.ell_vw, &g1.y);
                    let ell_vv = self.scale_nonnative_ext2(&c.ell_vv, &g1.x);
                    f = self.mul_by_024(&f, &c.ell_0, &ell_vw, &ell_vv);
                }
            }
        }

        let c = &precomp.coeffs[idx];
        idx += 1;
        let ell_vw = self.scale_nonnative_ext2(&c.ell_vw, &g1.y);
        let ell_vv = self.scale_nonnative_ext2(&c.ell_vv, &g1.x);
        f = self.mul_by_024(&f, &c.ell_0, &ell_vw, &ell_vv);

        let c = &precomp.coeffs[idx];
        let ell_vw = self.scale_nonnative_ext2(&c.ell_vw, &g1.y);
        let ell_vv = self.scale_nonnative_ext2(&c.ell_vv, &g1.x);
        f = self.mul_by_024(&f, &c.ell_0, &ell_vw, &ell_vv);

        f
    }
}

#[cfg(test)]
mod tests {
    use crate::curve::g1::G1;
    use crate::curve::g2::G2;
    use crate::field::bn128_base::Bn128Base;
    use crate::field::bn128_scalar::Bn128Scalar;
    use crate::field::extension::dodecic::DodecicExtension;
    use crate::field::extension::quadratic::QuadraticExtension;
    use crate::gadgets::g1::AffinePointTarget;
    use crate::gadgets::g2::{
        AffinePointTargetG2, CircuitBuilderCurveG2, EllCoefficientsTarget, JacobianPointTargetG2,
    };
    use crate::gadgets::nonnative_fp::CircuitBuilderNonNative;
    use crate::gadgets::nonnative_fp12::CircuitBuilderNonNativeExt12;
    use crate::gadgets::nonnative_fp2::CircuitBuilderNonNativeExt2;
    use anyhow::Result;
    use log::LevelFilter;
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2_ecdsa::curve::curve_types::{AffinePoint, Curve, CurveScalar};
    use plonky2_field::types::Field;
    use std::ops::Neg;

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

    #[test]
    #[should_panic]
    fn test_curve_point_is_not_valid() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_ecc_config();

        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let g = G2::GENERATOR_AFFINE;
        let not_g = AffinePoint::<G2> {
            x: g.x,
            y: g.y + QuadraticExtension::<Bn128Base>::ONE,
            zero: g.zero,
        };
        let not_g_target = builder.constant_affine_point_g2(not_g);

        builder.curve_assert_valid_g2::<G2, Bn128Base>(&not_g_target);

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

        let g = G2::GENERATOR_AFFINE;
        let g_target = builder.constant_affine_point_g2(g);
        let neg_g_target = builder.curve_neg_g2::<G2, Bn128Base>(&g_target);

        let double_g = g.double();
        let double_g_expected = builder.constant_affine_point_g2(double_g);
        builder.curve_assert_valid_g2::<G2, Bn128Base>(&double_g_expected);

        let double_neg_g = (-g).double();
        let double_neg_g_expected = builder.constant_affine_point_g2(double_neg_g);
        builder.curve_assert_valid_g2::<G2, Bn128Base>(&double_neg_g_expected);

        let double_g_actual = builder.curve_double_g2::<G2, Bn128Base>(&g_target);
        let double_neg_g_actual = builder.curve_double_g2::<G2, Bn128Base>(&neg_g_target);
        builder.curve_assert_valid_g2::<G2, Bn128Base>(&double_g_actual);
        builder.curve_assert_valid_g2::<G2, Bn128Base>(&double_neg_g_actual);

        builder.connect_affine_point_g2::<G2, Bn128Base>(&double_g_expected, &double_g_actual);
        builder
            .connect_affine_point_g2::<G2, Bn128Base>(&double_neg_g_expected, &double_neg_g_actual);

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

        let g = G2::GENERATOR_AFFINE;
        let double_g = g.double();
        let g_plus_2g = (g + double_g).to_affine();
        let g_plus_2g_expected = builder.constant_affine_point_g2(g_plus_2g);
        builder.curve_assert_valid_g2::<G2, Bn128Base>(&g_plus_2g_expected);

        let g_target = builder.constant_affine_point_g2(g);
        let double_g_target = builder.curve_double_g2::<G2, Bn128Base>(&g_target);
        let g_plus_2g_actual = builder.curve_add_g2::<G2, Bn128Base>(&g_target, &double_g_target);
        builder.curve_assert_valid_g2::<G2, Bn128Base>(&g_plus_2g_actual);

        builder.connect_affine_point_g2::<G2, Bn128Base>(&g_plus_2g_expected, &g_plus_2g_actual);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof)
    }

    #[test]
    #[ignore]
    fn test_curve_mul() -> Result<()> {
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

        let g = G2::GENERATOR_PROJECTIVE.to_affine();
        let five = Bn128Scalar::from_canonical_usize(5);
        let neg_five = five.neg();
        let neg_five_scalar = CurveScalar::<G2>(neg_five);
        let neg_five_g = (neg_five_scalar * g.to_projective()).to_affine();
        let neg_five_g_expected = builder.constant_affine_point_g2(neg_five_g);
        builder.curve_assert_valid_g2::<G2, Bn128Base>(&neg_five_g_expected);

        let g_target = builder.constant_affine_point_g2(g);
        let neg_five_target = builder.constant_nonnative(neg_five);
        let neg_five_g_actual =
            builder.curve_scalar_mul_g2::<G2, Bn128Base>(&g_target, &neg_five_target);
        builder.curve_assert_valid_g2::<G2, Bn128Base>(&neg_five_g_actual);

        builder.connect_affine_point_g2::<G2, Bn128Base>(&neg_five_g_expected, &neg_five_g_actual);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof)
    }

    #[test]
    #[ignore]
    fn test_precompute() -> Result<()> {
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

        let g = JacobianPointTargetG2 {
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
        let g_affine = builder.to_affine_g2::<G2, Bn128Base>(&g);

        let g_precomputed = builder.precompute::<G2, Bn128Base>(&g_affine);

        let q_expected = AffinePointTargetG2 {
            x: builder.constant_nonnative_ext2(QuadraticExtension::<Bn128Base>([
                Bn128Base([
                    11006543346086653583,
                    6918991450089238666,
                    18279842395430417956,
                    1732640417518178472,
                ]),
                Bn128Base([
                    11517548492582810861,
                    9169073428047311021,
                    9099478545610137041,
                    2335497441439112195,
                ]),
            ])),
            y: builder.constant_nonnative_ext2(QuadraticExtension::<Bn128Base>([
                Bn128Base([
                    8576222689638546622,
                    8183935398600054925,
                    8263144044154228149,
                    3015959802943919691,
                ]),
                Bn128Base([
                    13468896920756445043,
                    11126130999041690047,
                    2537329689975352328,
                    3196716715143124236,
                ]),
            ])),
        };
        builder.connect_affine_point_g2::<G2, Bn128Base>(&q_expected, &g_precomputed.q);

        let coeff_expected_0 = EllCoefficientsTarget {
            ell_0: builder.constant_nonnative_ext2(QuadraticExtension::<Bn128Base>([
                Bn128Base([
                    17277199671608171260,
                    7534830700521395156,
                    692817802423834870,
                    2609448412801810189,
                ]),
                Bn128Base([
                    5389190879121150457,
                    187941817706892431,
                    15071613302643113350,
                    2419974544044211348,
                ]),
            ])),
            ell_vw: builder.constant_nonnative_ext2(QuadraticExtension::<Bn128Base>([
                Bn128Base([
                    9959532436991770898,
                    5466377491755656191,
                    10036095814240933200,
                    942076927718101948,
                ]),
                Bn128Base([
                    174183974755974056,
                    18028730364581937563,
                    3040980448889133225,
                    580563103319692859,
                ]),
            ])),
            ell_vv: builder.constant_nonnative_ext2(QuadraticExtension::<Bn128Base>([
                Bn128Base([
                    7482695577452595874,
                    12720915354587739233,
                    15285336325258739141,
                    1001890062562077930,
                ]),
                Bn128Base([
                    5164457895468843746,
                    1673172257038644379,
                    1559362903759873829,
                    248219913139546960,
                ]),
            ])),
        };

        builder.connect_nonnative_ext2(&coeff_expected_0.ell_0, &g_precomputed.coeffs[0].ell_0);
        builder.connect_nonnative_ext2(&coeff_expected_0.ell_vw, &g_precomputed.coeffs[0].ell_vw);
        builder.connect_nonnative_ext2(&coeff_expected_0.ell_vv, &g_precomputed.coeffs[0].ell_vv);

        let coeff_expected_1 = EllCoefficientsTarget {
            ell_0: builder.constant_nonnative_ext2(QuadraticExtension::<Bn128Base>([
                Bn128Base([
                    13373442481846135230,
                    18162278520862515463,
                    3951913145905149164,
                    1705929995808613875,
                ]),
                Bn128Base([
                    3302322885510786647,
                    6108254548008280902,
                    11389629792418574312,
                    1497731481514317031,
                ]),
            ])),
            ell_vw: builder.constant_nonnative_ext2(QuadraticExtension::<Bn128Base>([
                Bn128Base([
                    13637779205322894244,
                    18313599956127061270,
                    13181708906852732943,
                    3223505406553364261,
                ]),
                Bn128Base([
                    8889208010557624044,
                    15934952838923155980,
                    2231106891030298788,
                    1720136300889719075,
                ]),
            ])),
            ell_vv: builder.constant_nonnative_ext2(QuadraticExtension::<Bn128Base>([
                Bn128Base([
                    5699172255660218441,
                    14224117930579859298,
                    9671055479960872346,
                    2897058453276464114,
                ]),
                Bn128Base([
                    1434851469978980926,
                    8787488385756412204,
                    8237694634490612487,
                    2312968450348013681,
                ]),
            ])),
        };
        builder.connect_nonnative_ext2(&coeff_expected_1.ell_0, &g_precomputed.coeffs[1].ell_0);
        builder.connect_nonnative_ext2(&coeff_expected_1.ell_vw, &g_precomputed.coeffs[1].ell_vw);
        builder.connect_nonnative_ext2(&coeff_expected_1.ell_vv, &g_precomputed.coeffs[1].ell_vv);

        let coeff_expected_101 = EllCoefficientsTarget {
            ell_0: builder.constant_nonnative_ext2(QuadraticExtension::<Bn128Base>([
                Bn128Base([
                    17085172404633693200,
                    10630938209732224048,
                    1371020573765003243,
                    1028232206131360563,
                ]),
                Bn128Base([
                    12232876582152898836,
                    767314283470872833,
                    15772841601744581597,
                    128106244370315677,
                ]),
            ])),
            ell_vw: builder.constant_nonnative_ext2(QuadraticExtension::<Bn128Base>([
                Bn128Base([
                    13268268652402041517,
                    413782302065018431,
                    10641674370522314647,
                    1317742553538815291,
                ]),
                Bn128Base([
                    7340261005993041334,
                    12959011140836651059,
                    6312169946649546817,
                    2020346702179008593,
                ]),
            ])),
            ell_vv: builder.constant_nonnative_ext2(QuadraticExtension::<Bn128Base>([
                Bn128Base([
                    17214549829497107128,
                    6367600020633491639,
                    4118147622849011930,
                    2701443844605818879,
                ]),
                Bn128Base([
                    9678615892898801219,
                    15105284796503706066,
                    15218042156631491887,
                    2386565019544464078,
                ]),
            ])),
        };
        builder.connect_nonnative_ext2(&coeff_expected_101.ell_0, &g_precomputed.coeffs[101].ell_0);
        builder.connect_nonnative_ext2(
            &coeff_expected_101.ell_vw,
            &g_precomputed.coeffs[101].ell_vw,
        );
        builder.connect_nonnative_ext2(
            &coeff_expected_101.ell_vv,
            &g_precomputed.coeffs[101].ell_vv,
        );

        assert_eq!(g_precomputed.coeffs.len(), 102);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof)
    }

    #[test]
    #[ignore]
    fn test_miller_loop() -> Result<()> {
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

        let g1 = AffinePointTarget::<G1> {
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
        let g2 = AffinePointTargetG2 {
            x: builder.constant_nonnative_ext2(QuadraticExtension::<Bn128Base>([
                Bn128Base([
                    11006543346086653583,
                    6918991450089238666,
                    18279842395430417956,
                    1732640417518178472,
                ]),
                Bn128Base([
                    11517548492582810861,
                    9169073428047311021,
                    9099478545610137041,
                    2335497441439112195,
                ]),
            ])),
            y: builder.constant_nonnative_ext2(QuadraticExtension::<Bn128Base>([
                Bn128Base([
                    8576222689638546622,
                    8183935398600054925,
                    8263144044154228149,
                    3015959802943919691,
                ]),
                Bn128Base([
                    13468896920756445043,
                    11126130999041690047,
                    2537329689975352328,
                    3196716715143124236,
                ]),
            ])),
        };

        let gt_expected = builder.constant_nonnative_ext12(DodecicExtension::<Bn128Base>([
            Bn128Base([
                11214948798496262313,
                17041960038845619795,
                15038543693968526953,
                2854769455943088582,
            ]),
            Bn128Base([
                18358947165889346901,
                7594645203897246376,
                8678460969103022172,
                1920999953682168236,
            ]),
            Bn128Base([
                3822366764294320012,
                17097402614902894928,
                9428044024961402650,
                243602561756596672,
            ]),
            Bn128Base([
                17183959784901604854,
                8949372598380251153,
                6758521511101568679,
                3292122140014866630,
            ]),
            Bn128Base([
                18184120903008236488,
                754777629877848609,
                11021228852074755205,
                1907956694624918089,
            ]),
            Bn128Base([
                1027874041688341259,
                11521396577902036682,
                3591493198463547173,
                83019242339262093,
            ]),
            Bn128Base([
                3122839170227481532,
                12173517765924753901,
                5944764658757645540,
                3140853624433931065,
            ]),
            Bn128Base([
                8180994361383621561,
                7383210295740433637,
                16513349742730085408,
                3103130917377758986,
            ]),
            Bn128Base([
                10794403896041222214,
                926595914487050175,
                14036399402507339094,
                1776103223747386957,
            ]),
            Bn128Base([
                5805166188446473199,
                2737269020341603902,
                13491591132308782822,
                2420261513329173431,
            ]),
            Bn128Base([
                1062543480691384776,
                13315554019138159385,
                3588730779329066043,
                106141411247146151,
            ]),
            Bn128Base([
                8227730547903353994,
                9584719179116428424,
                11268238026684181373,
                1782281581539027984,
            ]),
        ]));

        let g2_pre = builder.precompute::<G2, Bn128Base>(&g2);
        let gt = builder.miller_loop(&g1, &g2_pre);
        builder.connect_nonnative_ext12(&gt_expected, &gt);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof)
    }
}
