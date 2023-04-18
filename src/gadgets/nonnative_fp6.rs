use crate::field::extension::quadratic::QuadraticExtension;
use crate::field::extension::sextic::SexticExtension;
use crate::gadgets::nonnative_fp2::{CircuitBuilderNonNativeExt2, NonNativeTargetExt2};
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_field::extension::Extendable;
use plonky2_field::types::{Field, PrimeField};
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct NonNativeTargetExt6<FF: Field> {
    pub(crate) c0: NonNativeTargetExt2<FF>,
    pub(crate) c1: NonNativeTargetExt2<FF>,
    pub(crate) c2: NonNativeTargetExt2<FF>,
    pub(crate) _phantom: PhantomData<FF>,
}

pub trait CircuitBuilderNonNativeExt6<F: RichField + Extendable<D>, const D: usize> {
    fn zero_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
    ) -> NonNativeTargetExt6<FF>;

    fn constant_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        x: SexticExtension<FF>,
    ) -> NonNativeTargetExt6<FF>;

    // Assert that two NonNativeTarget's, both assumed to be in reduced form, are equal.
    fn connect_nonnative_ext6<FF: Field + Extendable<6> + Extendable<2>>(
        &mut self,
        lhs: &NonNativeTargetExt6<FF>,
        rhs: &NonNativeTargetExt6<FF>,
    );

    fn add_virtual_nonnative_ext6_target<FF: Field + Extendable<6> + Extendable<2>>(
        &mut self,
    ) -> NonNativeTargetExt6<FF>;

    fn add_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt6<FF>,
        b: &NonNativeTargetExt6<FF>,
    ) -> NonNativeTargetExt6<FF>;

    // Subtract two `NonNativeTarget`s.
    fn sub_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt6<FF>,
        b: &NonNativeTargetExt6<FF>,
    ) -> NonNativeTargetExt6<FF>;

    fn mul_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt6<FF>,
        b: &NonNativeTargetExt6<FF>,
    ) -> NonNativeTargetExt6<FF>;

    fn neg_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt6<FF>,
    ) -> NonNativeTargetExt6<FF>;

    fn inv_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt6<FF>,
    ) -> NonNativeTargetExt6<FF>;

    fn mul_by_nonresidue_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt6<FF>,
    ) -> NonNativeTargetExt6<FF>;

    fn squared_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt6<FF>,
    ) -> NonNativeTargetExt6<FF>;

    fn frobenius_map_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt6<FF>,
        power: usize,
    ) -> NonNativeTargetExt6<FF>;

    fn frobenius_coeffs_c1_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        n: usize,
    ) -> NonNativeTargetExt2<FF>;

    fn frobenius_coeffs_c2_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        n: usize,
    ) -> NonNativeTargetExt2<FF>;

    fn scale_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt6<FF>,
        by: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt6<FF>;
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilderNonNativeExt6<F, D>
    for CircuitBuilder<F, D>
{
    fn zero_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
    ) -> NonNativeTargetExt6<FF> {
        self.constant_nonnative_ext6(SexticExtension::ZERO)
    }

    fn constant_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        x: SexticExtension<FF>,
    ) -> NonNativeTargetExt6<FF> {
        NonNativeTargetExt6 {
            c0: self.constant_nonnative_ext2(QuadraticExtension {
                0: [x.0[0], x.0[1]],
            }),
            c1: self.constant_nonnative_ext2(QuadraticExtension {
                0: [x.0[2], x.0[3]],
            }),
            c2: self.constant_nonnative_ext2(QuadraticExtension {
                0: [x.0[4], x.0[5]],
            }),
            _phantom: PhantomData,
        }
    }

    fn connect_nonnative_ext6<FF: Field + Extendable<6> + Extendable<2>>(
        &mut self,
        lhs: &NonNativeTargetExt6<FF>,
        rhs: &NonNativeTargetExt6<FF>,
    ) {
        self.connect_nonnative_ext2(&rhs.c0, &lhs.c0);
        self.connect_nonnative_ext2(&rhs.c1, &lhs.c1);
        self.connect_nonnative_ext2(&rhs.c2, &lhs.c2);
    }

    fn add_virtual_nonnative_ext6_target<FF: Field + Extendable<6> + Extendable<2>>(
        &mut self,
    ) -> NonNativeTargetExt6<FF> {
        let c0 = self.add_virtual_nonnative_ext2_target();
        let c1 = self.add_virtual_nonnative_ext2_target();
        let c2 = self.add_virtual_nonnative_ext2_target();
        NonNativeTargetExt6 {
            c0,
            c1,
            c2,
            _phantom: PhantomData,
        }
    }

    fn add_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt6<FF>,
        b: &NonNativeTargetExt6<FF>,
    ) -> NonNativeTargetExt6<FF> {
        let c0 = self.add_nonnative_ext2(&a.c0, &b.c0);
        let c1 = self.add_nonnative_ext2(&a.c1, &b.c1);
        let c2 = self.add_nonnative_ext2(&a.c2, &b.c2);
        NonNativeTargetExt6 {
            c0,
            c1,
            c2,
            _phantom: PhantomData,
        }
    }

    fn sub_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt6<FF>,
        b: &NonNativeTargetExt6<FF>,
    ) -> NonNativeTargetExt6<FF> {
        let c0 = self.sub_nonnative_ext2(&a.c0, &b.c0);
        let c1 = self.sub_nonnative_ext2(&a.c1, &b.c1);
        let c2 = self.sub_nonnative_ext2(&a.c2, &b.c2);
        NonNativeTargetExt6 {
            c0,
            c1,
            c2,
            _phantom: PhantomData,
        }
    }

    fn mul_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt6<FF>,
        b: &NonNativeTargetExt6<FF>,
    ) -> NonNativeTargetExt6<FF> {
        let aa = self.mul_nonnative_ext2(&a.c0, &b.c0);
        let bb = self.mul_nonnative_ext2(&a.c1, &b.c1);
        let cc = self.mul_nonnative_ext2(&a.c2, &b.c2);

        let a1_add_a2 = self.add_nonnative_ext2(&a.c1, &a.c2);
        let a2_add_a0 = self.add_nonnative_ext2(&a.c2, &a.c0);
        let a0_add_a1 = self.add_nonnative_ext2(&a.c0, &a.c1);
        let b1_add_b2 = self.add_nonnative_ext2(&b.c1, &b.c2);
        let b2_add_b0 = self.add_nonnative_ext2(&b.c2, &b.c0);
        let b0_add_b1 = self.add_nonnative_ext2(&b.c0, &b.c1);

        let a1_add_a2_mul_b1_add_b2 = self.mul_nonnative_ext2(&a1_add_a2, &b1_add_b2);
        let a0_add_a1_mul_b0_add_b1 = self.mul_nonnative_ext2(&a0_add_a1, &b0_add_b1);
        let a2_add_a0_mul_b2_add_b0 = self.mul_nonnative_ext2(&a2_add_a0, &b2_add_b0);

        let mut c0 = self.sub_nonnative_ext2(&a1_add_a2_mul_b1_add_b2, &bb);
        c0 = self.sub_nonnative_ext2(&c0, &cc);
        c0 = self.mul_by_nonresidue_nonnative_ext2(&c0);
        c0 = self.add_nonnative_ext2(&c0, &aa);

        let cc_mul_nonresidue = self.mul_by_nonresidue_nonnative_ext2(&cc);
        let mut c1 = self.sub_nonnative_ext2(&a0_add_a1_mul_b0_add_b1, &aa);
        c1 = self.sub_nonnative_ext2(&c1, &bb);
        c1 = self.add_nonnative_ext2(&c1, &cc_mul_nonresidue);

        let mut c2 = self.sub_nonnative_ext2(&a2_add_a0_mul_b2_add_b0, &aa);
        c2 = self.add_nonnative_ext2(&c2, &bb);
        c2 = self.sub_nonnative_ext2(&c2, &cc);

        NonNativeTargetExt6 {
            c0,
            c1,
            c2,
            _phantom: PhantomData,
        }
    }

    fn neg_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt6<FF>,
    ) -> NonNativeTargetExt6<FF> {
        NonNativeTargetExt6 {
            c0: self.neg_nonnative_ext2(&x.c0),
            c1: self.neg_nonnative_ext2(&x.c1),
            c2: self.neg_nonnative_ext2(&x.c2),
            _phantom: PhantomData,
        }
    }

    fn inv_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt6<FF>,
    ) -> NonNativeTargetExt6<FF> {
        let mut c0 = self.squared_nonnative_ext2(&x.c0);
        let x2_mul_nonresidue = self.mul_by_nonresidue_nonnative_ext2(&x.c2);
        let x1_mul_x2_mul_nonresidue = self.mul_nonnative_ext2(&x.c1, &x2_mul_nonresidue);
        c0 = self.sub_nonnative_ext2(&c0, &x1_mul_x2_mul_nonresidue);

        let mut c1 = self.squared_nonnative_ext2(&x.c2);
        c1 = self.mul_by_nonresidue_nonnative_ext2(&c1);
        let x0_mul_x1 = self.mul_nonnative_ext2(&x.c0, &x.c1);
        c1 = self.sub_nonnative_ext2(&c1, &x0_mul_x1);

        let mut c2 = self.squared_nonnative_ext2(&x.c1);
        let x0_mul_x2 = self.mul_nonnative_ext2(&x.c0, &x.c2);
        c2 = self.sub_nonnative_ext2(&c2, &x0_mul_x2);

        let x2_mul_c1 = self.mul_nonnative_ext2(&x.c2, &c1);
        let x1_mul_c2 = self.mul_nonnative_ext2(&x.c1, &c2);
        let x0_mul_c0 = self.mul_nonnative_ext2(&x.c0, &c0);
        let mut t = self.add_nonnative_ext2(&x2_mul_c1, &x1_mul_c2);
        t = self.mul_by_nonresidue_nonnative_ext2(&t);
        t = self.add_nonnative_ext2(&t, &x0_mul_c0);
        t = self.inv_nonnative_ext2(&t);

        NonNativeTargetExt6 {
            c0: self.mul_nonnative_ext2(&t, &c0),
            c1: self.mul_nonnative_ext2(&t, &c1),
            c2: self.mul_nonnative_ext2(&t, &c2),
            _phantom: PhantomData,
        }
    }

    fn mul_by_nonresidue_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt6<FF>,
    ) -> NonNativeTargetExt6<FF> {
        NonNativeTargetExt6 {
            c0: self.mul_by_nonresidue_nonnative_ext2(&x.c2),
            c1: x.c0.clone(),
            c2: x.c1.clone(),
            _phantom: PhantomData,
        }
    }

    fn squared_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt6<FF>,
    ) -> NonNativeTargetExt6<FF> {
        let s0 = self.squared_nonnative_ext2(&x.c0);
        let ab = self.mul_nonnative_ext2(&x.c0, &x.c1);
        let s1 = self.add_nonnative_ext2(&ab, &ab);
        let mut s2 = self.sub_nonnative_ext2(&x.c0, &x.c1);
        s2 = self.add_nonnative_ext2(&s2, &x.c2);
        s2 = self.squared_nonnative_ext2(&s2);
        let bc = self.mul_nonnative_ext2(&x.c1, &x.c2);
        let s3 = self.add_nonnative_ext2(&bc, &bc);
        let s4 = self.squared_nonnative_ext2(&x.c2);
        let mut c0 = self.mul_by_nonresidue_nonnative_ext2(&s3);
        c0 = self.add_nonnative_ext2(&s0, &c0);
        let mut c1 = self.mul_by_nonresidue_nonnative_ext2(&s4);
        c1 = self.add_nonnative_ext2(&s1, &c1);
        let mut c2 = self.add_nonnative_ext2(&s1, &s2);
        c2 = self.add_nonnative_ext2(&c2, &s3);
        c2 = self.sub_nonnative_ext2(&c2, &s0);
        c2 = self.sub_nonnative_ext2(&c2, &s4);
        NonNativeTargetExt6 {
            c0,
            c1,
            c2,
            _phantom: PhantomData,
        }
    }

    fn frobenius_map_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt6<FF>,
        power: usize,
    ) -> NonNativeTargetExt6<FF> {
        let mut c1 = self.frobenius_map_nonnative_ext2(&x.c1, power);
        let mut c2 = self.frobenius_map_nonnative_ext2(&x.c2, power);
        let frobenius_c1 = self.frobenius_coeffs_c1_nonnative_ext6(power);
        let frobenius_c2 = self.frobenius_coeffs_c2_nonnative_ext6(power);
        c1 = self.mul_nonnative_ext2(&c1, &frobenius_c1);
        c2 = self.mul_nonnative_ext2(&c2, &frobenius_c2);

        NonNativeTargetExt6 {
            c0: self.frobenius_map_nonnative_ext2(&x.c0, power),
            c1,
            c2,
            _phantom: PhantomData,
        }
    }

    fn frobenius_coeffs_c1_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        n: usize,
    ) -> NonNativeTargetExt2<FF> {
        match n % 6 {
            0 => self.constant_nonnative_ext2(QuadraticExtension([FF::ONE, FF::ZERO])),
            1 => self.constant_nonnative_ext2(QuadraticExtension([
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT6_C1[0],
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT6_C1[1],
            ])),
            2 => self.constant_nonnative_ext2(QuadraticExtension([
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT6_C1[2],
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT6_C1[3],
            ])),
            3 => self.constant_nonnative_ext2(QuadraticExtension([
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT6_C1[4],
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT6_C1[5],
            ])),
            _ => unreachable!(),
        }
    }

    fn frobenius_coeffs_c2_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        n: usize,
    ) -> NonNativeTargetExt2<FF> {
        match n % 6 {
            0 => self.constant_nonnative_ext2(QuadraticExtension([FF::ONE, FF::ZERO])),
            1 => self.constant_nonnative_ext2(QuadraticExtension([
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT6_C2[0],
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT6_C2[1],
            ])),
            2 => self.constant_nonnative_ext2(QuadraticExtension([
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT6_C2[2],
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT6_C2[3],
            ])),
            3 => self.constant_nonnative_ext2(QuadraticExtension([
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT6_C2[4],
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT6_C2[5],
            ])),
            _ => unreachable!(),
        }
    }

    fn scale_nonnative_ext6<FF: PrimeField + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt6<FF>,
        by: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt6<FF> {
        NonNativeTargetExt6 {
            c0: self.mul_nonnative_ext2(&x.c0, by),
            c1: self.mul_nonnative_ext2(&x.c1, by),
            c2: self.mul_nonnative_ext2(&x.c2, by),
            _phantom: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::field::bn128_base::Bn128Base;
    use crate::field::extension::sextic::SexticExtension;
    use crate::gadgets::nonnative_fp6::CircuitBuilderNonNativeExt6;
    use anyhow::Result;
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2_field::ops::Square;
    use plonky2_field::types::{Field, Sample};

    #[test]
    fn test_nonnative_ext6_add() -> Result<()> {
        type FF = SexticExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let x_ff = FF::rand();
        let y_ff = FF::rand();
        let sum_ff = x_ff + y_ff;

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext6(x_ff);
        let y = builder.constant_nonnative_ext6(y_ff);
        let sum = builder.add_nonnative_ext6(&x, &y);

        let sum_expected = builder.constant_nonnative_ext6(sum_ff);
        builder.connect_nonnative_ext6(&sum, &sum_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_ext6_sub() -> Result<()> {
        type FF = SexticExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let x_ff = FF::rand();
        let y_ff = FF::rand();
        let diff_ff = x_ff - y_ff;

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext6(x_ff);
        let y = builder.constant_nonnative_ext6(y_ff);
        let diff = builder.sub_nonnative_ext6(&x, &y);

        let diff_expected = builder.constant_nonnative_ext6(diff_ff);
        builder.connect_nonnative_ext6(&diff, &diff_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_ext6_mul() -> Result<()> {
        type FF = SexticExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand();
        let y_ff = FF::rand();

        let product_ff = x_ff * y_ff;

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext6(x_ff);
        let y = builder.constant_nonnative_ext6(y_ff);
        let product = builder.mul_nonnative_ext6(&x, &y);

        let product_expected = builder.constant_nonnative_ext6(product_ff);
        builder.connect_nonnative_ext6(&product, &product_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_ext6_neg() -> Result<()> {
        type FF = SexticExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand();
        let neg_x_ff = -x_ff;

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext6(x_ff);
        let neg_x = builder.neg_nonnative_ext6(&x);

        let neg_x_expected = builder.constant_nonnative_ext6(neg_x_ff);
        builder.connect_nonnative_ext6(&neg_x, &neg_x_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_ext6_inv() -> Result<()> {
        type FF = SexticExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand();
        let inv_x_ff = x_ff.inverse();

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext6(x_ff);
        let inv_x = builder.inv_nonnative_ext6(&x);

        let inv_x_expected = builder.constant_nonnative_ext6(inv_x_ff);
        builder.connect_nonnative_ext6(&inv_x, &inv_x_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_ext6_square() -> Result<()> {
        type FF = SexticExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand();
        let square_x_ff = x_ff.square();

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext6(x_ff);
        let square_x = builder.squared_nonnative_ext6(&x);

        let square_x_expected = builder.constant_nonnative_ext6(square_x_ff);
        builder.connect_nonnative_ext6(&square_x, &square_x_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }
}
