use crate::field::extension::dodecic::DodecicExtension;
use crate::field::extension::sextic::SexticExtension;
use crate::gadgets::nonnative_fp2::{CircuitBuilderNonNativeExt2, NonNativeTargetExt2};
use crate::gadgets::nonnative_fp6::{CircuitBuilderNonNativeExt6, NonNativeTargetExt6};
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_field::extension::Extendable;
use plonky2_field::types::{Field, PrimeField};
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct NonNativeTargetExt12<FF: Field> {
    pub(crate) c0: NonNativeTargetExt6<FF>,
    pub(crate) c1: NonNativeTargetExt6<FF>,
    pub(crate) _phantom: PhantomData<FF>,
}

pub trait CircuitBuilderNonNativeExt12<F: RichField + Extendable<D>, const D: usize> {
    fn zero_nonnative_ext12<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
    ) -> NonNativeTargetExt12<FF>;

    fn constant_nonnative_ext12<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        x: DodecicExtension<FF>,
    ) -> NonNativeTargetExt12<FF>;

    // Assert that two NonNativeTarget's, both assumed to be in reduced form, are equal.
    fn connect_nonnative_ext12<FF: Field + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        lhs: &NonNativeTargetExt12<FF>,
        rhs: &NonNativeTargetExt12<FF>,
    );

    fn add_virtual_nonnative_ex2_target<
        FF: Field + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
    ) -> NonNativeTargetExt12<FF>;

    fn add_nonnative_ext12<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt12<FF>,
        b: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF>;

    // Subtract two `NonNativeTarget`s.
    fn sub_nonnative_ext12<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt12<FF>,
        b: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF>;

    fn mul_nonnative_ext12<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt12<FF>,
        b: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF>;

    fn neg_nonnative_ext12<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF>;

    fn inv_nonnative_ext12<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF>;

    fn squared_nonnative_ext12<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF>;

    fn mul_by_024<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
        ell_0: &NonNativeTargetExt2<FF>,
        ell_vw: &NonNativeTargetExt2<FF>,
        ell_vv: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt12<FF>;
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilderNonNativeExt12<F, D>
    for CircuitBuilder<F, D>
{
    fn zero_nonnative_ext12<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
    ) -> NonNativeTargetExt12<FF> {
        self.constant_nonnative_ext12(DodecicExtension::ZERO)
    }

    fn constant_nonnative_ext12<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        x: DodecicExtension<FF>,
    ) -> NonNativeTargetExt12<FF> {
        NonNativeTargetExt12 {
            c0: self.constant_nonnative_ext6(SexticExtension {
                0: [x.0[0], x.0[1], x.0[2], x.0[3], x.0[4], x.0[5]],
            }),
            c1: self.constant_nonnative_ext6(SexticExtension {
                0: [x.0[6], x.0[7], x.0[8], x.0[9], x.0[10], x.0[11]],
            }),
            _phantom: PhantomData,
        }
    }

    fn connect_nonnative_ext12<FF: Field + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        lhs: &NonNativeTargetExt12<FF>,
        rhs: &NonNativeTargetExt12<FF>,
    ) {
        self.connect_nonnative_ext6(&rhs.c0, &lhs.c0);
        self.connect_nonnative_ext6(&rhs.c1, &lhs.c1);
    }

    fn add_virtual_nonnative_ex2_target<
        FF: Field + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
    ) -> NonNativeTargetExt12<FF> {
        let c0 = self.add_virtual_nonnative_ext6_target();
        let c1 = self.add_virtual_nonnative_ext6_target();
        NonNativeTargetExt12 {
            c0,
            c1,
            _phantom: PhantomData,
        }
    }

    fn add_nonnative_ext12<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt12<FF>,
        b: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF> {
        let c0 = self.add_nonnative_ext6(&a.c0, &b.c0);
        let c1 = self.add_nonnative_ext6(&a.c1, &b.c1);
        NonNativeTargetExt12 {
            c0,
            c1,
            _phantom: PhantomData,
        }
    }

    fn sub_nonnative_ext12<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt12<FF>,
        b: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF> {
        let c0 = self.sub_nonnative_ext6(&a.c0, &b.c0);
        let c1 = self.sub_nonnative_ext6(&a.c1, &b.c1);
        NonNativeTargetExt12 {
            c0,
            c1,
            _phantom: PhantomData,
        }
    }

    fn mul_nonnative_ext12<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt12<FF>,
        b: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF> {
        let aa = self.mul_nonnative_ext6(&a.c0, &b.c0);
        let bb = self.mul_nonnative_ext6(&a.c1, &b.c1);
        let aa_add_bb = self.add_nonnative_ext6(&aa, &bb);
        let bb_mul_nonresidue = self.mul_by_nonresidue_nonnative_ext6(&bb);
        let a0_add_a1 = self.add_nonnative_ext6(&a.c0, &a.c1);
        let b0_add_b1 = self.add_nonnative_ext6(&b.c0, &b.c1);
        let t = self.mul_nonnative_ext6(&a0_add_a1, &b0_add_b1);

        NonNativeTargetExt12 {
            c0: self.add_nonnative_ext6(&bb_mul_nonresidue, &aa),
            c1: self.sub_nonnative_ext6(&t, &aa_add_bb),
            _phantom: PhantomData,
        }
    }

    fn neg_nonnative_ext12<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF> {
        NonNativeTargetExt12 {
            c0: self.neg_nonnative_ext6(&x.c0),
            c1: self.neg_nonnative_ext6(&x.c1),
            _phantom: PhantomData,
        }
    }

    fn inv_nonnative_ext12<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF> {
        let c0_squared = self.squared_nonnative_ext6(&x.c0);
        let c1_squared = self.squared_nonnative_ext6(&x.c1);
        let c1_squared_mul_nonresidue = self.mul_by_nonresidue_nonnative_ext6(&c1_squared);
        let t = self.sub_nonnative_ext6(&c0_squared, &c1_squared_mul_nonresidue);
        let inv_t = self.inv_nonnative_ext6(&t);
        let c1_mul_inv_t = self.mul_nonnative_ext6(&x.c1, &inv_t);

        NonNativeTargetExt12 {
            c0: self.mul_nonnative_ext6(&x.c0, &inv_t),
            c1: self.neg_nonnative_ext6(&c1_mul_inv_t),
            _phantom: PhantomData,
        }
    }

    fn squared_nonnative_ext12<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF> {
        let ab = self.mul_nonnative_ext6(&x.c0, &x.c1);
        let c1 = self.add_nonnative_ext6(&ab, &ab);
        let a_add_b = self.add_nonnative_ext6(&x.c0, &x.c1);
        let b_mul_nonresidue = self.mul_by_nonresidue_nonnative_ext6(&x.c1);
        let a_add_b_mul_nonresidue = self.add_nonnative_ext6(&x.c0, &b_mul_nonresidue);
        let a_add_b_mul_nonresidue_mul_a_add_b =
            self.mul_nonnative_ext6(&a_add_b, &a_add_b_mul_nonresidue);
        let ab_mul_nonresidue = self.mul_by_nonresidue_nonnative_ext6(&ab);
        let mut c0 = self.sub_nonnative_ext6(&a_add_b_mul_nonresidue_mul_a_add_b, &ab);
        c0 = self.sub_nonnative_ext6(&c0, &ab_mul_nonresidue);
        NonNativeTargetExt12 {
            c0,
            c1,
            _phantom: PhantomData,
        }
    }

    fn mul_by_024<FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
        ell_0: &NonNativeTargetExt2<FF>,
        ell_vw: &NonNativeTargetExt2<FF>,
        ell_vv: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt12<FF> {
        let z0 = x.c0.c0.clone();
        let z1 = x.c0.c1.clone();
        let z2 = x.c0.c2.clone();
        let z3 = x.c1.c0.clone();
        let z4 = x.c1.c1.clone();
        let z5 = x.c1.c2.clone();

        let x0 = ell_0.clone();
        let x2 = ell_vv.clone();
        let x4 = ell_vw.clone();

        let d0 = self.mul_nonnative_ext2(&z0, &x0);
        let d2 = self.mul_nonnative_ext2(&z2, &x2);
        let d4 = self.mul_nonnative_ext2(&z4, &x4);
        let t2 = self.add_nonnative_ext2(&z0, &z4);
        let t1 = self.add_nonnative_ext2(&z0, &z2);
        let mut s0 = self.add_nonnative_ext2(&z1, &z3);
        s0 = self.add_nonnative_ext2(&s0, &z5);

        let s1 = self.mul_nonnative_ext2(&z1, &x2);
        let t3 = self.add_nonnative_ext2(&s1, &d4);
        let mut t4 = self.mul_by_nonresidue_nonnative_ext2(&t3);
        t4 = self.add_nonnative_ext2(&t4, &d0);
        let z0 = t4;

        let t3 = self.mul_nonnative_ext2(&z5, &x4);
        let s1 = self.add_nonnative_ext2(&s1, &t3);
        let t3 = self.add_nonnative_ext2(&t3, &d2);
        let t4 = self.mul_by_nonresidue_nonnative_ext2(&t3);
        let t3 = self.mul_nonnative_ext2(&z1, &x0);
        let s1 = self.add_nonnative_ext2(&s1, &t3);
        let t4 = self.add_nonnative_ext2(&t4, &t3);
        let z1 = t4;

        let t0 = self.add_nonnative_ext2(&x0, &x2);
        let mut t3 = self.mul_nonnative_ext2(&t1, &t0);
        t3 = self.sub_nonnative_ext2(&t3, &d0);
        t3 = self.sub_nonnative_ext2(&t3, &d2);
        let t4 = self.mul_nonnative_ext2(&z3, &x4);
        let s1 = self.add_nonnative_ext2(&s1, &t4);
        let t3 = self.add_nonnative_ext2(&t3, &t4);

        let t0 = self.add_nonnative_ext2(&z2, &z4);
        let z2 = t3;

        let t1 = self.add_nonnative_ext2(&x2, &x4);
        let mut t3 = self.mul_nonnative_ext2(&t0, &t1);
        t3 = self.sub_nonnative_ext2(&t3, &d2);
        t3 = self.sub_nonnative_ext2(&t3, &d4);
        let t4 = self.mul_by_nonresidue_nonnative_ext2(&t3);
        let t3 = self.mul_nonnative_ext2(&z3, &x0);
        let mut s1 = self.add_nonnative_ext2(&s1, &t3);
        let t4 = self.add_nonnative_ext2(&t4, &t3);
        let z3 = t4;

        let t3 = self.mul_nonnative_ext2(&z5, &x2);
        let s1 = self.add_nonnative_ext2(&s1, &t3);
        let t4 = self.mul_by_nonresidue_nonnative_ext2(&t3);
        let t0 = self.add_nonnative_ext2(&x0, &x4);
        let mut t3 = self.mul_nonnative_ext2(&t2, &t0);
        t3 = self.sub_nonnative_ext2(&t3, &d0);
        t3 = self.sub_nonnative_ext2(&t3, &d4);
        let t4 = self.add_nonnative_ext2(&t4, &t3);
        let z4 = t4;

        let mut t0 = self.add_nonnative_ext2(&x0, &x2);
        t0 = self.add_nonnative_ext2(&t0, &x4);
        let mut t3 = self.mul_nonnative_ext2(&s0, &t0);
        t3 = self.sub_nonnative_ext2(&t3, &s1);
        let z5 = t3;

        NonNativeTargetExt12 {
            c0: NonNativeTargetExt6 {
                c0: z0,
                c1: z1,
                c2: z2,
                _phantom: PhantomData,
            },
            c1: NonNativeTargetExt6 {
                c0: z3,
                c1: z4,
                c2: z5,
                _phantom: PhantomData,
            },
            _phantom: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::field::bn128_base::Bn128Base;
    use crate::field::extension::dodecic::DodecicExtension;
    use crate::gadgets::nonnative_fp12::CircuitBuilderNonNativeExt12;
    use anyhow::Result;
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2_field::ops::Square;
    use plonky2_field::types::{Field, Sample};

    #[test]
    fn test_nonnative_ext12_add() -> Result<()> {
        type FF = DodecicExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let x_ff = FF::rand();
        let y_ff = FF::rand();
        let sum_ff = x_ff + y_ff;

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext12(x_ff);
        let y = builder.constant_nonnative_ext12(y_ff);
        let sum = builder.add_nonnative_ext12(&x, &y);

        let sum_expected = builder.constant_nonnative_ext12(sum_ff);
        builder.connect_nonnative_ext12(&sum, &sum_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_ext12_sub() -> Result<()> {
        type FF = DodecicExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let x_ff = FF::rand();
        let y_ff = FF::rand();
        let diff_ff = x_ff - y_ff;

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext12(x_ff);
        let y = builder.constant_nonnative_ext12(y_ff);
        let diff = builder.sub_nonnative_ext12(&x, &y);

        let diff_expected = builder.constant_nonnative_ext12(diff_ff);
        builder.connect_nonnative_ext12(&diff, &diff_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_ext12_mul() -> Result<()> {
        type FF = DodecicExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand();
        let y_ff = FF::rand();

        let product_ff = x_ff * y_ff;

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext12(x_ff);
        let y = builder.constant_nonnative_ext12(y_ff);
        let product = builder.mul_nonnative_ext12(&x, &y);

        let product_expected = builder.constant_nonnative_ext12(product_ff);
        builder.connect_nonnative_ext12(&product, &product_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_ext12_neg() -> Result<()> {
        type FF = DodecicExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand();
        let neg_x_ff = -x_ff;

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext12(x_ff);
        let neg_x = builder.neg_nonnative_ext12(&x);

        let neg_x_expected = builder.constant_nonnative_ext12(neg_x_ff);
        builder.connect_nonnative_ext12(&neg_x, &neg_x_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_ext12_inv() -> Result<()> {
        type FF = DodecicExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand();
        let inv_x_ff = x_ff.inverse();

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext12(x_ff);
        let inv_x = builder.inv_nonnative_ext12(&x);

        let inv_x_expected = builder.constant_nonnative_ext12(inv_x_ff);
        builder.connect_nonnative_ext12(&inv_x, &inv_x_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_ext12_square() -> Result<()> {
        type FF = DodecicExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand();
        let square_x_ff = x_ff.square();

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext12(x_ff);
        let square_x = builder.squared_nonnative_ext12(&x);

        let square_x_expected = builder.constant_nonnative_ext12(square_x_ff);
        builder.connect_nonnative_ext12(&square_x, &square_x_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }
}
