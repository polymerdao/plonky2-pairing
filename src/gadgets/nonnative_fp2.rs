use crate::field::extension::quadratic::QuadraticExtension;
use crate::gadgets::nonnative_fp::{CircuitBuilderNonNative, NonNativeTarget};
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::BoolTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_field::extension::Extendable;
use plonky2_field::types::{Field, PrimeField};
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct NonNativeTargetExt2<FF: Field> {
    pub(crate) c0: NonNativeTarget<FF>,
    pub(crate) c1: NonNativeTarget<FF>,
    pub(crate) _phantom: PhantomData<FF>,
}

pub trait CircuitBuilderNonNativeExt2<F: RichField + Extendable<D>, const D: usize> {
    fn zero_nonnative_ext2<FF: PrimeField + Extendable<2>>(&mut self) -> NonNativeTargetExt2<FF>;

    fn constant_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        x: QuadraticExtension<FF>,
    ) -> NonNativeTargetExt2<FF>;

    // Assert that two NonNativeTarget's, both assumed to be in reduced form, are equal.
    fn connect_nonnative_ext2<FF: Field + Extendable<2>>(
        &mut self,
        lhs: &NonNativeTargetExt2<FF>,
        rhs: &NonNativeTargetExt2<FF>,
    );

    fn add_virtual_nonnative_ext2_target<FF: Field + Extendable<2>>(
        &mut self,
    ) -> NonNativeTargetExt2<FF>;

    fn add_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt2<FF>,
        b: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt2<FF>;

    fn mul_nonnative_by_bool_ext2<FF: Field + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt2<FF>,
        b: BoolTarget,
    ) -> NonNativeTargetExt2<FF>;

    // Subtract two `NonNativeTarget`s.
    fn sub_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt2<FF>,
        b: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt2<FF>;

    fn mul_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt2<FF>,
        b: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt2<FF>;

    fn neg_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt2<FF>;

    fn inv_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt2<FF>;

    fn mul_by_nonresidue_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt2<FF>;

    fn nonnative_conditional_neg_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt2<FF>,
        b: BoolTarget,
    ) -> NonNativeTargetExt2<FF>;

    fn squared_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt2<FF>;

    fn scale_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt2<FF>,
        scalar: &NonNativeTarget<FF>,
    ) -> NonNativeTargetExt2<FF>;

    fn frobenius_map_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt2<FF>,
        power: usize,
    ) -> NonNativeTargetExt2<FF>;
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilderNonNativeExt2<F, D>
    for CircuitBuilder<F, D>
{
    fn zero_nonnative_ext2<FF: PrimeField + Extendable<2>>(&mut self) -> NonNativeTargetExt2<FF> {
        self.constant_nonnative_ext2(QuadraticExtension::ZERO)
    }

    fn constant_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        x: QuadraticExtension<FF>,
    ) -> NonNativeTargetExt2<FF> {
        NonNativeTargetExt2 {
            c0: self.constant_nonnative(x.0[0]),
            c1: self.constant_nonnative(x.0[1]),
            _phantom: PhantomData,
        }
    }

    fn connect_nonnative_ext2<FF: Field + Extendable<2>>(
        &mut self,
        lhs: &NonNativeTargetExt2<FF>,
        rhs: &NonNativeTargetExt2<FF>,
    ) {
        self.connect_nonnative(&rhs.c0, &lhs.c0);
        self.connect_nonnative(&rhs.c1, &lhs.c1);
    }

    fn add_virtual_nonnative_ext2_target<FF: Field + Extendable<2>>(
        &mut self,
    ) -> NonNativeTargetExt2<FF> {
        let c0 = self.add_virtual_nonnative_target();
        let c1 = self.add_virtual_nonnative_target();
        NonNativeTargetExt2 {
            c0,
            c1,
            _phantom: PhantomData,
        }
    }

    fn add_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt2<FF>,
        b: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt2<FF> {
        let c0 = self.add_nonnative(&a.c0, &b.c0);
        let c1 = self.add_nonnative(&a.c1, &b.c1);
        NonNativeTargetExt2 {
            c0,
            c1,
            _phantom: PhantomData,
        }
    }

    fn mul_nonnative_by_bool_ext2<FF: Field + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt2<FF>,
        b: BoolTarget,
    ) -> NonNativeTargetExt2<FF> {
        NonNativeTargetExt2 {
            c0: self.mul_nonnative_by_bool(&a.c0, b),
            c1: self.mul_nonnative_by_bool(&a.c1, b),
            _phantom: PhantomData,
        }
    }

    fn sub_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt2<FF>,
        b: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt2<FF> {
        let c0 = self.sub_nonnative(&a.c0, &b.c0);
        let c1 = self.sub_nonnative(&a.c1, &b.c1);
        NonNativeTargetExt2 {
            c0,
            c1,
            _phantom: PhantomData,
        }
    }

    fn mul_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt2<FF>,
        b: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt2<FF> {
        // Devegili OhEig Scott Dahab
        //     Multiplication and Squaring on Pairing-Friendly Fields.pdf
        //     Section 3 (Karatsuba)

        let aa = self.mul_nonnative(&a.c0, &b.c0);
        let bb = self.mul_nonnative(&a.c1, &b.c1);
        let aa_add_bb = self.add_nonnative(&aa, &bb);
        let bb_mul_nonresidue = self.mul_by_nonresidue_nonnative(&bb);
        let a0_add_a1 = self.add_nonnative(&a.c0, &a.c1);
        let b0_add_b1 = self.add_nonnative(&b.c0, &b.c1);
        let t = self.mul_nonnative(&a0_add_a1, &b0_add_b1);

        NonNativeTargetExt2 {
            c0: self.add_nonnative(&bb_mul_nonresidue, &aa),
            c1: self.sub_nonnative(&t, &aa_add_bb),
            _phantom: PhantomData,
        }
    }

    fn neg_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt2<FF> {
        NonNativeTargetExt2 {
            c0: self.neg_nonnative(&x.c0),
            c1: self.neg_nonnative(&x.c1),
            _phantom: PhantomData,
        }
    }

    fn inv_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt2<FF> {
        // "High-Speed Software Implementation of the Optimal Ate Pairing
        // over Barreto–Naehrig Curves"; Algorithm 8
        // TODO: deal with special case inv of zero
        // TODO: should use SimpleGenerator

        let c0_squared = self.mul_nonnative(&x.c0, &x.c0);
        let c1_squared = self.mul_nonnative(&x.c1, &x.c1);
        let c1_squared_mul_nonresidue = self.mul_by_nonresidue_nonnative(&c1_squared);
        let t = self.sub_nonnative(&c0_squared, &c1_squared_mul_nonresidue);
        let inv_t = self.inv_nonnative(&t);
        let c1_mul_inv_t = self.mul_nonnative(&x.c1, &inv_t);

        NonNativeTargetExt2 {
            c0: self.mul_nonnative(&x.c0, &inv_t),
            c1: self.neg_nonnative(&c1_mul_inv_t),
            _phantom: PhantomData,
        }
    }

    fn mul_by_nonresidue_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt2<FF> {
        let non_residue = self.constant_nonnative_ext2(QuadraticExtension(FF::EXT_NONRESIDUE));
        self.mul_nonnative_ext2(&x, &non_residue)
    }

    fn nonnative_conditional_neg_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt2<FF>,
        b: BoolTarget,
    ) -> NonNativeTargetExt2<FF> {
        let not_b = self.not(b);
        let neg = self.neg_nonnative_ext2(x);
        let x_if_true = self.mul_nonnative_by_bool_ext2(&neg, b);
        let x_if_false = self.mul_nonnative_by_bool_ext2(x, not_b);

        self.add_nonnative_ext2(&x_if_true, &x_if_false)
    }

    fn squared_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt2<FF>,
    ) -> NonNativeTargetExt2<FF> {
        // Devegili OhEig Scott Dahab
        //     Multiplication and Squaring on Pairing-Friendly Fields.pdf
        //     Section 3 (Complex squaring)

        let ab = self.mul_nonnative(&x.c0, &x.c1);
        let c1 = self.add_nonnative(&ab, &ab);
        let a_add_b = self.add_nonnative(&x.c0, &x.c1);
        let b_mul_nonresidue = self.mul_by_nonresidue_nonnative(&x.c1);
        let a_add_b_mul_nonresidue = self.add_nonnative(&x.c0, &b_mul_nonresidue);
        let a_add_b_mul_nonresidue_mul_a_add_b =
            self.mul_nonnative(&a_add_b, &a_add_b_mul_nonresidue);
        let ab_mul_nonresidue = self.mul_by_nonresidue_nonnative(&ab);
        let mut c0 = self.sub_nonnative(&a_add_b_mul_nonresidue_mul_a_add_b, &ab);
        c0 = self.sub_nonnative(&c0, &ab_mul_nonresidue);
        NonNativeTargetExt2 {
            c0,
            c1,
            _phantom: PhantomData,
        }
    }

    fn scale_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt2<FF>,
        scalar: &NonNativeTarget<FF>,
    ) -> NonNativeTargetExt2<FF> {
        NonNativeTargetExt2 {
            c0: self.mul_nonnative(&x.c0, scalar),
            c1: self.mul_nonnative(&x.c1, scalar),
            _phantom: PhantomData,
        }
    }

    fn frobenius_map_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        x: &NonNativeTargetExt2<FF>,
        power: usize,
    ) -> NonNativeTargetExt2<FF> {
        if power % 2 == 0 {
            x.clone()
        } else {
            NonNativeTargetExt2 {
                c0: x.c0.clone(),
                c1: self.mul_by_nonresidue_nonnative(&x.c1),
                _phantom: PhantomData,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::field::bn128_base::Bn128Base;
    use crate::field::extension::quadratic::QuadraticExtension;
    use crate::gadgets::nonnative_fp2::CircuitBuilderNonNativeExt2;
    use anyhow::Result;
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2_field::ops::Square;
    use plonky2_field::types::{Field, Sample};

    #[test]
    fn test_nonnative_ext2_add() -> Result<()> {
        type FF = QuadraticExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let x_ff = FF::rand();
        let y_ff = FF::rand();
        let sum_ff = x_ff + y_ff;

        let config = CircuitConfig::pairing_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext2(x_ff);
        let y = builder.constant_nonnative_ext2(y_ff);
        let sum = builder.add_nonnative_ext2(&x, &y);

        let sum_expected = builder.constant_nonnative_ext2(sum_ff);
        builder.connect_nonnative_ext2(&sum, &sum_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_ext2_sub() -> Result<()> {
        type FF = QuadraticExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let x_ff = FF::rand();
        let y_ff = FF::rand();
        let diff_ff = x_ff - y_ff;

        let config = CircuitConfig::pairing_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext2(x_ff);
        let y = builder.constant_nonnative_ext2(y_ff);
        let diff = builder.sub_nonnative_ext2(&x, &y);

        let diff_expected = builder.constant_nonnative_ext2(diff_ff);
        builder.connect_nonnative_ext2(&diff, &diff_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_ext2_mul() -> Result<()> {
        type FF = QuadraticExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand();
        let y_ff = FF::rand();

        let product_ff = x_ff * y_ff;

        let config = CircuitConfig::pairing_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext2(x_ff);
        let y = builder.constant_nonnative_ext2(y_ff);
        let product = builder.mul_nonnative_ext2(&x, &y);

        let product_expected = builder.constant_nonnative_ext2(product_ff);
        builder.connect_nonnative_ext2(&product, &product_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_ext2_neg() -> Result<()> {
        type FF = QuadraticExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand();
        let neg_x_ff = -x_ff;

        let config = CircuitConfig::pairing_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext2(x_ff);
        let neg_x = builder.neg_nonnative_ext2(&x);

        let neg_x_expected = builder.constant_nonnative_ext2(neg_x_ff);
        builder.connect_nonnative_ext2(&neg_x, &neg_x_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_ext2_inv() -> Result<()> {
        type FF = QuadraticExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand();
        let inv_x_ff = x_ff.inverse();

        let config = CircuitConfig::pairing_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext2(x_ff);
        let inv_x = builder.inv_nonnative_ext2(&x);

        let inv_x_expected = builder.constant_nonnative_ext2(inv_x_ff);
        builder.connect_nonnative_ext2(&inv_x, &inv_x_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_ext2_square() -> Result<()> {
        type FF = QuadraticExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand();
        let square_x_ff = x_ff.square();

        let config = CircuitConfig::pairing_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext2(x_ff);
        let square_x = builder.squared_nonnative_ext2(&x);

        let square_x_expected = builder.constant_nonnative_ext2(square_x_ff);
        builder.connect_nonnative_ext2(&square_x, &square_x_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }
}
