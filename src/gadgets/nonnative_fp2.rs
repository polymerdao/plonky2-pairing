use crate::field::extension::quadratic::QuadraticExtension;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_ecdsa::gadgets::nonnative::{CircuitBuilderNonNative, NonNativeTarget};
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

    fn add_virtual_nonnative_ex2_target<FF: Field + Extendable<2>>(
        &mut self,
    ) -> NonNativeTargetExt2<FF>;

    fn add_nonnative_ext2<FF: PrimeField + Extendable<2>>(
        &mut self,
        a: &NonNativeTargetExt2<FF>,
        b: &NonNativeTargetExt2<FF>,
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

    fn add_virtual_nonnative_ex2_target<FF: Field + Extendable<2>>(
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
    use plonky2_field::types::Sample;

    #[test]
    fn test_nonnative_ext2_add() -> Result<()> {
        type FF = QuadraticExtension<Bn128Base>;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let x_ff = FF::rand();
        let y_ff = FF::rand();
        let sum_ff = x_ff + y_ff;

        let config = CircuitConfig::standard_ecc_config();
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
}
