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
    use plonky2_field::types::Sample;

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
}
