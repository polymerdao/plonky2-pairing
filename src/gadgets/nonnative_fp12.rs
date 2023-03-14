use crate::field::extension::dodecic::DodecicExtension;
use crate::field::extension::sextic::SexticExtension;
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
    use plonky2_field::types::Sample;

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
}
