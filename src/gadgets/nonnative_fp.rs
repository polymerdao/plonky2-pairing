use core::marker::PhantomData;

use crate::gadgets::biguint::{
    BigUintTarget, CircuitBuilderBiguint, GeneratedValuesBigUint, WitnessBigUint,
};
use crate::gadgets::gates::nonnative_add::NonnativeAddGate;
use crate::gadgets::gates::nonnative_mul::NonnativeMulGate;
use crate::gadgets::gates::u28_to_u32::U28ToU32Gate;
use crate::gadgets::gates::u32_to_u28::U32ToU28Gate;
use num::{BigUint, Integer, Zero};
use plonky2::field::extension::Extendable;
use plonky2::field::types::{Field, PrimeField};
use plonky2::hash::hash_types::RichField;
use plonky2::iop::generator::{GeneratedValues, SimpleGenerator};
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartitionWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::util::ceil_div_usize;
use plonky2_u32::gadgets::arithmetic_u32::{CircuitBuilderU32, U32Target};
use plonky2_u32::gadgets::range_check::range_check_u32_circuit;
use plonky2_u32::witness::GeneratedValuesU32;

// TODO:refactor
// 0xed84884a014afa37,
// 0xeb2022850278edf8,
// 0xcf63e9cfb74492d9,
// 0x2e67157159e5c639,
const BN128_BASE_INV: [u32; 10] = [
    0x14afa37, 0x84884a0, 0x8edf8ed, 0x2285027, 0x2d9eb20, 0xcfb7449, 0x9cf63e9, 0x59e5c63,
    0xe671571, 0x2,
];

#[derive(Clone, Debug)]
pub struct NonNativeTarget<FF: Field> {
    pub value: BigUintTarget,
    pub _phantom: PhantomData<FF>,
}

pub trait CircuitBuilderNonNative<F: RichField + Extendable<D>, const D: usize> {
    fn num_nonnative_limbs<FF: Field>() -> usize {
        ceil_div_usize(FF::BITS, 32)
    }

    fn biguint_to_nonnative<FF: Field>(&mut self, x: &BigUintTarget) -> NonNativeTarget<FF>;

    fn nonnative_to_canonical_biguint<FF: Field>(
        &mut self,
        x: &NonNativeTarget<FF>,
    ) -> BigUintTarget;

    fn constant_nonnative<FF: PrimeField>(&mut self, x: FF) -> NonNativeTarget<FF>;

    fn zero_nonnative<FF: PrimeField>(&mut self) -> NonNativeTarget<FF>;

    // Assert that two NonNativeTarget's, both assumed to be in reduced form, are equal.
    fn connect_nonnative<FF: Field>(
        &mut self,
        lhs: &NonNativeTarget<FF>,
        rhs: &NonNativeTarget<FF>,
    );

    fn add_virtual_nonnative_target<FF: Field>(&mut self) -> NonNativeTarget<FF>;

    fn add_virtual_nonnative_target_sized<FF: Field>(
        &mut self,
        num_limbs: usize,
    ) -> NonNativeTarget<FF>;

    fn add_nonnative<FF: PrimeField>(
        &mut self,
        a: &NonNativeTarget<FF>,
        b: &NonNativeTarget<FF>,
    ) -> NonNativeTarget<FF>;

    fn mul_nonnative_by_bool<FF: Field>(
        &mut self,
        a: &NonNativeTarget<FF>,
        b: BoolTarget,
    ) -> NonNativeTarget<FF>;

    fn if_nonnative<FF: PrimeField>(
        &mut self,
        b: BoolTarget,
        x: &NonNativeTarget<FF>,
        y: &NonNativeTarget<FF>,
    ) -> NonNativeTarget<FF>;

    // Subtract two `NonNativeTarget`s.
    fn sub_nonnative<FF: PrimeField>(
        &mut self,
        a: &NonNativeTarget<FF>,
        b: &NonNativeTarget<FF>,
    ) -> NonNativeTarget<FF>;

    fn mul_nonnative<FF: PrimeField>(
        &mut self,
        a: &NonNativeTarget<FF>,
        b: &NonNativeTarget<FF>,
    ) -> NonNativeTarget<FF>;

    fn neg_nonnative<FF: PrimeField>(&mut self, x: &NonNativeTarget<FF>) -> NonNativeTarget<FF>;

    fn inv_nonnative<FF: PrimeField>(&mut self, x: &NonNativeTarget<FF>) -> NonNativeTarget<FF>;

    fn mul_by_nonresidue_nonnative<FF: PrimeField>(
        &mut self,
        x: &NonNativeTarget<FF>,
    ) -> NonNativeTarget<FF>;

    /// Returns `x % |FF|` as a `NonNativeTarget`.
    fn reduce<FF: Field>(&mut self, x: &BigUintTarget) -> NonNativeTarget<FF>;

    fn reduce_nonnative<FF: Field>(&mut self, x: &NonNativeTarget<FF>) -> NonNativeTarget<FF>;

    fn bool_to_nonnative<FF: Field>(&mut self, b: &BoolTarget) -> NonNativeTarget<FF>;

    // Split a nonnative field element to bits.
    fn split_nonnative_to_bits<FF: Field>(&mut self, x: &NonNativeTarget<FF>) -> Vec<BoolTarget>;

    fn nonnative_conditional_neg<FF: PrimeField>(
        &mut self,
        x: &NonNativeTarget<FF>,
        b: BoolTarget,
    ) -> NonNativeTarget<FF>;
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilderNonNative<F, D>
    for CircuitBuilder<F, D>
{
    fn num_nonnative_limbs<FF: Field>() -> usize {
        ceil_div_usize(FF::BITS, 32)
    }

    fn biguint_to_nonnative<FF: Field>(&mut self, x: &BigUintTarget) -> NonNativeTarget<FF> {
        NonNativeTarget {
            value: x.clone(),
            _phantom: PhantomData,
        }
    }

    fn nonnative_to_canonical_biguint<FF: Field>(
        &mut self,
        x: &NonNativeTarget<FF>,
    ) -> BigUintTarget {
        x.value.clone()
    }

    fn constant_nonnative<FF: PrimeField>(&mut self, x: FF) -> NonNativeTarget<FF> {
        let mut x_biguint = self.constant_biguint(&x.to_canonical_biguint());
        let num_limbs = FF::BITS / 32;
        for _ in 0..(num_limbs - x_biguint.num_limbs()) {
            x_biguint.limbs.push(self.constant_u32(0));
        }
        self.biguint_to_nonnative(&x_biguint)
    }

    fn zero_nonnative<FF: PrimeField>(&mut self) -> NonNativeTarget<FF> {
        self.constant_nonnative(FF::ZERO)
    }

    // Assert that two NonNativeTarget's, both assumed to be in reduced form, are equal.
    fn connect_nonnative<FF: Field>(
        &mut self,
        lhs: &NonNativeTarget<FF>,
        rhs: &NonNativeTarget<FF>,
    ) {
        self.connect_biguint(&lhs.value, &rhs.value);
    }

    fn add_virtual_nonnative_target<FF: Field>(&mut self) -> NonNativeTarget<FF> {
        let num_limbs = Self::num_nonnative_limbs::<FF>();
        let value = self.add_virtual_biguint_target(num_limbs);

        NonNativeTarget {
            value,
            _phantom: PhantomData,
        }
    }

    fn add_virtual_nonnative_target_sized<FF: Field>(
        &mut self,
        num_limbs: usize,
    ) -> NonNativeTarget<FF> {
        let value = self.add_virtual_biguint_target(num_limbs);

        NonNativeTarget {
            value,
            _phantom: PhantomData,
        }
    }

    fn add_nonnative<FF: PrimeField>(
        &mut self,
        a: &NonNativeTarget<FF>,
        b: &NonNativeTarget<FF>,
    ) -> NonNativeTarget<FF> {
        let gate = NonnativeAddGate::<F, D>::new_from_config(&self.config);
        let (row, copy) = self.find_slot(gate, &[], &[]);

        let mut targets = Vec::new();
        for i in 0..8 {
            self.connect(
                Target::wire(row, gate.wire_ith_input_x(copy, i)),
                a.value.limbs[i].0,
            );
            self.connect(
                Target::wire(row, gate.wire_ith_input_y(copy, i)),
                b.value.limbs[i].0,
            );
            targets.push(U32Target {
                0: Target::wire(row, gate.wire_ith_output_result(copy, i)),
            });
        }

        NonNativeTarget {
            value: BigUintTarget { limbs: targets },
            _phantom: PhantomData,
        }
    }

    fn mul_nonnative_by_bool<FF: Field>(
        &mut self,
        a: &NonNativeTarget<FF>,
        b: BoolTarget,
    ) -> NonNativeTarget<FF> {
        NonNativeTarget {
            value: self.mul_biguint_by_bool(&a.value, b),
            _phantom: PhantomData,
        }
    }

    fn if_nonnative<FF: PrimeField>(
        &mut self,
        b: BoolTarget,
        x: &NonNativeTarget<FF>,
        y: &NonNativeTarget<FF>,
    ) -> NonNativeTarget<FF> {
        let not_b = self.not(b);
        let maybe_x = self.mul_nonnative_by_bool(x, b);
        let maybe_y = self.mul_nonnative_by_bool(y, not_b);
        self.add_nonnative(&maybe_x, &maybe_y)
    }

    // Subtract two `NonNativeTarget`s.
    fn sub_nonnative<FF: PrimeField>(
        &mut self,
        a: &NonNativeTarget<FF>,
        b: &NonNativeTarget<FF>,
    ) -> NonNativeTarget<FF> {
        let diff = self.add_virtual_nonnative_target::<FF>();
        let overflow = self.add_virtual_bool_target_unsafe();

        self.add_simple_generator(NonNativeSubtractionGenerator::<F, D, FF> {
            a: a.clone(),
            b: b.clone(),
            diff: diff.clone(),
            overflow,
            _phantom: PhantomData,
        });

        range_check_u32_circuit(self, diff.value.limbs.clone());
        self.assert_bool(overflow);

        let diff_plus_b = self.add_biguint(&diff.value, &b.value);
        let modulus = self.constant_biguint(&FF::order());
        let mod_times_overflow = self.mul_biguint_by_bool(&modulus, overflow);
        let diff_plus_b_reduced = self.sub_biguint(&diff_plus_b, &mod_times_overflow);
        self.connect_biguint(&a.value, &diff_plus_b_reduced);

        diff
    }

    fn mul_nonnative<FF: PrimeField>(
        &mut self,
        a: &NonNativeTarget<FF>,
        b: &NonNativeTarget<FF>,
    ) -> NonNativeTarget<FF> {
        let gate = U32ToU28Gate::<F, D>::new_from_config(&self.config);
        let (row, copy) = self.find_slot(gate, &[], &[]);
        for i in 0..8 {
            self.connect(
                Target::wire(row, gate.wire_ith_input(copy, i)),
                a.value.limbs[i].0,
            );
        }
        let mut a_targets = Vec::new();
        for i in 0..10 {
            a_targets.push(Target::wire(row, gate.wire_ith_output_result(copy, i)));
        }
        let gate = U32ToU28Gate::<F, D>::new_from_config(&self.config);
        let (row, copy) = self.find_slot(gate, &[], &[]);
        for i in 0..8 {
            self.connect(
                Target::wire(row, gate.wire_ith_input(copy, i)),
                b.value.limbs[i].0,
            );
        }
        let mut b_targets = Vec::new();
        for i in 0..10 {
            b_targets.push(Target::wire(row, gate.wire_ith_output_result(copy, i)));
        }

        let mut xy = Vec::new();
        let gate = NonnativeMulGate::<F, D>::new_from_config(&self.config);
        let (row, copy) = self.find_slot(gate, &[], &[]);
        for i in 0..10 {
            self.connect(
                Target::wire(row, gate.wire_ith_input_x(copy, i)),
                a_targets[i],
            );
            self.connect(
                Target::wire(row, gate.wire_ith_input_y(copy, i)),
                b_targets[i],
            );
            xy.push(Target::wire(row, gate.wire_ith_output_result(copy, i)));
        }

        let mut res = Vec::new();
        let gate = NonnativeMulGate::<F, D>::new_from_config(&self.config);
        let (row, copy) = self.find_slot(gate, &[], &[]);
        for i in 0..10 {
            self.connect(Target::wire(row, gate.wire_ith_input_x(copy, i)), xy[i]);
            let inv = self.constant(F::from_canonical_u32(BN128_BASE_INV[i]));
            self.connect(Target::wire(row, gate.wire_ith_input_y(copy, i)), inv);
            res.push(Target::wire(row, gate.wire_ith_output_result(copy, i)));
        }

        let gate = U28ToU32Gate::<F, D>::new_from_config(&self.config);
        let (row, copy) = self.find_slot(gate, &[], &[]);
        for i in 0..10 {
            self.connect(Target::wire(row, gate.wire_ith_input(copy, i)), res[i]);
        }
        let mut targets = Vec::new();
        for i in 0..8 {
            targets.push(U32Target {
                0: Target::wire(row, gate.wire_ith_output_result(copy, i)),
            });
        }

        NonNativeTarget {
            value: BigUintTarget { limbs: targets },
            _phantom: PhantomData,
        }
    }

    fn neg_nonnative<FF: PrimeField>(&mut self, x: &NonNativeTarget<FF>) -> NonNativeTarget<FF> {
        let zero_target = self.constant_biguint(&BigUint::zero());
        let zero_ff = self.biguint_to_nonnative(&zero_target);

        self.sub_nonnative(&zero_ff, x)
    }

    fn inv_nonnative<FF: PrimeField>(&mut self, x: &NonNativeTarget<FF>) -> NonNativeTarget<FF> {
        let num_limbs = x.value.num_limbs();
        let inv_biguint = self.add_virtual_biguint_target(num_limbs);
        let one = self.constant_nonnative(FF::ONE);

        self.add_simple_generator(NonNativeInverseGenerator::<F, D, FF> {
            x: x.clone(),
            inv: inv_biguint.clone(),
            _phantom: PhantomData,
        });

        let product = self.mul_nonnative(
            &x,
            &NonNativeTarget {
                value: inv_biguint.clone(),
                _phantom: PhantomData,
            },
        );
        self.connect_nonnative(&product, &one);

        NonNativeTarget::<FF> {
            value: inv_biguint,
            _phantom: PhantomData,
        }
    }

    fn mul_by_nonresidue_nonnative<FF: PrimeField>(
        &mut self,
        x: &NonNativeTarget<FF>,
    ) -> NonNativeTarget<FF> {
        let non_residue = self.constant_nonnative(FF::NONRESIDUE);
        self.mul_nonnative(&x, &non_residue)
    }

    /// Returns `x % |FF|` as a `NonNativeTarget`.
    fn reduce<FF: Field>(&mut self, x: &BigUintTarget) -> NonNativeTarget<FF> {
        let modulus = FF::order();
        let order_target = self.constant_biguint(&modulus);
        let value = self.rem_biguint(x, &order_target);

        NonNativeTarget {
            value,
            _phantom: PhantomData,
        }
    }

    fn reduce_nonnative<FF: Field>(&mut self, x: &NonNativeTarget<FF>) -> NonNativeTarget<FF> {
        let x_biguint = self.nonnative_to_canonical_biguint(x);
        self.reduce(&x_biguint)
    }

    fn bool_to_nonnative<FF: Field>(&mut self, b: &BoolTarget) -> NonNativeTarget<FF> {
        let limbs = vec![U32Target(b.target)];
        let value = BigUintTarget { limbs };

        NonNativeTarget {
            value,
            _phantom: PhantomData,
        }
    }

    // Split a nonnative field element to bits.
    fn split_nonnative_to_bits<FF: Field>(&mut self, x: &NonNativeTarget<FF>) -> Vec<BoolTarget> {
        let num_limbs = x.value.num_limbs();
        let mut result = Vec::with_capacity(num_limbs * 32);

        for i in 0..num_limbs {
            let limb = x.value.get_limb(i);
            let bit_targets = self.split_le_base::<2>(limb.0, 32);
            let mut bits: Vec<_> = bit_targets
                .iter()
                .map(|&t| BoolTarget::new_unsafe(t))
                .collect();

            result.append(&mut bits);
        }

        result
    }

    fn nonnative_conditional_neg<FF: PrimeField>(
        &mut self,
        x: &NonNativeTarget<FF>,
        b: BoolTarget,
    ) -> NonNativeTarget<FF> {
        let not_b = self.not(b);
        let neg = self.neg_nonnative(x);
        let x_if_true = self.mul_nonnative_by_bool(&neg, b);
        let x_if_false = self.mul_nonnative_by_bool(x, not_b);

        self.add_nonnative(&x_if_true, &x_if_false)
    }
}

#[derive(Debug)]
struct NonNativeAdditionGenerator<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> {
    a: NonNativeTarget<FF>,
    b: NonNativeTarget<FF>,
    sum: NonNativeTarget<FF>,
    overflow: BoolTarget,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> SimpleGenerator<F>
    for NonNativeAdditionGenerator<F, D, FF>
{
    fn dependencies(&self) -> Vec<Target> {
        self.a
            .value
            .limbs
            .iter()
            .cloned()
            .chain(self.b.value.limbs.clone())
            .map(|l| l.0)
            .collect()
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let a = FF::from_noncanonical_biguint(witness.get_biguint_target(self.a.value.clone()));
        let b = FF::from_noncanonical_biguint(witness.get_biguint_target(self.b.value.clone()));
        let a_biguint = a.to_canonical_biguint();
        let b_biguint = b.to_canonical_biguint();
        let sum_biguint = a_biguint + b_biguint;
        let modulus = FF::order();
        let (overflow, sum_reduced) = if sum_biguint > modulus {
            (true, sum_biguint - modulus)
        } else {
            (false, sum_biguint)
        };

        out_buffer.set_biguint_target(&self.sum.value, &sum_reduced);
        out_buffer.set_bool_target(self.overflow, overflow);
    }
}

#[derive(Debug)]
struct NonNativeMultipleAddsGenerator<F: RichField + Extendable<D>, const D: usize, FF: PrimeField>
{
    summands: Vec<NonNativeTarget<FF>>,
    sum: NonNativeTarget<FF>,
    overflow: U32Target,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> SimpleGenerator<F>
    for NonNativeMultipleAddsGenerator<F, D, FF>
{
    fn dependencies(&self) -> Vec<Target> {
        self.summands
            .iter()
            .flat_map(|summand| summand.value.limbs.iter().map(|limb| limb.0))
            .collect()
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let summands: Vec<_> = self
            .summands
            .iter()
            .map(|summand| {
                FF::from_noncanonical_biguint(witness.get_biguint_target(summand.value.clone()))
            })
            .collect();
        let summand_biguints: Vec<_> = summands
            .iter()
            .map(|summand| summand.to_canonical_biguint())
            .collect();

        let sum_biguint = summand_biguints
            .iter()
            .fold(BigUint::zero(), |a, b| a + b.clone());

        let modulus = FF::order();
        let (overflow_biguint, sum_reduced) = sum_biguint.div_rem(&modulus);
        let overflow = overflow_biguint.to_u64_digits()[0] as u32;

        out_buffer.set_biguint_target(&self.sum.value, &sum_reduced);
        out_buffer.set_u32_target(self.overflow, overflow);
    }
}

#[derive(Debug)]
struct NonNativeSubtractionGenerator<F: RichField + Extendable<D>, const D: usize, FF: Field> {
    a: NonNativeTarget<FF>,
    b: NonNativeTarget<FF>,
    diff: NonNativeTarget<FF>,
    overflow: BoolTarget,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> SimpleGenerator<F>
    for NonNativeSubtractionGenerator<F, D, FF>
{
    fn dependencies(&self) -> Vec<Target> {
        self.a
            .value
            .limbs
            .iter()
            .cloned()
            .chain(self.b.value.limbs.clone())
            .map(|l| l.0)
            .collect()
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let a = FF::from_noncanonical_biguint(witness.get_biguint_target(self.a.value.clone()));
        let b = FF::from_noncanonical_biguint(witness.get_biguint_target(self.b.value.clone()));
        let a_biguint = a.to_canonical_biguint();
        let b_biguint = b.to_canonical_biguint();

        let modulus = FF::order();
        let (diff_biguint, overflow) = if a_biguint >= b_biguint {
            (a_biguint - b_biguint, false)
        } else {
            (modulus + a_biguint - b_biguint, true)
        };

        out_buffer.set_biguint_target(&self.diff.value, &diff_biguint);
        out_buffer.set_bool_target(self.overflow, overflow);
    }
}

#[derive(Debug)]
struct NonNativeMultiplicationGenerator<F: RichField + Extendable<D>, const D: usize, FF: Field> {
    a: NonNativeTarget<FF>,
    b: NonNativeTarget<FF>,
    prod: NonNativeTarget<FF>,
    overflow: BigUintTarget,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> SimpleGenerator<F>
    for NonNativeMultiplicationGenerator<F, D, FF>
{
    fn dependencies(&self) -> Vec<Target> {
        self.a
            .value
            .limbs
            .iter()
            .cloned()
            .chain(self.b.value.limbs.clone())
            .map(|l| l.0)
            .collect()
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let a = FF::from_noncanonical_biguint(witness.get_biguint_target(self.a.value.clone()));
        let b = FF::from_noncanonical_biguint(witness.get_biguint_target(self.b.value.clone()));
        let a_biguint = a.to_canonical_biguint();
        let b_biguint = b.to_canonical_biguint();

        let prod_biguint = a_biguint * b_biguint;

        let modulus = FF::order();
        let (overflow_biguint, prod_reduced) = prod_biguint.div_rem(&modulus);

        out_buffer.set_biguint_target(&self.prod.value, &prod_reduced);
        out_buffer.set_biguint_target(&self.overflow, &overflow_biguint);
    }
}

#[derive(Debug)]
struct NonNativeInverseGenerator<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> {
    x: NonNativeTarget<FF>,
    inv: BigUintTarget,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> SimpleGenerator<F>
    for NonNativeInverseGenerator<F, D, FF>
{
    fn dependencies(&self) -> Vec<Target> {
        self.x.value.limbs.iter().map(|&l| l.0).collect()
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let x = FF::from_noncanonical_biguint(witness.get_biguint_target(self.x.value.clone()));
        let inv = x.inverse();
        let inv_biguint = inv.to_canonical_biguint();
        out_buffer.set_biguint_target(&self.inv, &inv_biguint);
    }
}

#[cfg(test)]
mod tests {
    use crate::field::bn128_base::Bn128Base;
    use crate::gadgets::biguint::BigUintTarget;
    use crate::gadgets::gates::u28_to_u32::U28ToU32Gate;
    use crate::gadgets::gates::u32_to_u28::U32ToU28Gate;
    use crate::gadgets::nonnative_fp::U32Target;
    use crate::gadgets::nonnative_fp::{CircuitBuilderNonNative, NonNativeTarget};
    use anyhow::Result;
    use log::LevelFilter;
    use plonky2::field::types::{Field, PrimeField, Sample};
    use plonky2::iop::target::Target;
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use std::marker::PhantomData;

    #[test]
    fn test_nonnative_add() -> Result<()> {
        let mut builder = env_logger::Builder::from_default_env();
        builder.format_timestamp(None);
        builder.filter_level(LevelFilter::Info);
        builder.try_init()?;

        type FF = Bn128Base;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let x_ff = FF::rand();
        let y_ff = FF::rand();
        let sum_ff = x_ff + y_ff;

        let config = CircuitConfig::pairing_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative(x_ff);
        let y = builder.constant_nonnative(y_ff);
        let sum = builder.add_nonnative(&x, &y);

        let sum_expected = builder.constant_nonnative(sum_ff);
        builder.connect_nonnative(&sum, &sum_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_conversion_gates() -> Result<()> {
        type FF = Bn128Base;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let x_ff = FF::rand();

        let config = CircuitConfig::pairing_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config.clone());

        let x = builder.constant_nonnative(x_ff);

        let gate = U32ToU28Gate::<F, D>::new_from_config(&config);
        let (row, copy) = builder.find_slot(gate, &[], &[]);
        for i in 0..8 {
            builder.connect(
                Target::wire(row, gate.wire_ith_input(copy, i)),
                x.value.limbs[i].0,
            );
        }
        let mut x_targets = Vec::new();
        for i in 0..10 {
            x_targets.push(Target::wire(row, gate.wire_ith_output_result(copy, i)));
        }

        let gate2 = U28ToU32Gate::<F, D>::new_from_config(&config);
        let (row, copy) = builder.find_slot(gate2, &[], &[]);
        for i in 0..10 {
            builder.connect(
                Target::wire(row, gate2.wire_ith_input(copy, i)),
                x_targets[i],
            );
        }
        let mut targets = Vec::new();
        for i in 0..8 {
            targets.push(U32Target {
                0: Target::wire(row, gate2.wire_ith_output_result(copy, i)),
            });
        }

        let new_x = NonNativeTarget::<FF> {
            value: BigUintTarget { limbs: targets },
            _phantom: PhantomData,
        };
        builder.connect_nonnative(&x, &new_x);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_sub() -> Result<()> {
        type FF = Bn128Base;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let x_ff = FF::rand();
        let mut y_ff = FF::rand();
        while y_ff.to_canonical_biguint() > x_ff.to_canonical_biguint() {
            y_ff = FF::rand();
        }
        let diff_ff = x_ff - y_ff;

        let config = CircuitConfig::pairing_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative(x_ff);
        let y = builder.constant_nonnative(y_ff);
        let diff = builder.sub_nonnative(&x, &y);

        let diff_expected = builder.constant_nonnative(diff_ff);
        builder.connect_nonnative(&diff, &diff_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_mul() -> Result<()> {
        type FF = Bn128Base;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand(); // FF::from_canonical_u32(1);
        let y_ff = FF::rand(); // FF::from_canonical_u32(2);
        let product_ff = x_ff * y_ff;

        let config = CircuitConfig::pairing_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative(x_ff);
        let y = builder.constant_nonnative(y_ff);
        let product_expected = builder.constant_nonnative(product_ff);
        let product = builder.mul_nonnative(&x, &y);

        //let product_expected = builder.constant_nonnative(product_ff);
        builder.connect_nonnative(&product, &product_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_neg() -> Result<()> {
        type FF = Bn128Base;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand();
        let neg_x_ff = -x_ff;

        let config = CircuitConfig::pairing_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative(x_ff);
        let neg_x = builder.neg_nonnative(&x);

        let neg_x_expected = builder.constant_nonnative(neg_x_ff);
        builder.connect_nonnative(&neg_x, &neg_x_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_inv() -> Result<()> {
        type FF = Bn128Base;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand();
        let inv_x_ff = x_ff.inverse();

        let config = CircuitConfig::pairing_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative(x_ff);
        let inv_x = builder.inv_nonnative(&x);

        let inv_x_expected = builder.constant_nonnative(inv_x_ff);
        builder.connect_nonnative(&inv_x, &inv_x_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }
}
