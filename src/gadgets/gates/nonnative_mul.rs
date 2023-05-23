use core::marker::PhantomData;
use num::{BigUint, FromPrimitive, ToPrimitive, Zero};

use plonky2::field::extension::Extendable;
use plonky2::field::packed::PackedField;
use plonky2::field::types::Field;
use plonky2::gates::gate::Gate;
use plonky2::gates::packed_util::PackedEvaluableBase;
use plonky2::gates::util::StridedConstraintConsumer;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::iop::generator::{GeneratedValues, SimpleGenerator, WitnessGenerator};
use plonky2::iop::target::Target;
use plonky2::iop::wire::Wire;
use plonky2::iop::witness::{PartitionWitness, Witness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::vars::{
    EvaluationTargets, EvaluationVars, EvaluationVarsBase, EvaluationVarsBaseBatch,
    EvaluationVarsBasePacked,
};

// 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47
const NONNATIVE_BASE: [u32; 8] = [
    0xd87cfd47, 0x3c208c16, 0x6871ca8d, 0x97816a91, 0x8181585d, 0xb85045b6, 0xe131a029, 0x30644e72,
];
const NONNATIVE_BASE_28: [u32; 10] = [
    0x87cfd47, 0x208c16d, 0x1ca8d3c, 0x6a91687, 0x85d9781, 0xb681815, 0x9b85045, 0xe131a02,
    0x0644e72, 0x3,
];

/// A gate to perform a addition of two nonnative with 8 limbs.
#[derive(Copy, Clone, Debug)]
pub struct NonnativeMulGate<F: RichField + Extendable<D>, const D: usize> {
    pub num_ops: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> NonnativeMulGate<F, D> {
    pub fn new_from_config(config: &CircuitConfig) -> Self {
        Self {
            num_ops: Self::num_ops(config),
            _phantom: PhantomData,
        }
    }

    pub(crate) fn num_ops(config: &CircuitConfig) -> usize {
        let wires_per_op = 296;
        let routed_wires_per_op = 30;
        (config.num_wires / wires_per_op).min(config.num_routed_wires / routed_wires_per_op)
    }

    pub fn wire_ith_input_x(&self, i: usize, j: usize) -> usize {
        debug_assert!(i < self.num_ops);
        debug_assert!(j < 10);
        30 * i + j
    }
    pub fn wire_ith_input_y(&self, i: usize, j: usize) -> usize {
        debug_assert!(i < self.num_ops);
        debug_assert!(j < 10);
        30 * i + 10 + j
    }
    pub fn wire_ith_output_result(&self, i: usize, j: usize) -> usize {
        debug_assert!(i < self.num_ops);
        debug_assert!(j < 10);
        30 * i + 20 + j
    }
    pub fn wire_ith_quotient(&self, i: usize, j: usize) -> usize {
        debug_assert!(i < self.num_ops);
        debug_assert!(j < 10);
        30 * self.num_ops + 285 * i
    }
    pub fn wire_ith_output_jth_limb28_kth_limb2_bit(&self, i: usize, j: usize, k: usize) -> usize {
        debug_assert!(i < self.num_ops);
        debug_assert!(j < 10);
        debug_assert!(k < 14);
        debug_assert!(j != 9 || k < 2);
        30 * self.num_ops + 285 * i + 10 + 14 * j + k
    }
    pub fn wire_ith_quotient_jth_limb28_kth_limb2_bit(
        &self,
        i: usize,
        j: usize,
        k: usize,
    ) -> usize {
        debug_assert!(i < self.num_ops);
        debug_assert!(j < 10);
        debug_assert!(k < 14);
        debug_assert!(j != 9 || k < 2);
        30 * self.num_ops + 285 * i + 138 + 14 * j + k
    }
    pub fn wire_ith_output_jth_limb32_kth_limb2_bit(&self, i: usize, j: usize, k: usize) -> usize {
        debug_assert!(i < self.num_ops);
        debug_assert!(j < 8);
        debug_assert!(k < 16);
        30 * self.num_ops + 285 * i + 10 + 16 * j + k
    }
    pub fn wire_ith_quotient_jth_limb32_kth_limb2_bit(
        &self,
        i: usize,
        j: usize,
        k: usize,
    ) -> usize {
        debug_assert!(i < self.num_ops);
        debug_assert!(j < 8);
        debug_assert!(k < 16);
        30 * self.num_ops + 285 * i + 138 + 16 * j + k
    }
    pub fn wire_ith_carry_diff(&self, i: usize, j: usize) -> usize {
        debug_assert!(i < self.num_ops);
        debug_assert!(j < 19);
        30 * self.num_ops + 285 * i + 138 + 128 + j
    }

    pub fn limb_bits() -> usize {
        2
    }
    // We have 14 2-bit limbs for a 28-bit limb.
    pub fn num_limbs() -> usize {
        28 / Self::limb_bits()
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for NonnativeMulGate<F, D> {
    fn id(&self) -> String {
        format!("{self:?}")
    }

    fn export_circom_verification_code(&self) -> String {
        todo!()
    }
    fn export_solidity_verification_code(&self) -> String {
        todo!()
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        let mut constraints = Vec::with_capacity(self.num_constraints());
        for i in 0..self.num_ops {
            let mut input_x = vec![F::Extension::ZERO; 10];
            let mut input_y = vec![F::Extension::ZERO; 10];
            let mut output_result = vec![F::Extension::ZERO; 10];
            let mut quotient = vec![F::Extension::ZERO; 10];
            let mut carry_diff = vec![F::Extension::ZERO; 19];

            for j in 0..10 {
                input_x[j] = vars.local_wires[self.wire_ith_input_x(i, j)];
                input_y[j] = vars.local_wires[self.wire_ith_input_y(i, j)];
                output_result[j] = vars.local_wires[self.wire_ith_output_result(i, j)];
                quotient[j] = vars.local_wires[self.wire_ith_quotient(i, j)];
            }
            for j in 0..19 {
                carry_diff[j] = vars.local_wires[self.wire_ith_carry_diff(i, j)];
            }

            // Range-check output_result and quotient to be at most 28 bits each limb.
            for j in 0..10 {
                let limb_base = F::Extension::from_canonical_u64(1u64 << Self::limb_bits());
                let num_limbs = if j == 9 { 2 } else { Self::num_limbs() };

                let mut combined_limbs = F::Extension::ZERO;
                for k in (0..num_limbs).rev() {
                    let this_limb =
                        vars.local_wires[self.wire_ith_output_jth_limb28_kth_limb2_bit(i, j, k)];
                    let max_limb = 1 << Self::limb_bits();
                    let product = (0..max_limb)
                        .map(|x| this_limb - F::Extension::from_canonical_usize(x))
                        .product();
                    constraints.push(product);

                    combined_limbs = limb_base * combined_limbs + this_limb;
                }
                constraints.push(combined_limbs - output_result[j]);

                let mut combined_limbs = F::Extension::ZERO;
                for k in (0..num_limbs).rev() {
                    let this_limb =
                        vars.local_wires[self.wire_ith_quotient_jth_limb28_kth_limb2_bit(i, j, k)];
                    let max_limb = 1 << Self::limb_bits();
                    let product = (0..max_limb)
                        .map(|x| this_limb - F::Extension::from_canonical_usize(x))
                        .product();
                    constraints.push(product);

                    combined_limbs = limb_base * combined_limbs + this_limb;
                }
                constraints.push(combined_limbs - quotient[j]);
            }

            let mut last_carry_diff = F::Extension::ZERO;
            let base = F::Extension::from_canonical_u32(1 << 28);
            // For each limb, checks input_x * input_y + last_carry_left ===
            // output_result + quotient * NONNATIVE_BASE + last_carry_right.
            for j in 0..19 {
                let mut left = F::Extension::ZERO;
                let mut right = F::Extension::ZERO;

                let start_index = if j < 10 { 0 } else { j - 9 };
                let end_index = if j < 10 { j } else { 9 };
                for k in 0..end_index - start_index + 1 {
                    left = left + input_x[k + start_index] * input_y[end_index - k];
                    right = right
                        + quotient[k + start_index]
                            * F::Extension::from_canonical_u32(NONNATIVE_BASE_28[end_index - k]);
                }

                right = if j < 10 {
                    right + output_result[j]
                } else {
                    right
                };

                constraints.push(left - right - last_carry_diff + base * carry_diff[j]);
                last_carry_diff = carry_diff[j];
            }
        }

        constraints
    }

    fn eval_unfiltered_base_one(
        &self,
        _vars: EvaluationVarsBase<F>,
        _yield_constr: StridedConstraintConsumer<F>,
    ) {
        panic!("use eval_unfiltered_base_packed instead");
    }

    fn eval_unfiltered_base_batch(&self, vars_base: EvaluationVarsBaseBatch<F>) -> Vec<F> {
        self.eval_unfiltered_base_batch_packed(vars_base)
    }

    fn eval_unfiltered_circuit(
        &self,
        _builder: &mut CircuitBuilder<F, D>,
        _vars: EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
        todo!("eval_unfiltered_circuit")
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<Box<dyn WitnessGenerator<F>>> {
        (0..self.num_ops)
            .map(|i| {
                let g: Box<dyn WitnessGenerator<F>> = Box::new(
                    NonnativeMulGenerator {
                        gate: *self,
                        row,
                        i,
                        _phantom: PhantomData,
                    }
                    .adapter(),
                );
                g
            })
            .collect()
    }

    fn num_wires(&self) -> usize {
        296 + 19
    }

    fn num_constants(&self) -> usize {
        0
    }

    fn degree(&self) -> usize {
        1 << Self::limb_bits()
    }

    fn num_constraints(&self) -> usize {
        self.num_ops * (19 + (10 + 128) * 2)
    }
}

impl<F: RichField + Extendable<D>, const D: usize> PackedEvaluableBase<F, D>
    for NonnativeMulGate<F, D>
{
    fn eval_unfiltered_base_packed<P: PackedField<Scalar = F>>(
        &self,
        vars: EvaluationVarsBasePacked<P>,
        mut yield_constr: StridedConstraintConsumer<P>,
    ) {
        for i in 0..self.num_ops {
            let mut input_x = vec![P::ZEROS; 10];
            let mut input_y = vec![P::ZEROS; 10];
            let mut output_result = vec![P::ZEROS; 10];
            let mut quotient = vec![P::ZEROS; 10];
            let mut carry_diff = vec![P::ZEROS; 19];

            for j in 0..10 {
                input_x[j] = vars.local_wires[self.wire_ith_input_x(i, j)];
                input_y[j] = vars.local_wires[self.wire_ith_input_y(i, j)];
                output_result[j] = vars.local_wires[self.wire_ith_output_result(i, j)];
                quotient[j] = vars.local_wires[self.wire_ith_quotient(i, j)];
            }
            for j in 0..19 {
                carry_diff[j] = vars.local_wires[self.wire_ith_carry_diff(i, j)];
            }

            // Range-check output_result and quotient to be at most 28 bits each limb.
            for j in 0..10 {
                let limb_base = F::from_canonical_u64(1u64 << Self::limb_bits());
                let num_limbs = if j == 9 { 2 } else { Self::num_limbs() };

                let mut combined_limbs = P::ZEROS;
                for k in (0..num_limbs).rev() {
                    let this_limb =
                        vars.local_wires[self.wire_ith_output_jth_limb28_kth_limb2_bit(i, j, k)];
                    let max_limb = 1 << Self::limb_bits();
                    let product = (0..max_limb)
                        .map(|x| this_limb - F::from_canonical_usize(x))
                        .product();
                    yield_constr.one(product);

                    combined_limbs = combined_limbs * limb_base.clone() + this_limb;
                }
                yield_constr.one(combined_limbs - output_result[j]);

                let mut combined_limbs = P::ZEROS;
                for k in (0..num_limbs).rev() {
                    let this_limb =
                        vars.local_wires[self.wire_ith_quotient_jth_limb28_kth_limb2_bit(i, j, k)];
                    let max_limb = 1 << Self::limb_bits();
                    let product = (0..max_limb)
                        .map(|x| this_limb - F::from_canonical_usize(x))
                        .product();
                    yield_constr.one(product);

                    combined_limbs = combined_limbs * limb_base.clone() + this_limb;
                }
                yield_constr.one(combined_limbs - quotient[j]);
            }

            let mut last_carry_diff = P::ZEROS;
            let base = F::from_canonical_u32(1 << 28);
            // For each limb, checks input_x * input_y + last_carry_left ===
            // output_result + quotient * NONNATIVE_BASE + last_carry_right.
            for j in 0..19 {
                let mut left = P::ZEROS;
                let mut right = P::ZEROS;

                let start_index = if j < 10 { 0 } else { j - 9 };
                let end_index = if j < 10 { j } else { 9 };
                for k in 0..end_index - start_index + 1 {
                    left = left + input_x[k + start_index] * input_y[end_index - k];
                    right = right
                        + quotient[k + start_index]
                            * F::from_canonical_u32(NONNATIVE_BASE_28[end_index - k]);
                }

                right = if j < 10 {
                    right + output_result[j]
                } else {
                    right
                };

                yield_constr.one(left - right - last_carry_diff + carry_diff[j] * base.clone());
                last_carry_diff = carry_diff[j];
            }
        }
    }
}

#[derive(Clone, Debug)]
struct NonnativeMulGenerator<F: RichField + Extendable<D>, const D: usize> {
    gate: NonnativeMulGate<F, D>,
    row: usize,
    i: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F>
    for NonnativeMulGenerator<F, D>
{
    fn dependencies(&self) -> Vec<Target> {
        let local_target = |column| Target::wire(self.row, column);

        let x_range: Vec<_> = (0..8)
            .map(|i| local_target(self.gate.wire_ith_input_x(self.i, i)))
            .collect();
        let y_range: Vec<_> = (0..8)
            .map(|i| local_target(self.gate.wire_ith_input_y(self.i, i)))
            .collect();

        [x_range, y_range].concat()
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let local_wire = |column| Wire {
            row: self.row,
            column,
        };

        let get_local_wire = |column| witness.get_wire(local_wire(column));

        let mut input_x_u32s = vec![0u32; 8];
        let mut input_y_u32s = vec![0u32; 8];
        let mut input_x_biguint = BigUint::zero();
        let mut input_y_biguint = BigUint::zero();
        for j in (0..10).rev() {
            let input_x = get_local_wire(self.gate.wire_ith_input_x(self.i, j));
            input_x_u32s[j] = input_x.to_canonical_u64() as u32;
            input_x_biguint += BigUint::from_u32(input_x_u32s[j]).unwrap();
            if j != 0 {
                input_x_biguint = input_x_biguint << 28;
            };

            let input_y = get_local_wire(self.gate.wire_ith_input_y(self.i, j));
            input_y_u32s[j] = input_y.to_canonical_u64() as u32;
            input_y_biguint += BigUint::from_u32(input_y_u32s[j]).unwrap();
            if j != 0 {
                input_y_biguint = input_y_biguint << 28;
            };
        }

        let result_biguint = input_x_biguint * input_y_biguint;
        let output_biguint = result_biguint.clone() % BigUint::from_slice(&NONNATIVE_BASE);
        let quotient_biguint = result_biguint.clone() / BigUint::from_slice(&NONNATIVE_BASE);

        for j in 0..10 {
            let result_limb: BigUint =
                (output_biguint.clone() >> (j * 28)) & BigUint::from_u32(0xfffffff).unwrap();
            let output_result = F::from_canonical_u32(result_limb.to_u32().unwrap());
            out_buffer.set_wire(
                local_wire(self.gate.wire_ith_output_result(self.i, j)),
                output_result.clone(),
            );

            let quotient_limb: BigUint =
                (quotient_biguint.clone() >> (j * 28)) & BigUint::from_u32(0xfffffff).unwrap();
            let quotient_result = F::from_canonical_u32(quotient_limb.to_u32().unwrap());
            out_buffer.set_wire(
                local_wire(self.gate.wire_ith_quotient(self.i, j)),
                quotient_result.clone(),
            );
        }

        let output_u32s = output_biguint.to_u32_digits();
        let quotient_u32s = quotient_biguint.to_u32_digits();
        for j in 0..8 {
            let num_limbs = 16;
            let limb_base = 1 << 2;

            let output_limbs: Vec<_> = (0..num_limbs)
                .scan(output_u32s[j] as u64, |acc, _| {
                    let tmp = *acc % limb_base;
                    *acc /= limb_base;
                    Some(F::from_canonical_u64(tmp))
                })
                .collect();
            for k in 0..num_limbs {
                let wire = local_wire(
                    self.gate
                        .wire_ith_output_jth_limb32_kth_limb2_bit(self.i, j, k),
                );
                out_buffer.set_wire(wire, output_limbs[k].clone());
            }

            let quotient_limbs: Vec<_> = (0..num_limbs)
                .scan(quotient_u32s[j] as u64, |acc, _| {
                    let tmp = *acc % limb_base;
                    *acc /= limb_base;
                    Some(F::from_canonical_u64(tmp))
                })
                .collect();
            for k in 0..num_limbs {
                let wire = local_wire(
                    self.gate
                        .wire_ith_quotient_jth_limb32_kth_limb2_bit(self.i, j, k),
                );
                out_buffer.set_wire(wire, quotient_limbs[k].clone());
            }
        }

        let mut last_carry_left = 0u64;
        let mut last_carry_right = 0u64;
        let base = 1 << 28u64;
        // For each limb, checks input_x * input_y + last_carry_left ===
        // output_result + quotient * NONNATIVE_BASE + last_carry_right.
        for j in 0..19 {
            let mut left = last_carry_left;
            let mut right = last_carry_right;

            let start_index = if j < 10 { 0 } else { j - 9 };
            let end_index = if j < 10 { j } else { 9 };
            for k in 0..end_index - start_index + 1 {
                left = left
                    + input_x_u32s[k + start_index] as u64 * input_y_u32s[end_index - k] as u64;
                right = right
                    + quotient_u32s[k + start_index] as u64
                        * NONNATIVE_BASE_28[end_index - k] as u64;
            }

            right = if j < 10 {
                right + output_u32s[j] as u64
            } else {
                right
            };

            let carry_left = left / base;
            let carry_right = right / base;

            let wire = local_wire(self.gate.wire_ith_carry_diff(self.i, j));
            out_buffer.set_wire(
                wire,
                F::from_canonical_u64((carry_left - carry_right) as u64),
            );

            last_carry_left = carry_left;
            last_carry_right = carry_right;
        }
    }
}

#[cfg(test)]
mod tests {
    use plonky2::field::goldilocks_field::GoldilocksField;
    use plonky2::gates::gate_testing::test_low_degree;

    use super::*;

    #[test]
    fn low_degree() {
        test_low_degree::<GoldilocksField, _, 4>(NonnativeMulGate::<GoldilocksField, 4> {
            num_ops: 1,
            _phantom: PhantomData,
        })
    }
}
