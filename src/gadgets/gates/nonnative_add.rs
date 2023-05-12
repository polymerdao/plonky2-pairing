use core::marker::PhantomData;

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

const NONNATIVE_BASE: [u32; 8] = [
    0xd87cfd47, 0x3c208c16, 0x6871ca8d, 0x97816a91, 0x8181585d, 0xb85045b6, 0xe131a029, 0x30644e72,
];

/// A gate to perform a addition of two nonnative with 8 limbs.
#[derive(Copy, Clone, Debug)]
pub struct NonnativeAddGate<F: RichField + Extendable<D>, const D: usize> {
    pub num_ops: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> NonnativeAddGate<F, D> {
    pub fn new_from_config(config: &CircuitConfig) -> Self {
        Self {
            num_ops: Self::num_ops(config),
            _phantom: PhantomData,
        }
    }

    pub(crate) fn num_ops(config: &CircuitConfig) -> usize {
        let wires_per_op = 169;
        let routed_wires_per_op = 24;
        (config.num_wires / wires_per_op).min(config.num_routed_wires / routed_wires_per_op)
    }

    pub fn wire_ith_input_x(&self, i: usize) -> usize {
        debug_assert!(i < self.num_ops);
        24 * i
    }
    pub fn wire_ith_input_y(&self, i: usize) -> usize {
        debug_assert!(i < self.num_ops);
        24 * i + 8
    }
    pub fn wire_ith_output_result(&self, i: usize) -> usize {
        debug_assert!(i < self.num_ops);
        24 * i + 16
    }
    pub fn wire_ith_carry(&self, i: usize) -> usize {
        debug_assert!(i < self.num_ops);
        24 * self.num_ops + 145 * i
    }
    pub fn wire_ith_carry_l(&self, i: usize) -> usize {
        debug_assert!(i < self.num_ops);
        24 * self.num_ops + 145 * i + 1
    }
    pub fn wire_ith_carry_r(&self, i: usize) -> usize {
        debug_assert!(i < self.num_ops);
        24 * self.num_ops + 145 * i + 9
    }
    pub fn wire_ith_output_jth_limb32_kth_limb2_bit(&self, i: usize, j: usize, k: usize) -> usize {
        debug_assert!(i < self.num_ops);
        debug_assert!(j < 8);
        debug_assert!(k < 16);
        24 * self.num_ops + 145 * i + 17 + 16 * j + k
    }

    pub fn limb_bits() -> usize {
        2
    }
    // We have 16 2-bit limbs for a 32-bit limb.
    pub fn num_limbs() -> usize {
        32 / Self::limb_bits()
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for NonnativeAddGate<F, D> {
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
            let mut input_x = vec![0; 8];
            let mut input_y = vec![0; 8];
            let mut output_result = vec![0; 8];
            let mut carry_l = vec![0; 8];
            let mut carry_r = vec![0; 8];
            let carry = vars.local_wires[self.wire_ith_carry(i)];

            for j in 0..8 {
                input_x[j] = vars.local_wires[self.wire_ith_input_x(i) + j];
                input_y[j] = vars.local_wires[self.wire_ith_input_y(i) + j];
                output_result[j] = vars.local_wires[self.wire_ith_output_result(i) + j];
                carry_l[j] = vars.local_wires[self.wire_ith_carry_l(i) + j];
                carry_r[j] = vars.local_wires[self.wire_ith_carry_r(i) + j];
            }

            let base = F::Extension::from_canonical_u64(1 << 32u64);
            let mut results_l = vec![0; 8];
            let mut results_r = vec![0; 8];

            for j in 0..8 {
                results_l[j] = input_x[j] + input_y[j] + carry_l[j] * base;
                results_r[j] = output_result[j]
                    + carry * F::Extension::from_canonical_u32(NONNATIVE_BASE[j])
                    + carry_r[j] * base;
                constraints.push(results_r[j] - results_l[j]);
                constraints.push(carry_l[j] * (F::Extension::ONE - carry_l[j]));
                constraints.push(carry_r[j] * (F::Extension::ONE - carry_r[j]));
            }
            constraints.push(carry * (F::Extension::ONE - carry));

            // Range-check output_result to be at most 32 bits.
            for j in 0..8 {
                let mut combined_limbs = F::Extension::ZERO;
                let limb_base = F::Extension::from_canonical_u64(1u64 << Self::limb_bits());
                for k in (0..Self::num_limbs()).rev() {
                    let this_limb =
                        vars.local_wires[self.wire_ith_output_jth_limb32_kth_limb2_bit(i, j, k)];
                    let max_limb = 1 << Self::limb_bits();
                    let product = (0..max_limb)
                        .map(|x| this_limb - F::Extension::from_canonical_usize(x))
                        .product();
                    constraints.push(product);

                    combined_limbs = limb_base * combined_limbs + this_limb;
                }
                constraints.push(combined_limbs - output_result[j]);
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
        builder: &mut CircuitBuilder<F, D>,
        vars: EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
        todo!("eval_unfiltered_circuit")
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<Box<dyn WitnessGenerator<F>>> {
        (0..self.num_ops)
            .map(|i| {
                let g: Box<dyn WitnessGenerator<F>> = Box::new(
                    NonnativeAddGenerator {
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
        169
    }

    fn num_constants(&self) -> usize {
        0
    }

    fn degree(&self) -> usize {
        1 << Self::limb_bits()
    }

    fn num_constraints(&self) -> usize {
        self.num_ops * (33 + 16 * 8)
    }
}

impl<F: RichField + Extendable<D>, const D: usize> PackedEvaluableBase<F, D>
    for NonnativeAddGate<F, D>
{
    fn eval_unfiltered_base_packed<P: PackedField<Scalar = F>>(
        &self,
        vars: EvaluationVarsBasePacked<P>,
        mut yield_constr: StridedConstraintConsumer<P>,
    ) {
        for i in 0..self.num_ops {
            let mut input_x = vec![0; 8];
            let mut input_y = vec![0; 8];
            let mut output_result = vec![0; 8];
            let mut carry_l = vec![0; 8];
            let mut carry_r = vec![0; 8];
            let carry = vars.local_wires[self.wire_ith_carry(i)];

            for j in 0..8 {
                input_x[j] = vars.local_wires[self.wire_ith_input_x(i) + j];
                input_y[j] = vars.local_wires[self.wire_ith_input_y(i) + j];
                output_result[j] = vars.local_wires[self.wire_ith_output_result(i) + j];
                carry_l[j] = vars.local_wires[self.wire_ith_carry_l(i) + j];
                carry_r[j] = vars.local_wires[self.wire_ith_carry_r(i) + j];
            }

            let base = F::Extension::from_canonical_u64(1 << 32u64);
            let mut results_l = vec![0; 8];
            let mut results_r = vec![0; 8];

            for j in 0..8 {
                results_l[j] = input_x[j] + input_y[j] + carry_l[j] * base;
                results_r[j] = output_result[j]
                    + carry * F::from_canonical_u32(NONNATIVE_BASE[j])
                    + carry_r[j] * base;
                yield_constr.one(results_r[j] - results_l[j]);
                yield_constr.one(carry_l[j] * (F::Extension::ONE - carry_l[j]));
                yield_constr.one(carry_r[j] * (F::Extension::ONE - carry_r[j]));
            }
            yield_constr.one(carry * (F::Extension::ONE - carry));

            // Range-check output_result to be at most 32 bits.
            for j in 0..8 {
                let mut combined_limbs = F::Extension::ZERO;
                let limb_base = F::Extension::from_canonical_u64(1u64 << Self::limb_bits());
                for k in (0..Self::num_limbs()).rev() {
                    let this_limb =
                        vars.local_wires[self.wire_ith_output_jth_limb32_kth_limb2_bit(i, j, k)];
                    let max_limb = 1 << Self::limb_bits();
                    let product = (0..max_limb)
                        .map(|x| this_limb - F::Extension::from_canonical_usize(x))
                        .product();
                    yield_constr.one(product);

                    combined_limbs = limb_base * combined_limbs + this_limb;
                }
                yield_constr.one(combined_limbs - output_result[j]);
            }
        }
    }
}

#[derive(Clone, Debug)]
struct NonnativeAddGenerator<F: RichField + Extendable<D>, const D: usize> {
    gate: NonnativeAddGate<F, D>,
    row: usize,
    i: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F>
    for NonnativeAddGenerator<F, D>
{
    fn dependencies(&self) -> Vec<Target> {
        let local_target = |column| Target::wire(self.row, column);

        let x_base = self.gate.wire_ith_input_x(self.i);
        let y_base = self.gate.wire_ith_input_y(self.i);

        let x_range: Vec<_> = (0..8).map(|i| local_target(x_base + i)).collect();
        let y_range: Vec<_> = (0..8).map(|i| local_target(y_base + i)).collect();

        [x_range, y_range].concat()
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let local_wire = |column| Wire {
            row: self.row,
            column,
        };

        let get_local_wire = |column| witness.get_wire(local_wire(column));

        let input_x = get_local_wire(self.gate.wire_ith_input_x(self.i));
        let input_y = get_local_wire(self.gate.wire_ith_input_y(self.i));
        let input_borrow = get_local_wire(self.gate.wire_ith_input_borrow(self.i));

        let result_initial = input_x - input_y - input_borrow;
        let result_initial_u64 = result_initial.to_canonical_u64();
        let output_borrow = if result_initial_u64 > 1 << 32u64 {
            F::ONE
        } else {
            F::ZERO
        };

        let base = F::from_canonical_u64(1 << 32u64);
        let output_result = result_initial + base * output_borrow;

        let output_result_wire = local_wire(self.gate.wire_ith_output_result(self.i));
        let output_borrow_wire = local_wire(self.gate.wire_ith_output_borrow(self.i));

        out_buffer.set_wire(output_result_wire, output_result);
        out_buffer.set_wire(output_borrow_wire, output_borrow);

        let output_result_u64 = output_result.to_canonical_u64();

        let num_limbs = NonnativeAddGate::<F, D>::num_limbs();
        let limb_base = 1 << NonnativeAddGate::<F, D>::limb_bits();
        let output_limbs: Vec<_> = (0..num_limbs)
            .scan(output_result_u64, |acc, _| {
                let tmp = *acc % limb_base;
                *acc /= limb_base;
                Some(F::from_canonical_u64(tmp))
            })
            .collect();

        for j in 0..num_limbs {
            let wire = local_wire(self.gate.wire_ith_output_jth_limb(self.i, j));
            out_buffer.set_wire(wire, output_limbs[j]);
        }
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use plonky2::field::extension::quartic::QuarticExtension;
    use plonky2::field::goldilocks_field::GoldilocksField;
    use plonky2::field::types::{PrimeField64, Sample};
    use plonky2::gates::gate_testing::{test_eval_fns, test_low_degree};
    use plonky2::hash::hash_types::HashOut;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use rand::rngs::OsRng;
    use rand::Rng;

    use super::*;

    #[test]
    fn low_degree() {
        test_low_degree::<GoldilocksField, _, 4>(NonnativeAddGate::<GoldilocksField, 4> {
            num_ops: 3,
            _phantom: PhantomData,
        })
    }

    #[test]
    fn eval_fns() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        test_eval_fns::<F, C, _, D>(NonnativeAddGate::<GoldilocksField, D> {
            num_ops: 3,
            _phantom: PhantomData,
        })
    }

    #[test]
    fn test_gate_constraint() {
        type F = GoldilocksField;
        type FF = QuarticExtension<GoldilocksField>;
        const D: usize = 4;
        const NUM_U32_SUBTRACTION_OPS: usize = 3;

        fn get_wires(inputs_x: Vec<u64>, inputs_y: Vec<u64>, borrows: Vec<u64>) -> Vec<FF> {
            let mut v0 = Vec::new();
            let mut v1 = Vec::new();

            let limb_bits = NonnativeAddGate::<F, D>::limb_bits();
            let num_limbs = NonnativeAddGate::<F, D>::num_limbs();
            let limb_base = 1 << limb_bits;
            for c in 0..NUM_U32_SUBTRACTION_OPS {
                let input_x = F::from_canonical_u64(inputs_x[c]);
                let input_y = F::from_canonical_u64(inputs_y[c]);
                let input_borrow = F::from_canonical_u64(borrows[c]);

                let result_initial = input_x - input_y - input_borrow;
                let result_initial_u64 = result_initial.to_canonical_u64();
                let output_borrow = if result_initial_u64 > 1 << 32u64 {
                    F::ONE
                } else {
                    F::ZERO
                };

                let base = F::from_canonical_u64(1 << 32u64);
                let output_result = result_initial + base * output_borrow;

                let output_result_u64 = output_result.to_canonical_u64();

                let mut output_limbs: Vec<_> = (0..num_limbs)
                    .scan(output_result_u64, |acc, _| {
                        let tmp = *acc % limb_base;
                        *acc /= limb_base;
                        Some(F::from_canonical_u64(tmp))
                    })
                    .collect();

                v0.push(input_x);
                v0.push(input_y);
                v0.push(input_borrow);
                v0.push(output_result);
                v0.push(output_borrow);
                v1.append(&mut output_limbs);
            }

            v0.iter().chain(v1.iter()).map(|&x| x.into()).collect()
        }

        let mut rng = OsRng;
        let inputs_x = (0..NUM_U32_SUBTRACTION_OPS)
            .map(|_| rng.gen::<u32>() as u64)
            .collect();
        let inputs_y = (0..NUM_U32_SUBTRACTION_OPS)
            .map(|_| rng.gen::<u32>() as u64)
            .collect();
        let borrows = (0..NUM_U32_SUBTRACTION_OPS)
            .map(|_| (rng.gen::<u32>() % 2) as u64)
            .collect();

        let gate = NonnativeAddGate::<F, D> {
            num_ops: NUM_U32_SUBTRACTION_OPS,
            _phantom: PhantomData,
        };

        let vars = EvaluationVars {
            local_constants: &[],
            local_wires: &get_wires(inputs_x, inputs_y, borrows),
            public_inputs_hash: &HashOut::rand(),
        };

        assert!(
            gate.eval_unfiltered(vars).iter().all(|x| x.is_zero()),
            "Gate constraints are not satisfied."
        );
    }
}
