use core::marker::PhantomData;
use num::{BigUint, FromPrimitive, ToPrimitive};

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

/// A gate to perform conversion of a 256-bit number in 8 u32 limbs to 10 u28 limbs.
#[derive(Copy, Clone, Debug)]
pub struct U32ToU28Gate<F: RichField + Extendable<D>, const D: usize> {
    pub num_ops: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> U32ToU28Gate<F, D> {
    pub fn new_from_config(config: &CircuitConfig) -> Self {
        Self {
            num_ops: Self::num_ops(config),
            _phantom: PhantomData,
        }
    }

    pub(crate) fn num_ops(config: &CircuitConfig) -> usize {
        let wires_per_op = 146;
        let routed_wires_per_op = 18;
        (config.num_wires / wires_per_op).min(config.num_routed_wires / routed_wires_per_op)
    }

    pub fn wire_ith_input(&self, i: usize, j: usize) -> usize {
        debug_assert!(i < self.num_ops);
        debug_assert!(j < 8);
        18 * i + j
    }
    pub fn wire_ith_output_result(&self, i: usize, j: usize) -> usize {
        debug_assert!(i < self.num_ops);
        debug_assert!(j < 10);
        18 * i + 8 + j
    }
    pub fn wire_ith_output_jth_limb_kth_limb(&self, i: usize, j: usize, k: usize) -> usize {
        debug_assert!(i < self.num_ops);
        debug_assert!(j < 10);
        debug_assert!(k < 14);
        debug_assert!(j != 9 || k < 2);
        18 * self.num_ops + 128 * i + 14 * j + k
    }
    pub fn wire_ith_input_jth_limb_kth_limb(&self, i: usize, j: usize, k: usize) -> usize {
        debug_assert!(i < self.num_ops);
        debug_assert!(j < 8);
        debug_assert!(k < 16);
        18 * self.num_ops + 128 * i + 16 * j + k
    }

    pub fn limb_bits() -> usize {
        2
    }
    // We have 14 2-bit limbs for a 28-bit limb.
    pub fn num_limbs() -> usize {
        28 / Self::limb_bits()
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for U32ToU28Gate<F, D> {
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
            let mut input = vec![F::Extension::ZERO; 8];
            let mut output_result = vec![F::Extension::ZERO; 10];

            for j in 0..8 {
                input[j] = vars.local_wires[self.wire_ith_input(i, j)];
            }

            for j in 0..10 {
                output_result[j] = vars.local_wires[self.wire_ith_output_result(i, j)];
            }

            // Range-check output_result to be at most 28 bits.
            for j in 0..10 {
                let mut combined_limbs = F::Extension::ZERO;
                let limb_base = F::Extension::from_canonical_u64(1u64 << Self::limb_bits());
                let num_limbs = if j == 9 { 2 } else { Self::num_limbs() };
                for k in (0..num_limbs).rev() {
                    let this_limb =
                        vars.local_wires[self.wire_ith_output_jth_limb_kth_limb(i, j, k)];
                    let max_limb = 1 << Self::limb_bits();
                    let product = (0..max_limb)
                        .map(|x| this_limb - F::Extension::from_canonical_usize(x))
                        .product();
                    constraints.push(product);

                    combined_limbs = limb_base * combined_limbs + this_limb;
                }
                constraints.push(combined_limbs - output_result[j]);
            }

            // Check input can be reconstructed from these limbs.
            for j in 0..8 {
                let mut combined_limbs = F::Extension::ZERO;
                let limb_base = F::Extension::from_canonical_u64(1u64 << Self::limb_bits());
                let num_limbs = 16;
                for k in (0..num_limbs).rev() {
                    let this_limb =
                        vars.local_wires[self.wire_ith_input_jth_limb_kth_limb(i, j, k)];
                    combined_limbs = limb_base * combined_limbs + this_limb;
                }
                constraints.push(combined_limbs - input[j]);
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
                    U32ToU28Generator {
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
        146
    }

    fn num_constants(&self) -> usize {
        0
    }

    fn degree(&self) -> usize {
        1 << Self::limb_bits()
    }

    fn num_constraints(&self) -> usize {
        self.num_ops * (18 + 128)
    }
}

impl<F: RichField + Extendable<D>, const D: usize> PackedEvaluableBase<F, D>
    for U32ToU28Gate<F, D>
{
    fn eval_unfiltered_base_packed<P: PackedField<Scalar = F>>(
        &self,
        vars: EvaluationVarsBasePacked<P>,
        mut yield_constr: StridedConstraintConsumer<P>,
    ) {
        for i in 0..self.num_ops {
            let mut input = vec![P::ZEROS; 8];
            for j in 0..8 {
                input[j] = vars.local_wires[self.wire_ith_input(i, j)];
            }

            let mut output_result = vec![P::ZEROS; 8];
            for j in 0..8 {
                output_result[j] = vars.local_wires[self.wire_ith_output_result(i, j)];
            }

            // Range-check output_result to be at most 28 bits.
            for j in 0..10 {
                let mut combined_limbs = P::ZEROS;
                let limb_base = F::from_canonical_u64(1u64 << Self::limb_bits());
                let num_limbs = if j == 9 { 2 } else { Self::num_limbs() };
                for k in (0..num_limbs).rev() {
                    let this_limb =
                        vars.local_wires[self.wire_ith_output_jth_limb_kth_limb(i, j, k)];
                    let max_limb = 1 << Self::limb_bits();
                    let product = (0..max_limb)
                        .map(|x| this_limb - F::from_canonical_usize(x))
                        .product();
                    yield_constr.one(product);

                    combined_limbs = combined_limbs * limb_base.clone() + this_limb;
                }
                yield_constr.one(combined_limbs - output_result[j]);
            }

            // Range-check output_result to be at most 28 bits.
            for j in 0..8 {
                let mut combined_limbs = P::ZEROS;
                let limb_base = F::from_canonical_u64(1u64 << Self::limb_bits());
                let num_limbs = 16;
                for k in (0..num_limbs).rev() {
                    let this_limb =
                        vars.local_wires[self.wire_ith_input_jth_limb_kth_limb(i, j, k)];
                    combined_limbs = combined_limbs * limb_base.clone() + this_limb;
                }
                yield_constr.one(combined_limbs - input[j]);
            }
        }
    }
}

#[derive(Clone, Debug)]
struct U32ToU28Generator<F: RichField + Extendable<D>, const D: usize> {
    gate: U32ToU28Gate<F, D>,
    row: usize,
    i: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F> for U32ToU28Generator<F, D> {
    fn dependencies(&self) -> Vec<Target> {
        let local_target = |column| Target::wire(self.row, column);

        let range: Vec<_> = (0..8)
            .map(|i| local_target(self.gate.wire_ith_input(self.i, i)))
            .collect();

        range
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let local_wire = |column| Wire {
            row: self.row,
            column,
        };

        let get_local_wire = |column| witness.get_wire(local_wire(column));

        let mut input = vec![F::ZERO; 8];
        let mut input_u32s = vec![0u32; 8];
        for j in 0..8 {
            input[j] = get_local_wire(self.gate.wire_ith_input(self.i, j));
            input_u32s[j] = input[j].to_canonical_u64() as u32;
        }

        let input_biguint = BigUint::from_slice(&input_u32s);

        for j in 0..10 {
            let this_limb: BigUint =
                (input_biguint.clone() >> (j * 28)) & BigUint::from_u32(0xfffffff).unwrap();
            let output_result = F::from_canonical_u32(this_limb.to_u32().unwrap());
            out_buffer.set_wire(
                local_wire(self.gate.wire_ith_output_result(self.i, j)),
                output_result.clone(),
            );
        }

        for j in 0..8 {
            let num_limbs = 16;
            let limb_base = 1 << U32ToU28Gate::<F, D>::limb_bits();
            let output_limbs: Vec<_> = (0..num_limbs)
                .scan(input_u32s[j] as u64, |acc, _| {
                    let tmp = *acc % limb_base;
                    *acc /= limb_base;
                    Some(F::from_canonical_u64(tmp))
                })
                .collect();

            for k in 0..num_limbs {
                let wire = local_wire(self.gate.wire_ith_input_jth_limb_kth_limb(self.i, j, k));
                out_buffer.set_wire(wire, output_limbs[k].clone());
            }
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
        test_low_degree::<GoldilocksField, _, 4>(U32ToU28Gate::<GoldilocksField, 4> {
            num_ops: 1,
            _phantom: PhantomData,
        })
    }
}
