use crate::field::extension::dodecic::DodecicExtension;
use crate::field::extension::quadratic::QuadraticExtension;
use crate::field::extension::sextic::SexticExtension;
use crate::gadgets::nonnative_fp2::{CircuitBuilderNonNativeExt2, NonNativeTargetExt2};
use crate::gadgets::nonnative_fp6::{CircuitBuilderNonNativeExt6, NonNativeTargetExt6};
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_field::extension::Extendable;
use plonky2_field::types::{Field, PrimeField};
use std::marker::PhantomData;

const CYCLOTOMIC_POW_LOOP: [u64; 4] = [4965661367192848881, 0, 0, 0];

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

    fn final_exponentiation_first_chunk<
        FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF>;

    fn final_exponentiation_last_chunk<
        FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF>;

    fn unitary_inverse_nonnative_ext12<
        FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF>;

    fn frobenius_map_nonnative_ext12<
        FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
        power: usize,
    ) -> NonNativeTargetExt12<FF>;

    fn frobenius_coeffs_c1_nonnative_ext12<
        FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
        power: usize,
    ) -> NonNativeTargetExt2<FF>;

    fn cyclotomic_pow_nonnative_ext12<
        FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF>;

    fn cyclotomic_squared_nonnative_ext12<
        FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF>;

    fn exp_by_neg_z_nonnative_ext12<
        FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
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
        let s1 = self.add_nonnative_ext2(&s1, &t3);
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

    fn final_exponentiation_first_chunk<
        FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF> {
        let b = self.inv_nonnative_ext12(x);
        let a = self.unitary_inverse_nonnative_ext12(x);
        let c = self.mul_nonnative_ext12(&a, &b);
        let d = self.frobenius_map_nonnative_ext12(&c, 2);
        return self.mul_nonnative_ext12(&d, &c);
    }

    fn final_exponentiation_last_chunk<
        FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF> {
        let a = self.exp_by_neg_z_nonnative_ext12(x);
        let b = self.cyclotomic_squared_nonnative_ext12(&a);
        let c = self.cyclotomic_squared_nonnative_ext12(&b);
        let d = self.mul_nonnative_ext12(&c, &b);

        let e = self.exp_by_neg_z_nonnative_ext12(&d);
        let f = self.cyclotomic_squared_nonnative_ext12(&e);
        let g = self.exp_by_neg_z_nonnative_ext12(&f);
        let h = self.unitary_inverse_nonnative_ext12(&d);
        let i = self.unitary_inverse_nonnative_ext12(&g);

        let j = self.mul_nonnative_ext12(&i, &e);
        let k = self.mul_nonnative_ext12(&j, &h);
        let l = self.mul_nonnative_ext12(&k, &b);
        let m = self.mul_nonnative_ext12(&k, &e);
        let n = self.mul_nonnative_ext12(x, &m);

        let o = self.frobenius_map_nonnative_ext12(&l, 1);
        let p = self.mul_nonnative_ext12(&o, &n);

        let q = self.frobenius_map_nonnative_ext12(&k, 2);
        let r = self.mul_nonnative_ext12(&q, &p);

        let s = self.unitary_inverse_nonnative_ext12(x);
        let t = self.mul_nonnative_ext12(&s, &l);
        let u = self.frobenius_map_nonnative_ext12(&t, 3);
        let v = self.mul_nonnative_ext12(&u, &r);

        v
    }

    fn unitary_inverse_nonnative_ext12<
        FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF> {
        NonNativeTargetExt12 {
            c0: x.c0.clone(),
            c1: self.neg_nonnative_ext6(&x.c1),
            _phantom: PhantomData,
        }
    }

    fn frobenius_map_nonnative_ext12<
        FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
        power: usize,
    ) -> NonNativeTargetExt12<FF> {
        let c0 = self.frobenius_map_nonnative_ext6(&x.c0, power);
        let mut c1 = self.frobenius_map_nonnative_ext6(&x.c1, power);
        let frobenius_coeffs_c1 = self.frobenius_coeffs_c1_nonnative_ext12::<FF>(power);
        c1 = self.scale_nonnative_ext6(&c1, &frobenius_coeffs_c1);

        NonNativeTargetExt12 {
            c0,
            c1,
            _phantom: PhantomData,
        }
    }

    fn frobenius_coeffs_c1_nonnative_ext12<
        FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
        power: usize,
    ) -> NonNativeTargetExt2<FF> {
        match power % 12 {
            0 => self.constant_nonnative_ext2(QuadraticExtension([FF::ONE, FF::ZERO])),
            1 => self.constant_nonnative_ext2(QuadraticExtension([
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT12_C1[0],
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT12_C1[1],
            ])),
            2 => self.constant_nonnative_ext2(QuadraticExtension([
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT12_C1[2],
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT12_C1[3],
            ])),
            3 => self.constant_nonnative_ext2(QuadraticExtension([
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT12_C1[4],
                <FF as Extendable<2>>::FROBENIUS_COEFFS_EXT12_C1[5],
            ])),
            _ => unreachable!(),
        }
    }

    fn cyclotomic_pow_nonnative_ext12<
        FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF> {
        let mut res = self.constant_nonnative_ext12(DodecicExtension::ONE);
        let mut found_one = false;

        for j in CYCLOTOMIC_POW_LOOP.iter().rev() {
            for i in (0..64).rev() {
                if found_one {
                    res = self.cyclotomic_squared_nonnative_ext12(&res);
                }

                if (j >> i) & 1 == 1 {
                    found_one = true;
                    res = self.mul_nonnative_ext12(&x, &res);
                }
            }
        }

        res
    }

    fn cyclotomic_squared_nonnative_ext12<
        FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF> {
        // let z0 = self.c0.c0;
        // let z4 = self.c0.c1;
        // let z3 = self.c0.c2;
        // let z2 = self.c1.c0;
        // let z1 = self.c1.c1;
        // let z5 = self.c1.c2;

        let mut z0 = x.c0.c0.clone();
        let mut z4 = x.c0.c1.clone();
        let mut z3 = x.c0.c2.clone();
        let mut z2 = x.c1.c0.clone();
        let mut z1 = x.c1.c1.clone();
        let mut z5 = x.c1.c2.clone();

        // let tmp = z0 * z1;
        // let t0 = (z0 + z1) * (z1.mul_by_nonresidue() + z0) - tmp - tmp.mul_by_nonresidue();
        // let t1 = tmp + tmp;
        let mut tmp = self.mul_nonnative_ext2(&z0, &z1);
        let mut tmp_mul_by_nonresidue = self.mul_by_nonresidue_nonnative_ext2(&tmp);
        let mut t0 = self.mul_by_nonresidue_nonnative_ext2(&z1);
        t0 = self.add_nonnative_ext2(&t0, &z0);
        let z0_add_z1 = self.add_nonnative_ext2(&z0, &z1);
        t0 = self.mul_nonnative_ext2(&t0, &z0_add_z1);
        t0 = self.sub_nonnative_ext2(&t0, &tmp);
        t0 = self.sub_nonnative_ext2(&t0, &tmp_mul_by_nonresidue);
        let mut t1 = self.add_nonnative_ext2(&tmp, &tmp);

        // let tmp = z2 * z3;
        // let t2 = (z2 + z3) * (z3.mul_by_nonresidue() + z2) - tmp - tmp.mul_by_nonresidue();
        // let t3 = tmp + tmp;
        tmp = self.mul_nonnative_ext2(&z2, &z3);
        tmp_mul_by_nonresidue = self.mul_by_nonresidue_nonnative_ext2(&tmp);
        let mut t2 = self.mul_by_nonresidue_nonnative_ext2(&z3);
        t2 = self.add_nonnative_ext2(&t2, &z2);
        let z2_add_z3 = self.add_nonnative_ext2(&z2, &z3);
        t2 = self.mul_nonnative_ext2(&t2, &z2_add_z3);
        t2 = self.sub_nonnative_ext2(&t2, &tmp);
        t2 = self.sub_nonnative_ext2(&t2, &tmp_mul_by_nonresidue);
        let mut t3 = self.add_nonnative_ext2(&tmp, &tmp);

        // let tmp = z4 * z5;
        // let t4 = (z4 + z5) * (z5.mul_by_nonresidue() + z4) - tmp - tmp.mul_by_nonresidue();
        // let t5 = tmp + tmp;
        tmp = self.mul_nonnative_ext2(&z4, &z5);
        tmp_mul_by_nonresidue = self.mul_by_nonresidue_nonnative_ext2(&tmp);
        let mut t4 = self.mul_by_nonresidue_nonnative_ext2(&z5);
        t4 = self.add_nonnative_ext2(&t4, &z4);
        let z4_add_z5 = self.add_nonnative_ext2(&z4, &z5);
        t4 = self.mul_nonnative_ext2(&t4, &z4_add_z5);
        t4 = self.sub_nonnative_ext2(&t4, &tmp);
        t4 = self.sub_nonnative_ext2(&t4, &tmp_mul_by_nonresidue);
        let mut t5 = self.add_nonnative_ext2(&tmp, &tmp);

        // let z0 = t0 - z0;
        // let z0 = z0 + z0;
        // let z0 = z0 + t0;
        //
        // let z1 = t1 + z1;
        // let z1 = z1 + z1;
        // let z1 = z1 + t1;
        z0 = self.sub_nonnative_ext2(&t0, &z0);
        z0 = self.add_nonnative_ext2(&z0, &z0);
        z0 = self.add_nonnative_ext2(&z0, &t0);
        z1 = self.add_nonnative_ext2(&t1, &z1);
        z1 = self.add_nonnative_ext2(&z1, &z1);
        z1 = self.add_nonnative_ext2(&z1, &t1);

        // let tmp = t5.mul_by_nonresidue();
        // let z2 = tmp + z2;
        // let z2 = z2 + z2;
        // let z2 = z2 + tmp;
        tmp = self.mul_by_nonresidue_nonnative_ext2(&t5);
        z2 = self.add_nonnative_ext2(&tmp, &z2);
        z2 = self.add_nonnative_ext2(&z2, &z2);
        z2 = self.add_nonnative_ext2(&z2, &tmp);

        // let z3 = t4 - z3;
        // let z3 = z3 + z3;
        // let z3 = z3 + t4;
        //
        // let z4 = t2 - z4;
        // let z4 = z4 + z4;
        // let z4 = z4 + t2;
        //
        // let z5 = t3 + z5;
        // let z5 = z5 + z5;
        // let z5 = z5 + t3;
        z3 = self.sub_nonnative_ext2(&t4, &z3);
        z3 = self.add_nonnative_ext2(&z3, &z3);
        z3 = self.add_nonnative_ext2(&z3, &t4);
        z4 = self.sub_nonnative_ext2(&t2, &z4);
        z4 = self.add_nonnative_ext2(&z4, &z4);
        z4 = self.add_nonnative_ext2(&z4, &t2);
        z5 = self.add_nonnative_ext2(&t3, &z5);
        z5 = self.add_nonnative_ext2(&z5, &z5);
        z5 = self.add_nonnative_ext2(&z5, &t3);

        NonNativeTargetExt12 {
            c0: NonNativeTargetExt6 {
                c0: z0,
                c1: z4,
                c2: z3,
                _phantom: PhantomData,
            },
            c1: NonNativeTargetExt6 {
                c0: z2,
                c1: z1,
                c2: z5,
                _phantom: PhantomData,
            },
            _phantom: PhantomData,
        }
    }

    fn exp_by_neg_z_nonnative_ext12<
        FF: PrimeField + Extendable<12> + Extendable<6> + Extendable<2>,
    >(
        &mut self,
        x: &NonNativeTargetExt12<FF>,
    ) -> NonNativeTargetExt12<FF> {
        let t = self.cyclotomic_pow_nonnative_ext12(&x);
        self.unitary_inverse_nonnative_ext12(&t)
    }
}

#[cfg(test)]
mod tests {
    use crate::field::bn128_base::Bn128Base;
    use crate::field::extension::dodecic::DodecicExtension;
    use crate::gadgets::nonnative_fp12::CircuitBuilderNonNativeExt12;
    use anyhow::Result;
    use log::LevelFilter;
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

    #[test]
    fn test_final_exponentiation_first_chunk() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext12(DodecicExtension::<Bn128Base>([
            Bn128Base([
                11214948798496262313,
                17041960038845619795,
                15038543693968526953,
                2854769455943088582,
            ]),
            Bn128Base([
                18358947165889346901,
                7594645203897246376,
                8678460969103022172,
                1920999953682168236,
            ]),
            Bn128Base([
                3822366764294320012,
                17097402614902894928,
                9428044024961402650,
                243602561756596672,
            ]),
            Bn128Base([
                17183959784901604854,
                8949372598380251153,
                6758521511101568679,
                3292122140014866630,
            ]),
            Bn128Base([
                18184120903008236488,
                754777629877848609,
                11021228852074755205,
                1907956694624918089,
            ]),
            Bn128Base([
                1027874041688341259,
                11521396577902036682,
                3591493198463547173,
                83019242339262093,
            ]),
            Bn128Base([
                3122839170227481532,
                12173517765924753901,
                5944764658757645540,
                3140853624433931065,
            ]),
            Bn128Base([
                8180994361383621561,
                7383210295740433637,
                16513349742730085408,
                3103130917377758986,
            ]),
            Bn128Base([
                10794403896041222214,
                926595914487050175,
                14036399402507339094,
                1776103223747386957,
            ]),
            Bn128Base([
                5805166188446473199,
                2737269020341603902,
                13491591132308782822,
                2420261513329173431,
            ]),
            Bn128Base([
                1062543480691384776,
                13315554019138159385,
                3588730779329066043,
                106141411247146151,
            ]),
            Bn128Base([
                8227730547903353994,
                9584719179116428424,
                11268238026684181373,
                1782281581539027984,
            ]),
        ]));
        let x_final_exp = builder.final_exponentiation_first_chunk(&x);

        let x_final_exp_expected =
            builder.constant_nonnative_ext12(DodecicExtension::<Bn128Base>([
                Bn128Base([
                    5043434446089285776,
                    10657533606529759381,
                    9152584192476601849,
                    863261167379340181,
                ]),
                Bn128Base([
                    1759854438208681881,
                    10094654885433073257,
                    10889272284263138169,
                    206742352424560226,
                ]),
                Bn128Base([
                    12238932165434206878,
                    452718107807392450,
                    3857971098306646129,
                    2613030368524641847,
                ]),
                Bn128Base([
                    319701665180357227,
                    16780665263894364593,
                    7227241905817552956,
                    1950574583009916137,
                ]),
                Bn128Base([
                    15637801825321601713,
                    8127946141092097176,
                    15152883888254822532,
                    674308714911400065,
                ]),
                Bn128Base([
                    3491857992057944970,
                    7544174498196655585,
                    5480627366048737444,
                    2759127147877780974,
                ]),
                Bn128Base([
                    7953389960191066797,
                    6608090703034079355,
                    12435011256579941993,
                    3317973050482146224,
                ]),
                Bn128Base([
                    18208874372440361022,
                    16672756784219067058,
                    11280915796095520360,
                    3251073394725726799,
                ]),
                Bn128Base([
                    2543162941034769838,
                    15580478473328230612,
                    15703823338471723517,
                    1671952983213063682,
                ]),
                Bn128Base([
                    10352949919205638184,
                    5317582320269278982,
                    1514888404229931376,
                    945684070290498550,
                ]),
                Bn128Base([
                    3331955989982546804,
                    13054065507425301176,
                    16966933150791074791,
                    1615565592860901151,
                ]),
                Bn128Base([
                    4235137809230761352,
                    8287660036747641836,
                    16044316575367099562,
                    1718719610590146095,
                ]),
            ]));
        builder.connect_nonnative_ext12(&x_final_exp, &x_final_exp_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_final_exponentiation_last_chunk() -> Result<()> {
        let mut builder = env_logger::Builder::from_default_env();
        builder.format_timestamp(None);
        builder.filter_level(LevelFilter::Info);
        builder.try_init()?;

        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative_ext12(DodecicExtension::<Bn128Base>([
            Bn128Base([
                5043434446089285776,
                10657533606529759381,
                9152584192476601849,
                863261167379340181,
            ]),
            Bn128Base([
                1759854438208681881,
                10094654885433073257,
                10889272284263138169,
                206742352424560226,
            ]),
            Bn128Base([
                12238932165434206878,
                452718107807392450,
                3857971098306646129,
                2613030368524641847,
            ]),
            Bn128Base([
                319701665180357227,
                16780665263894364593,
                7227241905817552956,
                1950574583009916137,
            ]),
            Bn128Base([
                15637801825321601713,
                8127946141092097176,
                15152883888254822532,
                674308714911400065,
            ]),
            Bn128Base([
                3491857992057944970,
                7544174498196655585,
                5480627366048737444,
                2759127147877780974,
            ]),
            Bn128Base([
                7953389960191066797,
                6608090703034079355,
                12435011256579941993,
                3317973050482146224,
            ]),
            Bn128Base([
                18208874372440361022,
                16672756784219067058,
                11280915796095520360,
                3251073394725726799,
            ]),
            Bn128Base([
                2543162941034769838,
                15580478473328230612,
                15703823338471723517,
                1671952983213063682,
            ]),
            Bn128Base([
                10352949919205638184,
                5317582320269278982,
                1514888404229931376,
                945684070290498550,
            ]),
            Bn128Base([
                3331955989982546804,
                13054065507425301176,
                16966933150791074791,
                1615565592860901151,
            ]),
            Bn128Base([
                4235137809230761352,
                8287660036747641836,
                16044316575367099562,
                1718719610590146095,
            ]),
        ]));
        let x_final_exp = builder.final_exponentiation_last_chunk(&x);

        let x_final_exp_expected =
            builder.constant_nonnative_ext12(DodecicExtension::<Bn128Base>([
                Bn128Base([
                    5261791323882946788,
                    5969279653909130133,
                    13914067258383528210,
                    94138518832923322,
                ]),
                Bn128Base([
                    16452828235560020136,
                    14277920321324140450,
                    1808868257472119675,
                    34528199959501362,
                ]),
                Bn128Base([
                    18153774717408091761,
                    4960813716655447740,
                    16877776237373176286,
                    111333703937892795,
                ]),
                Bn128Base([
                    6177369533740206595,
                    5540475544632735388,
                    18239293933561841014,
                    2106733616315301007,
                ]),
                Bn128Base([
                    12051797884938972865,
                    5452376490073186411,
                    13624941770027287332,
                    2556206152101805306,
                ]),
                Bn128Base([
                    12875218175083744969,
                    18411108459922848687,
                    16205159152680096724,
                    2298321485788462962,
                ]),
                Bn128Base([
                    14609934753813766369,
                    10831492163493656847,
                    9520417608604346386,
                    3185244767883521333,
                ]),
                Bn128Base([
                    1210469375740710922,
                    12695443078599703490,
                    15456619824566231090,
                    1318481115027774681,
                ]),
                Bn128Base([
                    12407907403893432531,
                    2577431929064026945,
                    13354667077106593055,
                    687277024136764940,
                ]),
                Bn128Base([
                    16854887897954252879,
                    12456401038131277336,
                    4434193903233473879,
                    1222410746383484321,
                ]),
                Bn128Base([
                    14754110002434578184,
                    3232557947137383979,
                    560992349178873120,
                    3162237541859216066,
                ]),
                Bn128Base([
                    4982245430574873546,
                    2614584005832853337,
                    14785904332481227781,
                    1602384300921012077,
                ]),
            ]));
        builder.connect_nonnative_ext12(&x_final_exp, &x_final_exp_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }
}
