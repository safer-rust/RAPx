use super::*;
use crate::vm::integer::{AddSubMul, overflowing_binary};
use z3::ast::BV;

impl<'z3, 'tcx> VmExecutor<'z3, 'tcx> {
    fn apply_binary_num(
        &mut self,
        dest: Local,
        args: &[VmValue<'z3, 'tcx>],
        lhs_arg: usize,
        rhs_arg: usize,
        f: impl Fn(&Int<'z3>, &Int<'z3>) -> Int<'z3>,
    ) {
        if let (Some(lhs), Some(rhs)) = (args.get(lhs_arg), args.get(rhs_arg)) {
            let dest_ty = self.body().local_decls[dest].ty;
            self.set_local(dest, VmValue::new(f(&lhs.z3_term, &rhs.z3_term), dest_ty));
        }
    }

    pub(super) fn apply_numeric_effect(
        &mut self,
        effect: &CallEffect,
        args: &[VmValue<'z3, 'tcx>],
        dest: Local,
    ) {
        match effect {
            CallEffect::ReturnMin { lhs_arg, rhs_arg } => {
                // Keep min as an `ite` so path conditions can simplify it
                // during later alignment and bounds checks.
                self.apply_binary_num(dest, args, *lhs_arg, *rhs_arg, |lhs, rhs| {
                    lhs.le(rhs).ite(lhs, rhs)
                });
            }
            CallEffect::ReturnMax { lhs_arg, rhs_arg } => {
                self.apply_binary_num(dest, args, *lhs_arg, *rhs_arg, |lhs, rhs| {
                    lhs.ge(rhs).ite(lhs, rhs)
                });
            }
            CallEffect::ReturnAdd { lhs_arg, rhs_arg } => {
                self.apply_binary_num(dest, args, *lhs_arg, *rhs_arg, |lhs, rhs| {
                    Int::add(self.z3_ctx, &[lhs, rhs])
                });
            }
            CallEffect::ReturnMul { lhs_arg, rhs_arg } => {
                self.apply_binary_num(dest, args, *lhs_arg, *rhs_arg, |lhs, rhs| {
                    Int::mul(self.z3_ctx, &[lhs, rhs])
                });
            }
            CallEffect::ReturnBoundedArithmetic {
                lhs_arg,
                rhs_arg,
                op,
            } => {
                if let (Some(lhs), Some(rhs)) = (args.get(*lhs_arg), args.get(*rhs_arg)) {
                    let dest_ty = self.body().local_decls[dest].ty;
                    let Some(layout) = self.integer_layout(dest_ty) else {
                        self.record_unsupported("bounded arithmetic result type");
                        return;
                    };
                    let raw = match op {
                        BoundedArithmeticOp::SaturatingAdd | BoundedArithmeticOp::WrappingAdd => {
                            Int::add(self.z3_ctx, &[&lhs.z3_term, &rhs.z3_term])
                        }
                        BoundedArithmeticOp::SaturatingSub | BoundedArithmeticOp::WrappingSub => {
                            Int::sub(self.z3_ctx, &[&lhs.z3_term, &rhs.z3_term])
                        }
                    };
                    let term = match op {
                        BoundedArithmeticOp::SaturatingAdd | BoundedArithmeticOp::SaturatingSub => {
                            let min = layout.min(self.z3_ctx);
                            let max = layout.max(self.z3_ctx);
                            raw.lt(&min).ite(&min, &raw.gt(&max).ite(&max, &raw))
                        }
                        BoundedArithmeticOp::WrappingAdd | BoundedArithmeticOp::WrappingSub => {
                            layout.normalize(self.z3_ctx, &raw)
                        }
                    };
                    self.set_local(dest, VmValue::new(term, dest_ty));
                }
            }
            CallEffect::ReturnWithOverflow {
                lhs_arg,
                rhs_arg,
                op,
            } => {
                if let (Some(lhs), Some(rhs)) = (args.get(*lhs_arg), args.get(*rhs_arg)) {
                    let dest_ty = self.body().local_decls[dest].ty;
                    let TyKind::Tuple(fields) = dest_ty.kind() else {
                        self.record_unsupported("overflow arithmetic result type");
                        return;
                    };
                    if fields.len() != 2
                        || fields[0] != lhs.ty
                        || fields[0] != rhs.ty
                        || fields[1] != self.tcx.types.bool
                    {
                        self.record_unsupported("overflow arithmetic tuple fields");
                        return;
                    }
                    let Some(layout) = self.integer_layout(fields[0]) else {
                        self.record_unsupported("overflow arithmetic operand type");
                        return;
                    };
                    let op = match op {
                        OverflowOp::Add => AddSubMul::Add,
                        OverflowOp::Sub => AddSubMul::Sub,
                        OverflowOp::Mul => AddSubMul::Mul,
                    };
                    let result =
                        overflowing_binary(self.z3_ctx, layout, op, &lhs.z3_term, &rhs.z3_term);

                    // Match ordinary tuple construction: the root is a fresh
                    // aggregate placeholder, and the scalar fields carry the
                    // numeric result. It has no pointer identity to propagate
                    // when the tuple is copied or moved.
                    self.ensure_local_allocation(dest);
                    let alloc_id = self.path_state.current_frame.local_alloc[&dest];
                    let mut root = VmValue::new(self.fresh_int("overflow_tuple"), dest_ty);
                    root.facts.init = true;
                    self.write_local_path(dest, Vec::new(), root);
                    let mut value = VmValue::new(result.value, fields[0]);
                    value.facts.init = true;
                    self.set_field_value(dest, vec![0], value);
                    let overflow_term = result.overflow.ite(
                        &Int::from_u64(self.z3_ctx, 1),
                        &Int::from_u64(self.z3_ctx, 0),
                    );
                    let mut overflow = VmValue::new(overflow_term, fields[1]);
                    overflow.facts.init = true;
                    self.set_field_value(dest, vec![1], overflow);
                    self.content_mut(alloc_id).facts.initialized = true;
                }
            }
            CallEffect::ReturnNonZeroIff { arg } => {
                if let Some(a) = args.get(*arg) {
                    let dest_ty = self.body().local_decls[dest].ty;
                    let zero = Int::from_u64(self.z3_ctx, 0);
                    let term = self.fresh_int(&format!("ret_nz_iff_{}", dest.as_usize()));
                    self.path_state.constraints
                        .assertions
                        .push(term._eq(&zero)._eq(&a.z3_term._eq(&zero)));
                    self.set_local(dest, VmValue::new(term, dest_ty));
                }
            }
            CallEffect::ReturnLeadingZeros { arg } | CallEffect::ReturnTrailingZeros { arg } => {
                if let Some(value) = args.get(*arg) {
                    let Some(layout) = self.integer_layout(value.ty) else {
                        self.record_unsupported("zero count operand type");
                        return;
                    };
                    let width = u32::from(layout.bits);
                    let bits = BV::from_int(&value.z3_term, width);
                    let bit_one = BV::from_u64(self.z3_ctx, 1, 1);
                    let leading = matches!(effect, CallEffect::ReturnLeadingZeros { .. });
                    let mut term = Int::from_u64(self.z3_ctx, u64::from(width));
                    // Interpret signed values by their width-bit representation.
                    // The last set bit visited determines the exact count; an
                    // all-zero operand retains the full width.
                    for index in 0..width {
                        let bit = if leading { index } else { width - index - 1 };
                        let count = if leading { width - bit - 1 } else { bit };
                        term = bits
                            .extract(bit, bit)
                            ._eq(&bit_one)
                            .ite(&Int::from_u64(self.z3_ctx, u64::from(count)), &term);
                    }
                    let dest_ty = self.body().local_decls[dest].ty;
                    self.set_local(dest, VmValue::new(term.simplify(), dest_ty));
                }
            }
            _ => unreachable!("non-numeric call effect"),
        }
    }
}
