use super::*;

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
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
                    let Some((min, max, modulus, signed)) = self
                        .integer_limits(dest_ty)
                        .or_else(|| self.integer_limits(lhs.ty))
                    else {
                        return;
                    };
                    let raw = match op {
                        BoundedArithmeticOp::SaturatingAdd => {
                            Int::add(self.z3_ctx, &[&lhs.z3_term, &rhs.z3_term])
                        }
                        BoundedArithmeticOp::SaturatingSub | BoundedArithmeticOp::WrappingSub => {
                            Int::sub(self.z3_ctx, &[&lhs.z3_term, &rhs.z3_term])
                        }
                    };
                    let term = match op {
                        BoundedArithmeticOp::SaturatingAdd | BoundedArithmeticOp::SaturatingSub => {
                            raw.lt(&min).ite(&min, &raw.gt(&max).ite(&max, &raw))
                        }
                        BoundedArithmeticOp::WrappingSub => {
                            let wrapped = raw.modulo(&modulus);
                            if signed {
                                wrapped
                                    .gt(&max)
                                    .ite(&Int::sub(self.z3_ctx, &[&wrapped, &modulus]), &wrapped)
                            } else {
                                wrapped
                            }
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
                    let term = match op {
                        OverflowOp::Add => Int::add(self.z3_ctx, &[&lhs.z3_term, &rhs.z3_term]),
                        OverflowOp::Sub => Int::sub(self.z3_ctx, &[&lhs.z3_term, &rhs.z3_term]),
                        OverflowOp::Mul => Int::mul(self.z3_ctx, &[&lhs.z3_term, &rhs.z3_term]),
                    };
                    self.set_field_value(dest, vec![0], VmValue::new(term, lhs.ty));
                }
            }
            CallEffect::ReturnNonZeroIff { arg } => {
                if let Some(a) = args.get(*arg) {
                    let dest_ty = self.body().local_decls[dest].ty;
                    let zero = Int::from_u64(self.z3_ctx, 0);
                    let term = self.fresh_int(&format!("ret_nz_iff_{}", dest.as_usize()));
                    self.constraints
                        .assertions
                        .push(term._eq(&zero)._eq(&a.z3_term._eq(&zero)));
                    self.set_local(dest, VmValue::new(term, dest_ty));
                }
            }
            CallEffect::ReturnLeadingZeros { arg } => {
                if let Some(value) = args.get(*arg) {
                    let width = self.size_of_ty(value.ty) * 8;
                    if width == 0
                        || width > 128
                        || !matches!(value.ty.kind(), TyKind::Uint(_) | TyKind::Int(_))
                    {
                        self.record_unsupported("ctlz operand type");
                    } else {
                        let zero = Int::from_u64(self.z3_ctx, 0);
                        let width_term = Int::from_u64(self.z3_ctx, width);
                        let one = Int::from_u64(self.z3_ctx, 1);
                        let two = Int::from_u64(self.z3_ctx, 2);
                        let high_bit = (1..width).fold(one.clone(), |acc, _| {
                            Int::mul(self.z3_ctx, &[&acc, &two]).simplify()
                        });
                        let term = self.fresh_int(&format!("ctlz_{}", dest.as_usize()));
                        self.constraints.assertions.push(term.ge(&zero));
                        self.constraints.assertions.push(term.le(&width_term));
                        self.constraints
                            .assertions
                            .push(value.z3_term._eq(&zero).implies(&term._eq(&width_term)));
                        self.constraints
                            .assertions
                            .push(value.z3_term.lt(&high_bit).implies(&term.ge(&one)));
                        self.constraints
                            .assertions
                            .push(value.z3_term.ge(&high_bit).implies(&term._eq(&zero)));
                        self.constraints
                            .assertions
                            .push(value.z3_term.lt(&zero).implies(&term._eq(&zero)));
                        let dest_ty = self.body().local_decls[dest].ty;
                        self.set_local(dest, VmValue::new(term, dest_ty));
                    }
                }
            }
            CallEffect::ReturnTrailingZeros { arg } => {
                if let Some(value) = args.get(*arg) {
                    let width = self.size_of_ty(value.ty) * 8;
                    if width == 0
                        || width > 128
                        || !matches!(value.ty.kind(), TyKind::Uint(_) | TyKind::Int(_))
                    {
                        self.record_unsupported("cttz operand type");
                    } else {
                        let zero = Int::from_u64(self.z3_ctx, 0);
                        let one = Int::from_u64(self.z3_ctx, 1);
                        let two = Int::from_u64(self.z3_ctx, 2);
                        let width_term = Int::from_u64(self.z3_ctx, width);
                        let term = self.fresh_int(&format!("cttz_{}", dest.as_usize()));
                        self.constraints.assertions.push(term.ge(&zero));
                        self.constraints.assertions.push(term.le(&width_term));
                        self.constraints
                            .assertions
                            .push(value.z3_term._eq(&zero).implies(&term._eq(&width_term)));
                        self.constraints.assertions.push(
                            value
                                .z3_term
                                .modulo(&two)
                                ._eq(&one)
                                .implies(&term._eq(&zero)),
                        );
                        self.constraints.assertions.push(
                            Bool::and(
                                self.z3_ctx,
                                &[
                                    &value.z3_term.modulo(&two)._eq(&zero),
                                    &value.z3_term._eq(&zero).not(),
                                ],
                            )
                            .implies(&term.ge(&one)),
                        );
                        let dest_ty = self.body().local_decls[dest].ty;
                        self.set_local(dest, VmValue::new(term, dest_ty));
                    }
                }
            }
            _ => unreachable!("non-numeric call effect"),
        }
    }
}
