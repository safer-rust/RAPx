use super::*;

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(super) fn apply_simd_effect(
        &mut self,
        effect: &CallEffect,
        args: &[VmValue<'z3, 'tcx>],
        caller_arg_locals: &[Option<Local>],
        dest: Local,
    ) {
        match effect {
            CallEffect::SimdCompare {
                lhs_arg,
                rhs_arg,
                op,
            } => {
                let dest_ty = self.body().local_decls[dest].ty;
                let Some((elem_ty, len)) = self.simd_lane_type(dest_ty) else {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                };
                let Some((lhs_local, rhs_local)) = caller_arg_locals
                    .get(*lhs_arg)
                    .copied()
                    .flatten()
                    .zip(caller_arg_locals.get(*rhs_arg).copied().flatten())
                else {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                };
                let Some((lhs, rhs)) = args.get(*lhs_arg).zip(args.get(*rhs_arg)) else {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                };
                let Some((input_ty, input_len)) = self.simd_lane_type(lhs.ty) else {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                };
                if input_len != len
                    || rhs.ty != lhs.ty
                    || !matches!(input_ty.kind(), TyKind::Int(_) | TyKind::Uint(_))
                {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                }
                let lanes: Option<Vec<_>> = (0..len)
                    .map(|index| {
                        let left = self.field_value(lhs_local, &[0, index])?.z3_term.clone();
                        let right = self.field_value(rhs_local, &[0, index])?.z3_term.clone();
                        let condition = match op {
                            SimdCmpOp::Eq => left._eq(&right),
                            SimdCmpOp::Ne => left._eq(&right).not(),
                            SimdCmpOp::Lt => left.lt(&right),
                            SimdCmpOp::Le => left.le(&right),
                            SimdCmpOp::Gt => left.gt(&right),
                            SimdCmpOp::Ge => left.ge(&right),
                        };
                        Some(condition)
                    })
                    .collect();
                let Some(lanes) = lanes else {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                };
                let true_value = if matches!(elem_ty.kind(), TyKind::Int(_)) {
                    Int::from_i64(self.z3_ctx, -1)
                } else if let Some((_, max, _, _)) = self.integer_limits(elem_ty) {
                    max
                } else {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                };
                let zero = Int::from_u64(self.z3_ctx, 0);
                for (index, condition) in lanes.into_iter().enumerate() {
                    let mut value = VmValue::new(condition.ite(&true_value, &zero), elem_ty);
                    value.facts.init = true;
                    self.set_field_value(dest, vec![0, index], value);
                }
            }
            CallEffect::SimdArithmetic {
                lhs_arg,
                rhs_arg,
                op,
            } => {
                let dest_ty = self.body().local_decls[dest].ty;
                let Some((elem_ty, len)) = self.simd_lane_type(dest_ty) else {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                };
                let Some((min, max, modulus, signed)) = self.integer_limits(elem_ty) else {
                    self.set_opaque_simd_result(dest);
                    return;
                };
                let Some((lhs_local, rhs_local)) = caller_arg_locals
                    .get(*lhs_arg)
                    .copied()
                    .flatten()
                    .zip(caller_arg_locals.get(*rhs_arg).copied().flatten())
                else {
                    self.set_opaque_simd_result(dest);
                    return;
                };
                if args.get(*lhs_arg).is_none_or(|value| value.ty != dest_ty)
                    || args.get(*rhs_arg).is_none_or(|value| value.ty != dest_ty)
                {
                    self.set_opaque_simd_result(dest);
                    return;
                }
                let lanes: Option<Vec<_>> = (0..len)
                    .map(|index| {
                        let left = self.field_value(lhs_local, &[0, index])?.z3_term.clone();
                        let right = self.field_value(rhs_local, &[0, index])?.z3_term.clone();
                        let raw = match op {
                            SimdArithOp::Add | SimdArithOp::SaturatingAdd => {
                                Int::add(self.z3_ctx, &[&left, &right])
                            }
                            SimdArithOp::Sub | SimdArithOp::SaturatingSub => {
                                Int::sub(self.z3_ctx, &[&left, &right])
                            }
                            SimdArithOp::Mul => Int::mul(self.z3_ctx, &[&left, &right]),
                        };
                        let term = match op {
                            SimdArithOp::SaturatingAdd | SimdArithOp::SaturatingSub => {
                                raw.lt(&min).ite(&min, &raw.gt(&max).ite(&max, &raw))
                            }
                            _ => {
                                let wrapped = raw.modulo(&modulus);
                                if signed {
                                    wrapped.gt(&max).ite(
                                        &Int::sub(self.z3_ctx, &[&wrapped, &modulus]),
                                        &wrapped,
                                    )
                                } else {
                                    wrapped
                                }
                            }
                        };
                        Some(term)
                    })
                    .collect();
                let Some(lanes) = lanes else {
                    self.set_opaque_simd_result(dest);
                    return;
                };
                for (index, term) in lanes.into_iter().enumerate() {
                    let mut value = VmValue::new(term, elem_ty);
                    value.facts.init = true;
                    self.set_field_value(dest, vec![0, index], value);
                }
            }
            CallEffect::SimdOpaque => self.set_opaque_simd_result(dest),
            CallEffect::SimdSplat { arg } => {
                let dest_ty = self.body().local_decls[dest].ty;
                let Some((elem_ty, len)) = self.simd_lane_type(dest_ty) else {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                };
                let Some(input) = args.get(*arg) else {
                    self.set_opaque_simd_result(dest);
                    return;
                };
                for index in 0..len {
                    let mut value = input.clone();
                    value.ty = elem_ty;
                    self.set_field_value(dest, vec![0, index], value);
                }
            }
            CallEffect::SimdExtract {
                vector_arg,
                index_arg,
            } => {
                let Some((local, index)) =
                    caller_arg_locals.get(*vector_arg).copied().flatten().zip(
                        args.get(*index_arg)
                            .and_then(|value| value.z3_term.simplify().as_u64()),
                    )
                else {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                };
                let Some((_, len)) = args
                    .get(*vector_arg)
                    .and_then(|value| self.simd_lane_type(value.ty))
                else {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                };
                if index >= len as u64 {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                }
                if let Some(mut value) = self.field_value(local, &[0, index as usize]).cloned() {
                    value.ty = self.body().local_decls[dest].ty;
                    self.set_local(dest, value);
                } else {
                    self.set_opaque_intrinsic_result(dest);
                }
            }
            CallEffect::SimdInsert {
                vector_arg,
                index_arg,
                value_arg,
            } => {
                let dest_ty = self.body().local_decls[dest].ty;
                let Some((elem_ty, len)) = self.simd_lane_type(dest_ty) else {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                };
                let Some((local, index, replacement)) = caller_arg_locals
                    .get(*vector_arg)
                    .copied()
                    .flatten()
                    .zip(
                        args.get(*index_arg)
                            .and_then(|value| value.z3_term.simplify().as_u64()),
                    )
                    .zip(args.get(*value_arg))
                    .map(|((local, index), value)| (local, index, value.clone()))
                else {
                    self.set_opaque_simd_result(dest);
                    return;
                };
                if index >= len as u64 {
                    self.set_opaque_simd_result(dest);
                    return;
                }
                let lanes: Option<Vec<_>> = (0..len)
                    .map(|lane| {
                        if lane == index as usize {
                            let mut value = replacement.clone();
                            value.ty = elem_ty;
                            Some(value)
                        } else {
                            self.field_value(local, &[0, lane]).cloned()
                        }
                    })
                    .collect();
                let Some(lanes) = lanes else {
                    self.set_opaque_simd_result(dest);
                    return;
                };
                for (lane, value) in lanes.into_iter().enumerate() {
                    self.set_field_value(dest, vec![0, lane], value);
                }
            }
            CallEffect::SimdHavocMemory { mask_arg, .. } => {
                let mask_is_zero = caller_arg_locals
                    .get(*mask_arg)
                    .copied()
                    .flatten()
                    .zip(
                        args.get(*mask_arg)
                            .and_then(|value| self.simd_lane_type(value.ty)),
                    )
                    .is_some_and(|(local, (_, len))| {
                        (0..len).all(|lane| {
                            self.field_value(local, &[0, lane])
                                .and_then(|value| value.z3_term.simplify().as_u64())
                                == Some(0)
                        })
                    });
                if !mask_is_zero {
                    for index in 0..self.units.len() {
                        self.forget_memory_values(AllocId(index));
                    }
                }
            }
            CallEffect::SimdMaskedFallback {
                mask_arg,
                fallback_arg,
            } => {
                let mask_is_zero = caller_arg_locals
                    .get(*mask_arg)
                    .copied()
                    .flatten()
                    .zip(
                        args.get(*mask_arg)
                            .and_then(|value| self.simd_lane_type(value.ty)),
                    )
                    .is_some_and(|(local, (_, len))| {
                        (0..len).all(|lane| {
                            self.field_value(local, &[0, lane])
                                .and_then(|value| value.z3_term.simplify().as_u64())
                                == Some(0)
                        })
                    });
                let copied = mask_is_zero
                    && caller_arg_locals
                        .get(*fallback_arg)
                        .copied()
                        .flatten()
                        .is_some_and(|local| self.copy_simd_result_from_local(dest, local));
                if !copied {
                    self.set_opaque_simd_result(dest);
                }
            }
            CallEffect::SimdBitmask { arg } => {
                let Some(local) = caller_arg_locals.get(*arg).copied().flatten() else {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                };
                let Some((_, len)) = args
                    .get(*arg)
                    .and_then(|value| self.simd_lane_type(value.ty))
                else {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                };
                if len == 0
                    || len > 64
                    || !matches!(self.body().local_decls[dest].ty.kind(), TyKind::Uint(_))
                {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                }
                let lanes: Option<Vec<_>> = (0..len)
                    .map(|index| {
                        self.field_value(local, &[0, index])
                            .map(|value| value.z3_term.clone())
                    })
                    .collect();
                let Some(lanes) = lanes else {
                    self.set_opaque_intrinsic_result(dest);
                    return;
                };
                let zero = Int::from_u64(self.z3_ctx, 0);
                let mut mask = zero.clone();
                for (index, lane) in lanes.into_iter().enumerate() {
                    let bit = if self.tcx.data_layout.endian == rustc_abi::Endian::Little {
                        index
                    } else {
                        len - 1 - index
                    };
                    let weight = Int::from_u64(self.z3_ctx, 1_u64 << bit);
                    mask = Int::add(
                        self.z3_ctx,
                        &[&mask, &lane._eq(&zero).not().ite(&weight, &zero)],
                    );
                }
                let dest_ty = self.body().local_decls[dest].ty;
                self.set_local(dest, VmValue::new(mask, dest_ty));
            }
            _ => unreachable!("non-SIMD call effect"),
        }
    }
}
