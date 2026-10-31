//! Apply modeled call effects to symbolic state.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Local, Operand};
use rustc_middle::ty::{Ty, TyKind};
use z3::ast::{Ast, Bool, Int};

use super::state::{
    AllocId, ElementTy, Provenance, ValueFacts, ValueSource, VmState,
    VmValue,
};
use crate::helpers::mir_utils;
use crate::verify::api_classify;
use crate::verify::call_summary::{BoundedArithmeticOp, CallEffect, OverflowOp};

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// Abstract a safe `Fn*` call when only a scalar boolean or `Ordering`
    /// result is required. The closure body is unavailable at a generic call
    /// site, so every allocation outside the active frame may have been
    /// reached through captures or globals. Locals explicitly passed by
    /// reference are also invalidated. Frame-private counters remain stable.
    pub(crate) fn apply_callback_effect(
        &mut self,
        args: &[VmValue<'z3, 'tcx>],
        caller_arg_locals: &[Option<Local>],
        dest: Local,
        callee: DefId,
    ) {
        let ty = self.body().local_decls[dest].ty;
        if !crate::verify::call_summary::callback::supports_result(ty) {
            self.record_missing_mir(callee);
            return;
        }
        let input_receiver = caller_arg_locals
            .first()
            .copied()
            .flatten()
            .is_some_and(|local| local.as_usize() <= self.body().arg_count)
            || args
                .first()
                .and_then(VmValue::provenance_alloc_id)
                .is_some_and(|id| {
                    (1..=self.body().arg_count).any(|index| {
                        self.current_frame
                            .local_alloc
                            .get(&Local::from_usize(index))
                            == Some(&id)
                    })
                });
        if !input_receiver {
            self.record_missing_mir(callee);
            return;
        }
        // The rust-call tuple may carry references to this frame's locals.
        // Require provenance for every reference field before keeping those
        // locals private. An opaque aggregate can hide such a reference.
        for (index, arg) in args.iter().enumerate().skip(1) {
            let resolved = match arg.ty.kind() {
                TyKind::Ref(..) | TyKind::RawPtr(..) => arg.provenance.is_some(),
                TyKind::Tuple(fields) => fields.iter().enumerate().all(|(field, ty)| {
                    match ty.kind() {
                        TyKind::Ref(..) | TyKind::RawPtr(..) => caller_arg_locals
                            .get(index)
                            .copied()
                            .flatten()
                            .and_then(|local| self.current_frame.local_alloc.get(&local))
                            .and_then(|id| self.load_value(*id, arg.ty, &[field]))
                            .and_then(VmValue::provenance_alloc_id)
                            .is_some(),
                        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_)
                        | TyKind::Float(_) | TyKind::Never => true,
                        _ => false,
                    }
                }),
                _ => false,
            };
            if !resolved {
                self.record_missing_mir(callee);
                return;
            }
        }

        let private: Vec<_> = self.current_frame.local_alloc.values().copied().collect();
        let borrowed: Vec<_> = self
            .current_frame
            .local_alloc
            .iter()
            .filter_map(|(local, id)| {
                (matches!(self.body().local_decls[*local].ty.kind(), TyKind::Ref(..))
                    && !self.alloc(*id).facts.dead)
                    .then(|| self.local_value(*local))
                    .flatten()
                    .and_then(VmValue::provenance_alloc_id)
                    .map(|id| self.root_alloc(id))
            })
            .collect();
        let mut affected: Vec<_> = (0..self.units.len())
            .map(AllocId)
            .filter(|id| !private.contains(id))
            .collect();
        affected.extend(args.iter().filter_map(VmValue::provenance_alloc_id));
        for local in caller_arg_locals.iter().flatten() {
            if let Some(id) = self.current_frame.local_alloc.get(local) {
                affected.extend(
                    self.content(*id)
                        .values
                        .values()
                        .filter_map(VmValue::provenance_alloc_id),
                );
            }
        }
        affected = affected.into_iter().map(|id| self.root_alloc(id)).collect();
        affected.sort_by_key(|id| id.0);
        affected.dedup();
        for id in affected {
            if !borrowed.contains(&id) {
                self.callback_may_drop.insert(id);
            }
            self.forget_memory_values(id);
            for alias in 0..self.units.len() {
                let alias = AllocId(alias);
                if self.root_alloc(alias) == id {
                    let facts = &mut self.alloc_mut(alias).facts;
                    facts.owning = None;
                    if !borrowed.contains(&id) {
                        facts.liveness = None;
                    }
                }
            }
        }

        let term = self.fresh_int("callback_result");
        if matches!(ty.kind(), TyKind::Bool) {
            let zero = Int::from_u64(self.z3_ctx, 0);
            let one = Int::from_u64(self.z3_ctx, 1);
            self.constraints.assertions.push(term.ge(&zero));
            self.constraints.assertions.push(term.le(&one));
        }
        let mut result = VmValue::new(term, ty);
        result.facts.init = true;
        self.set_local(dest, result);
    }

    /// Apply a single call effect to the VM state.
    pub(crate) fn apply_call_effect(
        &mut self,
        effect: &CallEffect,
        args: &[VmValue<'z3, 'tcx>],
        caller_arg_locals: &[Option<Local>],
        dest: Local,
        callee: Option<DefId>,
        func: &Operand<'tcx>,
    ) {
        match effect {
            CallEffect::ReturnUninitWrapper => {
                self.ensure_local_allocation(dest);
                if let Some(&id) = self.current_frame.local_alloc.get(&dest) {
                    self.content_mut(id).facts.inner_uninit = true;
                }
            }
            CallEffect::ReturnLayoutSymbolic { is_size } => {
                let ty = mir_utils::fn_def_first_type_arg(func)
                    .expect("layout effect built from a FnDef");
                let term = if *is_size {
                    self.size_sym(ty)
                } else {
                    self.align_sym(ty)
                };
                let dest_ty = self.body().local_decls[dest].ty;
                self.set_local(dest, VmValue::new(term, dest_ty));
            }
            CallEffect::ReturnAliasArg { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    self.set_dest_as_heap_ptr(arg_val, dest);
                }
            }
            CallEffect::ReturnArgValue { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    let mut val = arg_val.clone();
                    val.ty = self.body().local_decls[dest].ty;
                    val.facts.init = true;
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnOpaque => {
                self.set_opaque_intrinsic_result(dest);
            }
            CallEffect::ReturnSizeOfVal { arg } => {
                let size = args.get(*arg).and_then(|value| {
                    let pointee = mir_utils::pointee_ty(value.ty)?;
                    match pointee.kind() {
                        TyKind::Slice(elem) => {
                            let len = self.slice_len_from_value(value)?;
                            Some(Int::mul(self.z3_ctx, &[&len, &self.size_sym(*elem)]))
                        }
                        TyKind::Dynamic(..) => None,
                        _ => Some(self.size_sym(pointee)),
                    }
                });
                if let Some(size) = size {
                    let ty = self.body().local_decls[dest].ty;
                    self.set_local(dest, VmValue::new(size, ty));
                } else {
                    self.set_opaque_intrinsic_result(dest);
                }
            }
            CallEffect::ReturnRawEq {
                left_arg,
                right_arg,
            } => {
                let ty = self.body().local_decls[dest].ty;
                let Some((left, right)) = args.get(*left_arg).zip(args.get(*right_arg)) else {
                    self.unsupported_mir = true;
                    return;
                };
                if left.z3_term == right.z3_term && left.ty == right.ty {
                    self.set_local(dest, VmValue::new(Int::from_u64(self.z3_ctx, 1), ty));
                } else if let Some((left_local, right_local)) = self
                    .find_local_by_address(&left.z3_term)
                    .zip(self.find_local_by_address(&right.z3_term))
                    .filter(|(left_local, right_local)| {
                        let left_ty = self.body().local_decls[*left_local].ty;
                        left_ty == self.body().local_decls[*right_local].ty
                            && matches!(left_ty.kind(), TyKind::Int(_) | TyKind::Uint(_))
                    })
                    && let Some((left_value, right_value)) = self
                        .local_value(left_local)
                        .zip(self.local_value(right_local))
                {
                    let one = Int::from_u64(self.z3_ctx, 1);
                    let zero = Int::from_u64(self.z3_ctx, 0);
                    let term = left_value
                        .z3_term
                        ._eq(&right_value.z3_term)
                        .ite(&one, &zero);
                    self.set_local(dest, VmValue::new(term, ty));
                } else {
                    let term = self.fresh_int("raw_eq_result");
                    self.inline.opaque_intrinsic_terms.insert(term.clone());
                    self.set_local(dest, VmValue::new(term, ty));
                }
            }
            CallEffect::ReturnExactDiv { lhs_arg, rhs_arg } => {
                let ty = self.body().local_decls[dest].ty;
                let Some((lhs, rhs)) = args.get(*lhs_arg).zip(args.get(*rhs_arg)) else {
                    self.unsupported_mir = true;
                    return;
                };
                if !matches!(ty.kind(), TyKind::Uint(_)) {
                    self.unsupported_mir = true;
                    return;
                }
                self.set_local(dest, VmValue::new(lhs.z3_term.div(&rhs.z3_term), ty));
            }
            CallEffect::SelectUnpredictable => {
                if args.len() >= 3 {
                    let term = self.fresh_int(&format!("selunpred_{}", dest.as_usize()));
                    let dest_ty = self.body().local_decls[dest].ty;
                    let eq1 = term._eq(&args[1].z3_term);
                    let eq2 = term._eq(&args[2].z3_term);
                    self.constraints
                        .assertions
                        .push(Bool::or(self.z3_ctx, &[&eq1, &eq2]));
                    let prov = args[1]
                        .provenance
                        .clone()
                        .or_else(|| args[2].provenance.clone());
                    self.set_local(
                        dest,
                        VmValue {
                            z3_term: term,
                            ty: dest_ty,
                            provenance: prov,
                            facts: ValueFacts::default(),
                            source: ValueSource::None,
                        },
                    );
                }
            }
            CallEffect::ReturnTransparentDeref { arg, peel } => {
                if let Some(arg_val) = args.get(*arg) {
                    self.set_dest_as_heap_ptr(arg_val, dest);
                    if let Some(arg_local) = caller_arg_locals.get(*arg).copied().flatten() {
                        let keys: Vec<Vec<usize>> = self.field_paths(arg_local);
                        for path in keys {
                            if path.len() > *peel
                                && path[..*peel].iter().all(|&f| f == 0)
                                && let Some(v) = self.field_value(arg_local, &path).cloned()
                            {
                                self.set_field_value(dest, path[*peel..].to_vec(), v);
                            }
                        }
                    }
                }
            }
            CallEffect::ReturnWrappingPointerOffset {
                base_arg,
                offset_arg,
            } => {
                if let (Some(base), Some(offset)) = (args.get(*base_arg), args.get(*offset_arg)) {
                    let stride = mir_utils::pointee_ty(base.ty).and_then(|pointee| {
                        let (_, size) = mir_utils::type_layout(
                            self.tcx,
                            self.current_frame.current_def_id,
                            pointee,
                        )?;
                        if size == 0 && mir_utils::ty_has_type_param(pointee) {
                            None
                        } else {
                            Some(size)
                        }
                    });
                    self.apply_pointer_add(dest, base, offset, stride, false);
                }
            }
            CallEffect::ReturnPtrOffsetFrom { ptr_arg, base_arg } => {
                let dest_ty = self.body().local_decls[dest].ty;
                let ptr = args.get(*ptr_arg).cloned();
                let base = args.get(*base_arg).cloned();
                let count = match (ptr.as_ref(), base.as_ref()) {
                    (Some(p), Some(b)) => self
                        .iter_remaining_len_from_ptrs(b, p, None)
                        .unwrap_or_else(|| {
                            self.fresh_int(&format!("ptr_offset_from_{}", dest.as_usize()))
                        }),
                    _ => self.fresh_int(&format!("ptr_offset_from_{}", dest.as_usize())),
                };
                self.set_local(
                    dest,
                    VmValue {
                        z3_term: count,
                        ty: dest_ty,
                        provenance: None,
                        facts: ValueFacts::default(),
                        source: ValueSource::None,
                    },
                );
            }
            CallEffect::ReturnConst { value } => {
                let dest_ty = self.body().local_decls[dest].ty;
                let term = Int::from_u64(self.z3_ctx, *value);
                let val = VmValue::new(term, dest_ty);
                self.set_local(dest, val);
            }
            CallEffect::ReturnAlignOffset { ptr_arg, align_arg } => {
                let dest_ty = self.body().local_decls[dest].ty;
                let offset = self.fresh_int(&format!("align_offset_{}", dest.as_usize()));
                if let (Some(ptr_val), Some(align_val)) = (args.get(*ptr_arg), args.get(*align_arg)) {
                    let elem = mir_utils::pointee_ty(ptr_val.ty)
                        .map(|pointee| self.size_sym(pointee))
                        .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
                    let byte_off = Int::mul(self.z3_ctx, &[&offset, &elem]);
                    let ptr_plus_off = Int::add(self.z3_ctx, &[&ptr_val.z3_term, &byte_off]);
                    let zero = Int::from_u64(self.z3_ctx, 0);
                    let pointer_bits = self.tcx.data_layout.pointer_size().bits();
                    let max_value = if pointer_bits >= 64 {
                        u64::MAX
                    } else {
                        (1u64 << pointer_bits) - 1
                    };
                    let max = Int::from_u64(self.z3_ctx, max_value);
                    let aligned = ptr_plus_off.rem(&align_val.z3_term)._eq(&zero);
                    let nonnegative = offset.ge(&zero);
                    let bounded = offset.lt(&align_val.z3_term);
                    let success = Bool::and(self.z3_ctx, &[&aligned, &nonnegative, &bounded]);
                    self.constraints.assertions.push(Bool::or(
                        self.z3_ctx,
                        &[&offset._eq(&max), &success],
                    ));
                }
                let val = VmValue::new(offset, dest_ty);
                self.set_local(dest, val);
            }
            CallEffect::ReturnMin { lhs_arg, rhs_arg } => {
                // Build the min as a first-class `ite(lhs <= rhs, lhs, rhs)`
                // term rather than a fresh variable plus disjunction facts.
                // A fresh variable breaks downstream alignment/bounds
                // reasoning: e.g. `ptr.align_offset(8)` guarantees
                // `(ptr + offset) % 8 == 0`, but `offset.min(len)` would
                // then become an unrelated symbol and the `Align`/`InBound`
                // checks on `*(ptr.add(offset) as *const usize)` could no
                // longer discharge.  With an `ite`, the path conditions
                // (`offset < 8`, `len >= 16`) let the solver reduce
                // `ite(offset <= len, offset, len)` back to `offset`.
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
            CallEffect::ReturnBranchPayload { arg } => {
                let dest_ty = self.body().local_decls[dest].ty;
                if let Some(value) = args.get(*arg)
                    && let Some(discr) = value.discriminant()
                    && let TyKind::Adt(adt, _) = value.ty.kind()
                {
                    let branch_discr = if self
                        .tcx
                        .is_diagnostic_item(rustc_span::sym::Option, adt.did())
                    {
                        let one = Int::from_u64(self.z3_ctx, 1);
                        Some(Int::sub(self.z3_ctx, &[&one, discr]))
                    } else if self
                        .tcx
                        .is_diagnostic_item(rustc_span::sym::Result, adt.did())
                    {
                        Some(discr.clone())
                    } else {
                        None
                    };
                    if let Some(branch_discr) = branch_discr {
                        let term = self.fresh_int("try_branch");
                        self.set_local(
                            dest,
                            VmValue {
                                z3_term: term,
                                ty: dest_ty,
                                provenance: None,
                                facts: ValueFacts::default(),
                                source: ValueSource::Discriminant(branch_discr),
                            },
                        );
                    }
                }
                let arg_local = caller_arg_locals.get(*arg).copied().flatten();
                if let Some(l) = arg_local
                    && let Some(payload) = self.field_value(l, &[0]).cloned()
                {
                    self.set_field_value(dest, vec![0], payload);
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
                        || !matches!(value.ty.kind(), TyKind::Uint(_))
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
                        self.constraints.assertions.push(
                            value.z3_term._eq(&zero).implies(&term._eq(&width_term)),
                        );
                        self.constraints.assertions.push(
                            value.z3_term.lt(&high_bit).implies(&term.ge(&one)),
                        );
                        self.constraints.assertions.push(
                            value.z3_term.ge(&high_bit).implies(&term._eq(&zero)),
                        );
                        let dest_ty = self.body().local_decls[dest].ty;
                        self.set_local(dest, VmValue::new(term, dest_ty));
                    }
                }
            }
            CallEffect::CopyMemory {
                source_arg,
                destination_arg,
                count_arg,
            } => {
                if let (Some(source), Some(target), Some(count)) = (
                    args.get(*source_arg),
                    args.get(*destination_arg),
                    args.get(*count_arg),
                ) {
                    self.copy_memory_values(source, target, count);
                }
            }
            CallEffect::SwapMemory {
                left_arg,
                right_arg,
            } => {
                let Some((left, right)) = args.get(*left_arg).zip(args.get(*right_arg)) else {
                    self.unsupported_mir = true;
                    return;
                };
                if !self.swap_memory_values(left, right) {
                    self.unsupported_mir = true;
                }
            }
            CallEffect::FillBytes {
                pointer_arg,
                byte_arg,
                count_arg,
            } => {
                let (Some(pointer), Some(byte), Some(count)) = (
                    args.get(*pointer_arg),
                    args.get(*byte_arg),
                    args.get(*count_arg),
                ) else {
                    self.unsupported_mir = true;
                    return;
                };
                let concrete_count = count.z3_term.simplify().as_u64();
                if concrete_count == Some(0) {
                    return;
                }
                let (Some(ty), Some(byte_value)) = (
                    mir_utils::pointee_ty(pointer.ty),
                    byte.z3_term.simplify().as_u64(),
                ) else {
                    self.unsupported_mir = true;
                    return;
                };
                let local = self
                    .find_local_by_address(&pointer.z3_term)
                    .filter(|local| self.body().local_decls[*local].ty == ty);
                let inline_target =
                    self.inline
                        .arg_referents
                        .iter()
                        .enumerate()
                        .any(|(i, referent)| {
                            referent.is_some()
                                && self
                                    .local_value(Local::from_usize(i + 1))
                                    .is_some_and(|value| value.z3_term == pointer.z3_term)
                        });
                if concrete_count != Some(1)
                    || (local.is_none() && !inline_target)
                    || !matches!(ty.kind(), TyKind::Int(_) | TyKind::Uint(_))
                    || byte_value > u8::MAX as u64
                {
                    self.unsupported_mir = true;
                    return;
                }
                let value_bits = if byte_value == 0 {
                    0
                } else {
                    let size = self.size_of_ty(ty);
                    if !matches!(ty.kind(), TyKind::Uint(_)) || size == 0 || size > 8 {
                        self.unsupported_mir = true;
                        return;
                    }
                    (0..size).fold(0_u64, |bits, index| bits | (byte_value << (8 * index)))
                };
                let mut value = VmValue::new(Int::from_u64(self.z3_ctx, value_bits), ty);
                value.facts.init = true;
                self.write_through_pointer(pointer, Vec::new(), value);
                if let Some(local) = local
                    && let Some(alloc_id) = self.current_frame.local_alloc.get(&local).copied()
                {
                    self.content_mut(alloc_id).facts.initialized = true;
                }
            }
            CallEffect::WriteMemory { pointer_arg } => {
                if let Some(arg_val) = args.get(*pointer_arg)
                    && let Some(prov) = &arg_val.provenance
                {
                    // Writing a non-`u8` value through a byte buffer reinterprets
                    // it (e.g. `*mut FreeBlock` cast from a `Vec<u8>` buffer):
                    // update the allocation's element type so a later `Typed`
                    // invariant matches the written type.
                    if let rustc_middle::ty::TyKind::RawPtr(inner, _)
                    | rustc_middle::ty::TyKind::Ref(_, inner, _) = arg_val.ty.kind()
                    {
                        let cur = self.alloc(prov.alloc_id).element_ty.as_ty();
                        let is_u8 = |t: rustc_middle::ty::Ty<'_>| {
                            matches!(
                                t.kind(),
                                rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8)
                            )
                        };
                        if let Some(c) = cur
                            && is_u8(c)
                            && !is_u8(*inner)
                        {
                            self.alloc_mut(prov.alloc_id).element_ty = ElementTy::Typed(*inner);
                        }
                    }
                    let is_vec = api_classify::is_vec_push_or_reserve(callee);
                    let is_external = self.alloc(prov.alloc_id).is_external();
                    if is_vec && !is_external {
                        let elem_ty = match arg_val.ty.kind() {
                            TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => {
                                crate::verify::call_summary::effects::vec_elem_ty(*inner)
                            }
                            _ => crate::verify::call_summary::effects::vec_elem_ty(arg_val.ty),
                        };
                        let heap_align = elem_ty
                            .map(|ty| self.align_sym(ty))
                            .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
                        if let Some(old_data) = self.container_data_alloc(prov.alloc_id, arg_val.ty)
                        {
                            self.alloc_mut(old_data).facts.dead = true;
                        }
                        let max_size = Int::from_u64(self.z3_ctx, i64::MAX as u64);
                        let (data_alloc, data_base) =
                            self.allocate_external(max_size, heap_align, elem_ty);
                        let container_ty = match arg_val.ty.kind() {
                            TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => *inner,
                            _ => arg_val.ty,
                        };
                        self.set_container_data_field(
                            prov.alloc_id,
                            arg_val.ty,
                            data_alloc,
                            data_base,
                            elem_ty.unwrap_or(container_ty),
                        );
                    }
                    let off_u64 = prov
                        .offset
                        .as_u64()
                        .or_else(|| prov.offset.simplify().as_u64());
                    let written_pointee_ty = self.alloc(prov.alloc_id).element_ty.as_ty().and_then(|ty| {
                        match ty.kind() {
                            TyKind::Adt(def, args) if api_classify::is_maybe_uninit_type(def.did()) => {
                                args.first().and_then(|arg| arg.as_type())
                                    .filter(|inner| Some(*inner) == mir_utils::pointee_ty(arg_val.ty))
                            }
                            _ => None,
                        }
                    });
                    if let Some(off) = off_u64 {
                        if off == 0 {
                            self.content_mut(prov.alloc_id).facts.initialized = true;
                        }
                        let elem_size = match arg_val.ty.kind() {
                            rustc_middle::ty::TyKind::Ref(_, inner, _) => {
                                self.size_of_ty(*inner) as usize
                            }
                            _ => 0,
                        };
                        let write_size = if elem_size > 0 {
                            elem_size
                        } else {
                            self.allocation_size(prov.alloc_id).as_u64().unwrap_or(0) as usize
                        };
                        let end = (off as usize + write_size).min(4096);
                        for byte_off in (off as usize)..end {
                            self.mark_byte_init(prov.alloc_id, byte_off);
                        }
                    } else {
                        // Symbolic write offset: the exact written element
                        // can't be tracked per-byte. For concrete allocation
                        // sizes, mark every byte (as before). For unknown /
                        // zero sizes — generic element types such as
                        // `MaybeUninit<T>` inside `[MaybeUninit<T>; N]` —
                        // mark the whole allocation initialized so a later
                        // `assume_init_read`/`assume_init_drop` can discharge
                        // `Init` on those (fully initialized) elements.
                        let size_val = self.allocation_size(prov.alloc_id).as_u64();
                        match size_val {
                            Some(sz) if sz > 0 => {
                                for off in 0..(sz as usize).min(1024) {
                                    self.mark_byte_init(prov.alloc_id, off);
                                }
                            }
                            _ => {
                                self.content_mut(prov.alloc_id).facts.initialized = true;
                            }
                        }
                    }
                    if off_u64 == Some(0) {
                        self.content_mut(prov.alloc_id).facts.written_pointee_ty = written_pointee_ty;
                    }
                }
            }
            CallEffect::ReturnNullableAllocation { size_arg, align_arg, zeroed } => {
                if let Some(size) = args.get(*size_arg) {
                    let align = args
                        .get(*align_arg)
                        .map(|value| value.z3_term.clone())
                        .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
                    let (alloc_id, base) =
                        self.allocate_external(size.z3_term.clone(), align, Some(self.tcx.types.u8));
                    self.alloc_mut(alloc_id).facts.owning = Some(base.clone());
                    self.alloc_mut(alloc_id).facts.locally_allocated = true;
                    if *zeroed {
                        self.content_mut(alloc_id).facts.initialized = true;
                    }
                    let dest_ty = self.body().local_decls[dest].ty;
                    self.set_local(
                        dest,
                        VmValue {
                            z3_term: base,
                            ty: dest_ty,
                            provenance: Some(Provenance {
                                alloc_id,
                                offset: Int::from_u64(self.z3_ctx, 0),
                                offset_kind: None,
                            }),
                            facts: ValueFacts::default(),
                            source: ValueSource::None,
                        },
                    );
                }
            }
            CallEffect::ReturnVecFromSlice => {
                self.ensure_local_allocation(dest);
                let dest_ty = self.body().local_decls[dest].ty;
                let elem_ty = crate::verify::call_summary::effects::vec_elem_ty(dest_ty);
                let heap_align = elem_ty
                    .map(|ty| self.align_sym(ty))
                    .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
                let known_len = args
                    .first()
                    .and_then(|v| v.provenance.as_ref())
                    .and_then(|p| {
                        let alloc = self.alloc(p.alloc_id);
                        if let Some(slice_len) = alloc.slice_len().cloned() {
                            return Some(slice_len);
                        }
                        let source_ty = alloc.element_ty.as_ty()?;
                        let array_ty = match source_ty.kind() {
                            TyKind::Adt(def, args)
                                if api_classify::is_maybe_uninit_type(def.did()) =>
                            {
                                args.first()?.as_type()?
                            }
                            _ => source_ty,
                        };
                        let TyKind::Array(_, count) = array_ty.kind() else {
                            return None;
                        };
                        Some(self.const_len_term(count))
                    })
                    .or_else(|| {
                        let TyKind::Adt(box_def, box_args) = args.first()?.ty.kind() else {
                            return None;
                        };
                        if !api_classify::is_std_box(box_def.did()) {
                            return None;
                        }
                        let mut source_ty = box_args.first()?.as_type()?;
                        if let TyKind::Adt(def, args) = source_ty.kind()
                            && api_classify::is_maybe_uninit_type(def.did())
                        {
                            source_ty = args.first()?.as_type()?;
                        }
                        let TyKind::Array(_, count) = source_ty.kind() else {
                            return None;
                        };
                        Some(self.const_len_term(count))
                    });
                let size = if let Some(len) = &known_len {
                    let elem_size = elem_ty
                        .map(|ty| self.size_sym(ty))
                        .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
                    Int::mul(self.z3_ctx, &[len, &elem_size])
                } else {
                    Int::from_u64(self.z3_ctx, i64::MAX as u64)
                };
                let (alloc_id, base) = self.allocate_external(size, heap_align, elem_ty);
                if let Some(len) = &known_len {
                    self.alloc_mut(alloc_id).set_slice_len(len.clone());
                }
                if let Some(box_alloc) = args.first().and_then(|v| v.provenance_alloc_id()) {
                    self.copy_byte_tracking(box_alloc, 0, alloc_id);
                }
                if let Some(ptr_field) =
                    self.set_external_container_result(dest, alloc_id, base, elem_ty)
                {
                    let len_term = known_len
                        .clone()
                        .unwrap_or_else(|| self.fresh_int(&format!("vec_len_{}", dest.as_usize())));
                    self.materialize_vec_fields(dest, ptr_field, len_term.clone(), len_term);
                }
            }
            CallEffect::DropMemory { pointer_arg } => {
                // `ManuallyDrop::drop(slot)` / `drop_in_place(x)` frees the heap
                // allocation behind the argument. A reference/raw-pointer
                // argument carries the *stack* provenance of the referent
                // (penetrate to its heap field); a value argument (`Box`/`Vec`)
                // carries the heap provenance directly. Mark the allocation
                // dead; a second drop of an already-dead allocation is detected
                // downstream via `dead` alone.
                if let Some(arg_val) = args.get(*pointer_arg) {
                    let alloc_id = if matches!(
                        arg_val.ty.kind(),
                        rustc_middle::ty::TyKind::Ref(..) | rustc_middle::ty::TyKind::RawPtr(..)
                    ) {
                        self.find_local_by_address(&arg_val.z3_term)
                            .and_then(|r| self.owner_ptr_field(r))
                            .and_then(|v| v.provenance_alloc_id())
                    } else {
                        arg_val.provenance_alloc_id()
                    };
                    if let Some(alloc_id) = alloc_id {
                        self.alloc_mut(alloc_id).facts.dead = true;
                    }
                }
            }
            CallEffect::ReturnIterLen => self.apply_iter_len_effect(args, caller_arg_locals, dest),
            CallEffect::ReturnNonNullNew => {
                let Some(ptr) = args.first() else {
                    return;
                };
                let dest_ty = self.body().local_decls[dest].ty;
                let zero = Int::from_u64(self.z3_ctx, 0);
                let one = Int::from_u64(self.z3_ctx, 1);
                let definitely_non_null = ptr.facts.non_null
                    || ptr.facts.in_bounds
                    || ptr
                        .provenance
                        .as_ref()
                        .is_some_and(|p| !self.alloc(p.alloc_id).is_external());
                let discr = if definitely_non_null {
                    self.constraints
                        .assertions
                        .push(ptr.z3_term._eq(&zero).not());
                    one
                } else {
                    ptr.z3_term._eq(&zero).ite(&zero, &one)
                };
                let mut result = VmValue::new(self.fresh_int("nn_new"), dest_ty);
                result.source = ValueSource::Discriminant(discr);
                self.set_local(dest, result);
                self.set_field_value(dest, vec![0], ptr.clone());
            }
            CallEffect::ReturnIterNext => self.apply_iter_next_effect(args, dest),
            CallEffect::ReturnRangeNext => self.apply_range_next_effect(args, dest),
        }
    }

    fn set_opaque_intrinsic_result(&mut self, dest: Local) {
        let ty = self.body().local_decls[dest].ty;
        let term = self.fresh_int("intrinsic_result");
        self.inline.opaque_intrinsic_terms.insert(term.clone());
        self.set_local(dest, VmValue::new(term, ty));
    }

    fn set_external_container_result(
        &mut self,
        dest: Local,
        alloc_id: AllocId,
        base: Int<'z3>,
        elem_ty: Option<Ty<'tcx>>,
    ) -> Option<VmValue<'z3, 'tcx>> {
        let dest_ty = self.body().local_decls[dest].ty;
        let dest_alloc_id = self.current_frame.local_alloc.get(&dest).copied();
        self.alloc_mut(alloc_id).facts.owning = Some(base.clone());
        self.content_mut(alloc_id).facts.initialized = true;
        self.set_local(
            dest,
            VmValue {
                z3_term: base.clone(),
                ty: dest_ty,
                provenance: dest_alloc_id.map(|stack_id| Provenance {
                    alloc_id: stack_id,
                    offset: Int::from_u64(self.z3_ctx, 0),
                    offset_kind: None,
                }),
                facts: ValueFacts {
                    non_null: true,
                    init: true,
                    in_bounds: true,
                    ..ValueFacts::default()
                },
                source: ValueSource::None,
            },
        );
        let TyKind::Adt(adt_def, _) = dest_ty.kind() else {
            return None;
        };
        if !api_classify::is_std_vec(adt_def.did()) {
            return None;
        }
        Some(VmValue {
            z3_term: base,
            ty: elem_ty.unwrap_or(dest_ty),
            provenance: Some(Provenance {
                alloc_id,
                offset: Int::from_u64(self.z3_ctx, 0),
                offset_kind: None,
            }),
            facts: ValueFacts {
                non_null: true,
                init: true,
                in_bounds: true,
                ..ValueFacts::default()
            },
            source: ValueSource::None,
        })
    }

}
