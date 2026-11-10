mod memory;
mod numeric;
mod simd;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Local, Operand},
    ty::{Ty, TyKind},
};
use z3::ast::{Ast, Bool, Int};

use super::super::super::state::{
    AllocId, ElementTy, Provenance, ValueFacts, ValueSource, VmState, VmValue,
};
use crate::helpers::mir_utils;
use crate::verify::api_classify;
use crate::verify::call_summary::{
    BoundedArithmeticOp, CallEffect, OverflowOp, SimdArithOp, SimdCmpOp,
};

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    fn set_dest_as_heap_ptr(&mut self, arg_val: &VmValue<'z3, 'tcx>, dest: Local) {
        let mut val = arg_val.clone();
        val.ty = self.body().local_decls[dest].ty;
        val.facts.non_null = true;
        val.facts.init = true;
        self.set_local(dest, val);
    }

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
            CallEffect::AdjustRefCount { arg, owner, delta } => {
                if let Some(value) = args.get(*arg) {
                    if *delta > 0 {
                        self.grant_ownership_share(value, *owner);
                    } else {
                        self.consume_ownership_share(value, *owner, true);
                    }
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
            CallEffect::ReturnAlignOfVal { arg } => {
                let align = args.get(*arg).and_then(|value| {
                    let pointee = mir_utils::pointee_ty(value.ty)?;
                    match pointee.kind() {
                        TyKind::Slice(elem) => Some(self.align_sym(*elem)),
                        TyKind::Str => Some(Int::from_u64(self.z3_ctx, 1)),
                        TyKind::Dynamic(..) => None,
                        _ => Some(self.align_sym(pointee)),
                    }
                });
                if let Some(align) = align {
                    let ty = self.body().local_decls[dest].ty;
                    self.set_local(dest, VmValue::new(align, ty));
                } else {
                    self.set_opaque_intrinsic_result(dest);
                }
            }
            CallEffect::ReturnCompareBytes {
                left_arg,
                right_arg,
                count_arg,
            } => {
                let Some((left, right, count)) = args
                    .get(*left_arg)
                    .zip(args.get(*right_arg))
                    .zip(args.get(*count_arg))
                    .map(|((left, right), count)| (left, right, count))
                else {
                    self.record_unsupported("compare_bytes arguments");
                    return;
                };
                let ty = self.body().local_decls[dest].ty;
                let term = if count.z3_term.simplify().as_u64() == Some(0)
                    || left.z3_term == right.z3_term
                {
                    Int::from_u64(self.z3_ctx, 0)
                } else {
                    let result = self.fresh_int("compare_bytes_result");
                    if let Some((min, max, _, _)) = self.integer_limits(ty) {
                        self.constraints.assertions.push(result.ge(&min));
                        self.constraints.assertions.push(result.le(&max));
                    }
                    result
                };
                self.set_local(dest, VmValue::new(term, ty));
            }
            CallEffect::ReturnMaskedPointer {
                pointer_arg,
                mask_arg,
            } => {
                let unchanged = args.get(*mask_arg).is_some_and(|mask| {
                    let value = mask.z3_term.simplify();
                    value.as_u64() == Some(usize::MAX as u64) || value.as_i64() == Some(-1)
                });
                if unchanged {
                    if let Some(pointer) = args.get(*pointer_arg) {
                        let mut pointer = pointer.clone();
                        pointer.ty = self.body().local_decls[dest].ty;
                        self.set_local(dest, pointer);
                    }
                } else {
                    self.set_opaque_intrinsic_result(dest);
                }
            }
            effect @ (CallEffect::LoadMemory { .. }
            | CallEffect::StoreMemory { .. }
            | CallEffect::AtomicRmw { .. }
            | CallEffect::CopyMemory { .. }
            | CallEffect::SwapMemory { .. }
            | CallEffect::FillBytes { .. }
            | CallEffect::WriteMemory { .. }) => {
                self.apply_memory_effect(effect, args, dest, callee);
            }
            effect @ (CallEffect::SimdCompare { .. }
            | CallEffect::SimdArithmetic { .. }
            | CallEffect::SimdOpaque
            | CallEffect::SimdSplat { .. }
            | CallEffect::SimdExtract { .. }
            | CallEffect::SimdInsert { .. }
            | CallEffect::SimdHavocMemory { .. }
            | CallEffect::SimdMaskedFallback { .. }
            | CallEffect::SimdBitmask { .. }) => {
                self.apply_simd_effect(effect, args, caller_arg_locals, dest);
            }
            CallEffect::ReturnRawEq {
                left_arg,
                right_arg,
            } => {
                let ty = self.body().local_decls[dest].ty;
                let Some((left, right)) = args.get(*left_arg).zip(args.get(*right_arg)) else {
                    self.record_unsupported_effect("ReturnRawEq arguments unavailable");
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
                    self.record_unsupported_effect("ReturnExactDiv arguments unavailable");
                    return;
                };
                if !matches!(ty.kind(), TyKind::Uint(_)) {
                    self.record_unsupported_effect("ReturnExactDiv result type unsupported");
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
                    (Some(p), Some(b)) => self.iter_len_from_ptrs(b, p).unwrap_or_else(|| {
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
                if let (Some(ptr_val), Some(align_val)) = (args.get(*ptr_arg), args.get(*align_arg))
                {
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
                    self.constraints
                        .assertions
                        .push(Bool::or(self.z3_ctx, &[&offset._eq(&max), &success]));
                }
                let val = VmValue::new(offset, dest_ty);
                self.set_local(dest, val);
            }
            effect @ (CallEffect::ReturnMin { .. }
            | CallEffect::ReturnMax { .. }
            | CallEffect::ReturnAdd { .. }
            | CallEffect::ReturnMul { .. }
            | CallEffect::ReturnBoundedArithmetic { .. }
            | CallEffect::ReturnWithOverflow { .. }
            | CallEffect::ReturnNonZeroIff { .. }
            | CallEffect::ReturnLeadingZeros { .. }
            | CallEffect::ReturnTrailingZeros { .. }) => {
                self.apply_numeric_effect(effect, args, dest);
            }
            CallEffect::ReturnNullableAllocation {
                size_arg,
                align_arg,
                zeroed,
            } => {
                if let Some(size) = args.get(*size_arg) {
                    let align = args
                        .get(*align_arg)
                        .map(|value| value.z3_term.clone())
                        .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
                    let (alloc_id, base) = self.allocate_external(
                        size.z3_term.clone(),
                        align,
                        Some(self.tcx.types.u8),
                    );
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
        }
    }

    fn simd_lane_type(&self, ty: Ty<'tcx>) -> Option<(Ty<'tcx>, usize)> {
        let TyKind::Adt(def, args) = ty.kind() else {
            return None;
        };
        if !def.repr().simd() {
            return None;
        }
        let field = mir_utils::field_ty(self.tcx, def.non_enum_variant().fields.raw.first()?, args);
        let TyKind::Array(elem, len) = field.kind() else {
            return None;
        };
        let len = mir_utils::eval_array_len(self.tcx, len)? as usize;
        Some((*elem, len))
    }

    fn set_opaque_simd_result(&mut self, dest: Local) {
        let dest_ty = self.body().local_decls[dest].ty;
        let Some((elem_ty, len)) = self.simd_lane_type(dest_ty) else {
            self.set_opaque_intrinsic_result(dest);
            return;
        };
        let limits = self.integer_limits(elem_ty);
        for index in 0..len {
            let term = self.fresh_int("simd_lane");
            if let Some((min, max, _, _)) = &limits {
                self.constraints.assertions.push(term.ge(min));
                self.constraints.assertions.push(term.le(max));
            }
            let mut value = VmValue::new(term, elem_ty);
            value.facts.init = true;
            self.set_field_value(dest, vec![0, index], value);
        }
    }

    fn copy_simd_result_from_local(&mut self, dest: Local, source: Local) -> bool {
        let dest_ty = self.body().local_decls[dest].ty;
        let Some((_, len)) = self.simd_lane_type(dest_ty) else {
            return false;
        };
        let lanes: Option<Vec<_>> = (0..len)
            .map(|index| self.field_value(source, &[0, index]).cloned())
            .collect();
        let Some(lanes) = lanes else {
            return false;
        };
        for (index, value) in lanes.into_iter().enumerate() {
            self.set_field_value(dest, vec![0, index], value);
        }
        true
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
