//! Transfer functions for MIR rvalues.

use rustc_abi::FieldIdx;
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::mir::{AggregateKind, BinOp, CastKind, Operand, Place, UnOp};
#[cfg(rapx_const_ext)]
use rustc_middle::ty::consts::ConstExt;
use rustc_middle::ty::{Ty, TyKind};
use z3::ast::{Ast, Int};

use super::super::state::{
    Provenance, REPEATED_ARRAY_ELEMENT, ValueFacts, ValueSource, VmState, VmValue,
};

use crate::helpers::mir_utils;
use crate::verify::api_classify;

pub(crate) fn eval_use<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    place: &Place<'tcx>,
    operand: &Operand<'tcx>,
) -> VmValue<'z3, 'tcx> {
    let mut val = state.value_of_operand(operand);
    if let rustc_middle::mir::Operand::Constant(c) = operand
        && place.projection.is_empty()
    {
        state.materialize_const_adt(place.local, &c.const_);
    }
    state.try_materialize_const_bytes(&mut val, operand);
    if let Operand::Constant(_) = operand
        && let Some(bytes) = mir_utils::const_operand_bytes(state.tcx, operand)
    {
        val.source = ValueSource::ConstBytes(bytes);
    }
    state.inject_layout_constraints(operand, &val);
    state.try_emit_gcd_divisibility(operand, &val);
    val
}

pub(crate) fn eval_ref<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    place: &Place<'tcx>,
) -> VmValue<'z3, 'tcx> {
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    if let Some(addr) = state.address_of_place(place) {
        let alloc_align = state.alloc_align_of(&addr);
        let has_deref = place
            .projection
            .iter()
            .any(|p| matches!(p.kind(), rustc_middle::mir::ProjectionElem::Deref));
        let src_ty = state.body().local_decls[place.local].ty;
        let is_from_raw_parts_like =
            matches!(src_ty.kind(), rustc_middle::ty::TyKind::RawPtr(_, _));
        let is_slice_ref = if let rustc_middle::ty::TyKind::Ref(_, inner, _) = dest_ty.kind() {
            matches!(inner.kind(), rustc_middle::ty::TyKind::Slice(_))
        } else {
            false
        };
        let is_slice_ref_from_raw = is_slice_ref && is_from_raw_parts_like && has_deref;
        let src_in_bounds = if is_slice_ref_from_raw {
            addr.is_pointer()
        } else {
            state
                .local_value(place.local)
                .is_some_and(|v| v.facts.in_bounds)
        };
        // An empty slice (`&[]` from `align_to`'s `offset > len` / ZST branch)
        // is built as `&*dangling`: the dangling raw pointer (`NonNull::dangling`)
        // is aligned to the *element* type, but its provenance here may reuse
        // `self`'s allocation (whose align is that of `T`).  Record the element
        // type's alignment so `check_align` can discharge it.
        let slice_elem_align = if is_slice_ref_from_raw {
            if let rustc_middle::ty::TyKind::Ref(_, inner, _) = dest_ty.kind() {
                if let rustc_middle::ty::TyKind::Slice(elem) = inner.kind() {
                    let a = state.align_sym(*elem);
                    if a.simplify().as_u64() != Some(1) {
                        Some(a)
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        };
        let val = VmValue {
            z3_term: addr.z3_term,
            ty: dest_ty,
            provenance: addr.provenance,
            facts: ValueFacts {
                non_null: true,
                init: true,
                in_bounds: src_in_bounds,
                align_n: slice_elem_align.or(alloc_align),
                dangling: false,
            },
            source: match state.local_value(place.local).map(|value| &value.source) {
                Some(ValueSource::SliceLen(len)) if is_slice_ref && has_deref => {
                    ValueSource::SliceLen(len.clone())
                }
                _ => ValueSource::None,
            },
        };
        state.propagate_byte_values_to_ref(place, &val);
        state.propagate_field_values_to_ref(place, dest_place.local);
        // Expose the freshly-created reference's provenance before asserting
        // the pointee struct's `#[rapx::invariant]`s: the invariant predicates
        // (`ValidNum(len <= CAPACITY)` on `&LeafNode`) resolve their field
        // places through the pointee allocation, which needs `dest_place`'s
        // provenance to be live (`exec_assign` only stores `val` afterwards).
        state.set_local(dest_place.local, val.clone());
        state.assert_pointee_struct_invariants(dest_ty, dest_place.local);
        val
    } else {
        let term = state.fresh_int("ref_addr");
        VmValue {
            z3_term: term,
            ty: dest_ty,
            provenance: None,
            facts: ValueFacts {
                non_null: true,
                init: true,
                ..Default::default()
            },
            source: ValueSource::None,
        }
    }
}

pub(crate) fn eval_raw_ptr<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    place: &Place<'tcx>,
) -> VmValue<'z3, 'tcx> {
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    if let Some(addr) = state.address_of_place(place) {
        let alloc_align = state.alloc_align_of(&addr);
        let source_in_bounds = state
            .local_value(place.local)
            .is_some_and(|v| v.facts.in_bounds);
        VmValue {
            z3_term: addr.z3_term,
            ty: dest_ty,
            provenance: addr.provenance,
            facts: ValueFacts {
                non_null: true,
                in_bounds: source_in_bounds,
                align_n: alloc_align,
                ..Default::default()
            },
            source: ValueSource::None,
        }
    } else {
        let term = state.fresh_int("rawptr_addr");
        VmValue {
            z3_term: term,
            ty: dest_ty,
            provenance: None,
            facts: ValueFacts {
                non_null: true,
                ..Default::default()
            },
            source: ValueSource::None,
        }
    }
}

pub(crate) fn eval_binary_op<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    op: BinOp,
    pair: &(Operand<'tcx>, Operand<'tcx>),
) -> VmValue<'z3, 'tcx> {
    let (lhs_op, rhs_op) = pair;
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;

    let lhs = state.value_of_operand(lhs_op);
    let rhs = state.value_of_operand(rhs_op);
    // `Offset(ptr, count)` is the MIR lowering of `ptr.add(count)`/`ptr.sub(count)`
    // (via `intrinsics::offset`): pointer arithmetic in *element* units. Model it
    // with the same stride/provenance/align precision as pointer addition
    // effect, so inlined pointer arithmetic keeps `ValidPtr`/`Align` dischargeable.
    if op == BinOp::Offset {
        // The *base* operand carries the monomorphized pointee type (e.g. the
        // caller's `*const u32`), whereas `dest_ty` is the callee's declared
        // generic `*const T`.  Derive the stride from the base's value type so
        // a generic `T` doesn't turn the stride into an unrelated `size_sym(T)`
        // symbol that breaks `Allocated`'s byte-coverage query.
        let pointee = mir_utils::pointee_ty(lhs.ty);
        let stride = pointee.and_then(|p| {
            if mir_utils::ty_has_type_param(p)
                && let Some(alloc_id) = lhs.provenance_alloc_id()
                && let Some(element) = state.alloc(alloc_id).element_ty.as_ty()
                && !mir_utils::ty_has_type_param(element)
            {
                return Some(state.size_of_ty(element));
            }
            let (_, s) = mir_utils::type_layout(state.tcx, state.current_frame.current_def_id, p)?;
            if s == 0 && mir_utils::ty_has_type_param(p) {
                None
            } else {
                Some(s)
            }
        });
        state.apply_pointer_add(dest_place.local, &lhs, &rhs, stride, false);
        return state
            .local_value(dest_place.local)
            .cloned()
            .expect("pointer arithmetic must assign its destination");
    }
    let raw_term = state.eval_binary_op(op, &lhs.z3_term, &rhs.z3_term);
    if matches!(op, BinOp::Shl | BinOp::ShlUnchecked)
        && lhs.z3_term.simplify().as_u64() == Some(1)
        && matches!(lhs.ty.kind(), TyKind::Uint(_) | TyKind::Int(_))
    {
        let zero = Int::from_u64(state.z3_ctx, 0);
        state.constraints.assertions.push(raw_term._eq(&zero).not());
    }
    let term = if op == BinOp::Sub
        && api_classify::is_integer_wrapping_sub_method(Some(state.current_frame.current_def_id))
    {
        if let Some((_, max, modulus, signed)) = state.integer_limits(lhs.ty) {
            let wrapped = raw_term.modulo(&modulus);
            if signed {
                wrapped
                    .gt(&max)
                    .ite(&Int::sub(state.z3_ctx, &[&wrapped, &modulus]), &wrapped)
            } else {
                wrapped
            }
        } else {
            raw_term
        }
    } else {
        raw_term
    };
    let provenance = state.provenance_for_binary_op(op, &lhs, &rhs);
    let invariants = state.facts_for_binary_op(op, &lhs, &rhs, &provenance);
    let lhs_pk = mir_utils::operand_place(lhs_op);
    let rhs_pk = mir_utils::operand_place(rhs_op);
    // Carry the direct boolean condition alongside the ite-encoded result so
    // `switchInt`/`Assert` can record a precise path condition (e.g.
    // `offset <= len - 16`) instead of `ite(cond, 1, 0) != 0`, which the SMT
    // solver often fails to unfold.
    let cmp_cond = state
        .iter_ptr_comparison(op, &lhs, &rhs)
        .or_else(|| match op {
            BinOp::Le => Some(lhs.z3_term.le(&rhs.z3_term)),
            BinOp::Lt => Some(lhs.z3_term.lt(&rhs.z3_term)),
            BinOp::Ge => Some(lhs.z3_term.ge(&rhs.z3_term)),
            BinOp::Gt => Some(lhs.z3_term.gt(&rhs.z3_term)),
            BinOp::Eq => Some(lhs.z3_term._eq(&rhs.z3_term)),
            BinOp::Ne => Some(lhs.z3_term._eq(&rhs.z3_term).not()),
            _ => None,
        });
    if matches!(op, BinOp::Div | BinOp::Rem) {
        state.emit_div_rem_axioms(op, &term, &lhs.z3_term, &rhs.z3_term);
    }
    // For tuple-returning binary ops (AddWithOverflow, MulWithOverflow),
    // populate the field values so that .0 (result) and .1 (overflow flag)
    // are properly tracked. Without this, field access falls through to
    // cloning the base term, mixing the arithmetic result with the boolean
    // overflow flag and corrupting path conditions.
    if let rustc_middle::ty::TyKind::Tuple(fields) = dest_ty.kind()
        && fields.len() == 2
    {
        let result_val = VmValue {
            z3_term: term.clone(),
            ty: fields[0],
            provenance: provenance.clone(),
            facts: invariants.clone(),
            source: ValueSource::None,
        };
        state.set_field_value(dest_place.local, vec![0], result_val);
        let overflow_term = if matches!(op, BinOp::MulWithOverflow)
            && (lhs.z3_term.simplify().as_u64().is_some_and(|n| n <= 1)
                || rhs.z3_term.simplify().as_u64().is_some_and(|n| n <= 1))
        {
            Int::from_u64(state.z3_ctx, 0)
        } else if matches!(
            op,
            BinOp::AddWithOverflow | BinOp::SubWithOverflow | BinOp::MulWithOverflow
        )
            && let Some((min, max, _, _)) = state.integer_limits(lhs.ty)
        {
            let overflow = z3::ast::Bool::or(state.z3_ctx, &[&term.lt(&min), &term.gt(&max)]);
            overflow.ite(
                &Int::from_u64(state.z3_ctx, 1),
                &Int::from_u64(state.z3_ctx, 0),
            )
        } else {
            state.fresh_int("overflow_flag")
        };
        let overflow_val = VmValue::new(overflow_term, fields[1]);
        state.set_field_value(dest_place.local, vec![1], overflow_val);
    }
    VmValue {
        z3_term: term,
        ty: dest_ty,
        provenance,
        facts: invariants,
        source: match cmp_cond {
            Some(cond) => ValueSource::Comparison {
                lhs: lhs_pk,
                rhs: rhs_pk,
                op,
                cond,
            },
            None => ValueSource::BinaryOp {
                lhs: lhs_pk,
                rhs: rhs_pk,
                op,
            },
        },
    }
}

pub(crate) fn eval_unary_op<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    op: UnOp,
    operand: &Operand<'tcx>,
) -> VmValue<'z3, 'tcx> {
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    let val = state.value_of_operand(operand);
    let is_bool = matches!(val.ty.kind(), rustc_middle::ty::TyKind::Bool);
    let mut result_ty = dest_ty;
    let term = if matches!(op, UnOp::PtrMetadata) {
        // `PtrMetadata` on a `&[T]` gives the slice length, which is the
        // allocation size divided by the element size. Reuse the same symbolic
        // term as the allocation size so downstream InBound checks
        // (`offset <= len`) agree with the `len` used in loop guards
        // (`offset <= len - 16`).
        let is_dst = mir_utils::pointee_ty(val.ty).is_some_and(|p| {
            !p.is_sized(
                state.tcx,
                rustc_middle::ty::TypingEnv::post_analysis(
                    state.tcx,
                    state.current_frame.current_def_id,
                ),
            )
        });
        if is_dst {
            state
                .slice_len_from_value(&val)
                .unwrap_or_else(|| state.fresh_int("ptr_metadata"))
        } else {
            // A *sized* pointee has `()` metadata.  Re-type the value as unit
            // so `aggregate_raw_ptr` (`Rvalue::Aggregate(RawPtr(..))`) can
            // recognize the thin-pointer case and fold it to the data pointer
            // instead of materializing a fresh fat-pointer symbol.
            result_ty = state.tcx.types.unit;
            state.fresh_int("ptr_metadata")
        }
    } else {
        state.eval_unary_op(op, &val.z3_term, is_bool)
    };
    VmValue {
        z3_term: term,
        ty: result_ty,
        provenance: val.provenance,
        facts: val.facts,
        source: ValueSource::None,
    }
}

pub(crate) fn eval_cast<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    kind: CastKind,
    operand: &Operand<'tcx>,
    cast_ty: Ty<'tcx>,
) -> VmValue<'z3, 'tcx> {
    let mut src_val = state.value_of_operand(operand);
    #[cfg(rapx_box_deref_transmute)]
    if matches!(kind, CastKind::BoxDerefTransmute)
        && let Some(local) = mir_utils::extract_local(operand)
        && let Some(pointer) = state.field_value(local, &[0]).cloned()
    {
        src_val = pointer;
    }
    let src_ty = src_val.ty;
    let nonnull_to_raw = matches!(kind, CastKind::Transmute)
        && matches!(cast_ty.kind(), TyKind::RawPtr(..))
        && matches!(src_ty.kind(), TyKind::Adt(adt, _) if api_classify::is_std_nonnull(adt.did()));
    let numeric_transmute = matches!(kind, CastKind::Transmute)
        && mir_utils::is_std_crate_def_id(state.tcx, state.current_frame.current_def_id)
        && src_val.provenance.is_none()
        && (matches!(src_ty.kind(), TyKind::Int(_) | TyKind::Uint(_))
            || matches!(
                src_val.source,
                ValueSource::Discriminant(_) | ValueSource::KnownDiscriminant(_)
            ))
        && (matches!(cast_ty.kind(), TyKind::RawPtr(..))
            || matches!(cast_ty.kind(), TyKind::Adt(adt, _) if api_classify::is_std_nonnull(adt.did())));
    // A raw-pointer cast to a *different* ADT pointee reinterprets the
    // allocation's fields (e.g. `NonNull<LeafNode>::as_ptr() as *mut
    // InternalNode` in `NodeRef::as_internal_ptr`).  Lazily materialize the
    // target ADT's field view (keyed by type) so a later `(*cast_ptr).field`
    // resolves to the right field instead of the original view's field at the
    // same index.
    if let rustc_middle::ty::TyKind::RawPtr(target_ty, _) = cast_ty.kind()
        && let rustc_middle::ty::TyKind::Adt(adt_def, _) = target_ty.kind()
        && adt_def.is_struct()
        && let Some(alloc_id) = src_val.provenance_alloc_id()
    {
        state.decompose_pointee_fields(alloc_id, Vec::new(), *target_ty, *target_ty, 0, 0, 0);
    }
    // Transmute-like casts of single-field newtypes (e.g. NonZero::get's
    // `_0 = copy _1 as T`) yield the underlying field value, not the wrapper's
    // own term.
    let term = mir_utils::extract_local(operand)
        .and_then(|l| state.field_value(l, &[0]).map(|v| v.z3_term.clone()))
        .unwrap_or(src_val.z3_term);
    // A pointer→integer cast (`ptr as usize`) yields the (always non-negative)
    // address. Record this as a *path condition* so downstream pointer
    // arithmetic (e.g. `align_up` in a free-list allocator) can discharge
    // `NonNull` on the derived pointer — `check_non_null`'s SMT query only sees
    // path conditions, not the `term >= 0` constraint `assert_value_constraints`
    // adds.
    let src_is_ptr = matches!(
        src_ty.kind(),
        rustc_middle::ty::TyKind::RawPtr(..) | rustc_middle::ty::TyKind::Ref(..)
    );
    let dest_is_int = matches!(
        cast_ty.kind(),
        rustc_middle::ty::TyKind::Uint(_) | rustc_middle::ty::TyKind::Int(_)
    );
    if src_is_ptr && dest_is_int {
        let zero = Int::from_u64(state.z3_ctx, 0);
        state.constraints.assertions.push(term.ge(&zero));
        if src_val.facts.non_null {
            state.constraints.assertions.push(term._eq(&zero).not());
        }
    }
    VmValue {
        z3_term: term,
        ty: cast_ty,
        provenance: src_val.provenance,
        facts: ValueFacts {
            non_null: src_val.facts.non_null || nonnull_to_raw,
            dangling: src_val.facts.dangling || numeric_transmute,
            init: src_val.facts.init,
            in_bounds: src_val.facts.in_bounds,
            align_n: if mir_utils::pointee_ty(src_ty).is_some_and(|t| t.is_unit()) {
                None
            } else {
                src_val.facts.align_n
            },
        },
        source: src_val.source.field_offset_only(),
    }
}

pub(crate) fn eval_aggregate<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    kind: &AggregateKind<'tcx>,
    operands: &IndexVec<FieldIdx, Operand<'tcx>>,
) -> VmValue<'z3, 'tcx> {
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;

    // `intrinsics::aggregate_raw_ptr` lowers to `Rvalue::Aggregate(RawPtr(..))`
    // (`_0 = *const T from (data, meta)`).  For a *sized* pointee the metadata
    // operand is `()` and the result *is* the data pointer (a no-op cast used by
    // `byte_add`'s `with_metadata_of`), so return operand 0 preserving its
    // provenance and non-nullness instead of a fresh `aggregate` symbol.
    if let rustc_middle::mir::AggregateKind::RawPtr(pointee_ty, _) = kind
        && let Some(data_operand) = operands.iter().next()
    {
        let sized = pointee_ty.is_sized(
            state.tcx,
            rustc_middle::ty::TypingEnv::post_analysis(
                state.tcx,
                state.current_frame.current_def_id,
            ),
        ) || operands
            .iter()
            .nth(1)
            .is_some_and(|meta| state.value_of_operand(meta).ty.is_unit());
        if sized {
            let data_val = state.value_of_operand(data_operand);
            let mut val = data_val.clone();
            val.ty = dest_ty;
            return val;
        }
        if let Some(metadata) = operands.iter().nth(1) {
            let metadata = state.value_of_operand(metadata);
            let mut val = state.value_of_operand(data_operand);
            val.ty = dest_ty;
            if matches!(pointee_ty.kind(), TyKind::Slice(_))
                || metadata.ty == state.tcx.types.usize
            {
                val.source = ValueSource::SliceLen(metadata.z3_term);
            }
            return val;
        }
    }

    // For an enum aggregate, remember whether this is the data-carrying variant
    // of `Option`/`Result` (`Some`/`Ok`), so the nested-field flattening below
    // only fires on paths that actually carry a `Self`.
    let data_variant = match kind {
        rustc_middle::mir::AggregateKind::Adt(did, variant_idx, ..) => {
            if state.tcx.is_diagnostic_item(rustc_span::sym::Result, *did) {
                Some(variant_idx.as_usize() == 0)
            } else if state.tcx.is_diagnostic_item(rustc_span::sym::Option, *did) {
                Some(variant_idx.as_usize() == 1)
            } else {
                None
            }
        }
        _ => None,
    };
    // `NonNull::new_unchecked(ptr)` / `NonNull::from(&T)` construct a
    // repr(transparent) single-field newtype whose value *is* the underlying
    // pointer.  Model the wrapper as the pointer field itself (term + provenance
    // + invariants) so downstream checks like `NonNull(node)` / `Align(node, T)`
    // / `Allocated(node, ..)` can discharge against the real pointer instead of
    // a fresh unconstrained `aggregate` symbol.  The same transparent modelling
    // applies to value newtypes (`MaybeUninit<T>`, `ManuallyDrop<T>`) so that
    // `MaybeUninit::new(x).assume_init()` round-trips back to `x`.
    if operands.len() == 1
        && (state.find_nn_pointee(dest_ty).is_some() || state.is_transparent_newtype(dest_ty))
    {
        let operand = operands.iter().next().unwrap();
        let field_val = state.value_of_operand(operand);
        let dest_local = dest_place.local;
        state.set_field_value(dest_local, vec![0], field_val.clone());
        if let Some(source) = operand.place()
            && source.projection.is_empty()
        {
            let nested = state.field_paths(source.local).into_iter().filter_map(|path| {
                state.field_value(source.local, &path).cloned().map(|value| (path, value))
            }).collect::<Vec<_>>();
            for (path, value) in nested {
                let mut dest_path = vec![0];
                dest_path.extend(path);
                state.set_field_value(dest_local, dest_path, value);
            }
        }
        if let Some(alloc_id) = state.current_frame.local_alloc.get(&dest_local).copied() {
            state.content_mut(alloc_id).facts.initialized = true;
        }
        return VmValue {
            z3_term: field_val.z3_term,
            ty: dest_ty,
            provenance: field_val.provenance,
            facts: field_val.facts,
            source: ValueSource::None,
        };
    }
    let term = state.fresh_int("aggregate");
    let dest_local = dest_place.local;
    let dest_prefix = if dest_place.projection.iter().all(|projection| {
        matches!(projection.kind(), rustc_middle::mir::ProjectionElem::Field(..) | rustc_middle::mir::ProjectionElem::Downcast(..))
    }) {
        dest_place.projection.iter().filter_map(|projection| {
            match projection.kind() {
                rustc_middle::mir::ProjectionElem::Field(field, _) => Some(field.as_usize()),
                _ => None,
            }
        }).collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    // Prefer the pointee allocation (through a `*ptr` deref) over the base
    // local's own stack slot, so byte values land on the real buffer (e.g.
    // `((*_8).1).0 = [a, b, 0]` writes into the box).
    let dest_alloc_id = state
        .local_value(dest_local)
        .and_then(|v| v.provenance_alloc_id())
        .or_else(|| state.current_frame.local_alloc.get(&dest_local).copied());
    let is_byte_array = mir_utils::is_u8_array_or_slice(dest_ty);
    let field_types: Vec<_> = state.aggregate_field_tys(dest_ty);
    let mut byte_offset = 0usize;
    for (i, operand) in operands.iter().enumerate() {
        let mut field_val = state.value_of_operand(operand);
        let field_ty_opt = field_types.get(i).copied();
        if let Some(field_ty) = field_ty_opt {
            let src_is_ref = matches!(field_val.ty.kind(), rustc_middle::ty::TyKind::Ref(..));
            let dst_is_raw = matches!(field_ty.kind(), rustc_middle::ty::TyKind::RawPtr(..));
            if dst_is_raw && (src_is_ref || field_val.facts.non_null) {
                field_val.facts.in_bounds = true;
                field_val.ty = field_ty;
            }
        }
        let field_sz = field_ty_opt
            .map(|ty| state.size_of_ty(ty) as usize)
            .unwrap_or(1);
        let field_term = field_val.z3_term.clone();
        let mut field_path = dest_prefix.clone();
        field_path.push(i);
        state.set_field_value(dest_local, field_path.clone(), field_val);
        // Flatten a nested aggregate: if the operand is a local whose own fields
        // are tracked (e.g. `_0 = Result::Ok(_24)` where `_24 = RawVecInner { ptr:
        // _25, .. }`), expose the nested fields under the destination's field
        // path so a contract place like `Return.Field(0).Field(0)` can resolve to
        // `_25`.  Only flatten the data-carrying variant (`Ok`/`Some`); on
        // `Err`/`None` paths there is no `Self` and the nested place should
        // resolve to `Unknown`.
        if data_variant != Some(false)
            && let Some(op_place) = operand.place()
            && op_place.projection.is_empty()
        {
            let nested: Vec<(Vec<usize>, VmValue<'z3, 'tcx>)> = state
                .field_paths(op_place.local)
                .into_iter()
                .filter_map(|p| {
                    state
                        .field_value(op_place.local, &p)
                        .cloned()
                        .map(|v| (p, v))
                })
                .collect();
            for (nested_path, nested_val) in nested {
                let mut full = field_path.clone();
                full.extend_from_slice(&nested_path);
                state.set_field_value(dest_local, full, nested_val);
            }
        }
        if let Some(alloc_id) = dest_alloc_id {
            state.content_mut(alloc_id).facts.initialized = true;
            if is_byte_array && field_sz == 1 {
                state.record_byte_value(alloc_id, byte_offset, field_term.clone());
            }
            if let Some(int_val) = mir_utils::operand_const_u64(operand) {
                if field_sz == 1 {
                    if int_val == 0 {
                        if !is_byte_array {
                            state.record_byte_value(
                                alloc_id,
                                byte_offset,
                                Int::from_u64(state.z3_ctx, 0),
                            );
                        }
                    } else if !is_byte_array {
                        state.record_byte_value(
                            alloc_id,
                            byte_offset,
                            Int::from_u64(state.z3_ctx, int_val),
                        );
                    }
                }
                for b in 0..field_sz.min(8) {
                    let byte_off = byte_offset + b;
                    let byte_val = (int_val >> (b * 8)) & 0xFF;
                    state.record_byte_value(
                        alloc_id,
                        byte_off,
                        Int::from_u64(state.z3_ctx, byte_val),
                    );
                }
            }
        }
        byte_offset += field_sz;
    }
    // Fat-pointer construction (inlined `from_raw_parts` /
    // `slice_from_raw_parts_mut`): the result's address and provenance are those
    // of the data pointer (field 0), so downstream `Allocated`/`Owning` checks
    // on the slice resolve against the real buffer instead of a fresh `aggregate`
    // symbol.
    let is_slice_ptr = matches!(dest_ty.kind(),
        rustc_middle::ty::TyKind::RawPtr(inner, _) | rustc_middle::ty::TyKind::Ref(_, inner, _)
            if matches!(inner.kind(), rustc_middle::ty::TyKind::Slice(_)));
    let (result_term, result_prov) = if is_slice_ptr {
        match state.field_value(dest_local, &[0]).cloned() {
            Some(data) => (data.z3_term.clone(), data.provenance.clone()),
            None => (term.clone(), None),
        }
    } else {
        // `Box<T>` (an aggregate `Box(Unique<T>, A)`) takes its provenance from
        // the inner `Unique<T>.pointer` (`NonNull<T>` at path `[0, 0]`), which
        // the field-flattening above just recorded.  Without this,
        // `Box::assume_init`'s rebuild drops the heap provenance and a later
        // `Box::as_ptr` field read fails `NonNull`.
        let box_prov = if let rustc_middle::ty::TyKind::Adt(adt, _) = dest_ty.kind() {
            if api_classify::is_std_box(adt.did()) {
                state
                    .container_ptr_field(dest_ty)
                    .and_then(|path| state.field_value(dest_local, &path))
                    .and_then(|v| v.provenance.clone())
            } else {
                None
            }
        } else {
            None
        };
        (term.clone(), box_prov)
    };
    let source = match kind {
        rustc_middle::mir::AggregateKind::Adt(did, variant_idx, ..)
            if state.tcx.adt_def(*did).is_enum() =>
        {
            ValueSource::KnownDiscriminant(Int::from_u64(state.z3_ctx, variant_idx.as_usize() as u64))
        }
        _ => ValueSource::None,
    };
    VmValue {
        z3_term: result_term,
        ty: dest_ty,
        provenance: result_prov,
        facts: ValueFacts::default(),
        source,
    }
}

pub(crate) fn eval_discriminant<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    place: &Place<'tcx>,
) -> VmValue<'z3, 'tcx> {
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    // If the ADT's variant is known symbolically (e.g. `Iterator::next` returns
    // `Some` iff the iterator was non-empty), reuse that term so
    // `switchInt(discriminant)` branches stay tied to the real condition instead
    // of a fresh unconstrained symbol.
    let place_val = state
        .value_of_place(place)
        .or_else(|| state.local_value(place.local).cloned());
    let term = place_val
        .as_ref()
        .and_then(|v| v.discriminant().cloned())
        .unwrap_or_else(|| state.fresh_int("discriminant"));
    // For Ordering (repr i8, values: Less=-1 Equal=0 Greater=1), the
    // discriminant index equals the repr value + 1.  Connect the fresh
    // discriminant term to the ADT value so that SwitchInt constraints propagate
    // to the stored value.
    if let Some(ref pv) = place_val
        && let rustc_middle::ty::TyKind::Adt(adt_def, _) = pv.ty.kind()
        && api_classify::is_std_ordering(adt_def.did())
        && adt_def.is_enum()
    {
        let one = Int::from_u64(state.z3_ctx, 1);
        let discr_minus_one = Int::sub(state.z3_ctx, &[&term, &one]);
        state
            .constraints
            .assertions
            .push(pv.z3_term._eq(&discr_minus_one));
        let zero = Int::from_u64(state.z3_ctx, 0);
        let two = Int::from_u64(state.z3_ctx, 2);
        state.constraints.assertions.push(term.ge(&zero));
        state.constraints.assertions.push(term.le(&two));
    }
    let mut value = VmValue::new(term, dest_ty);
    if place_val.is_some_and(|value| matches!(value.source, ValueSource::KnownDiscriminant(_))) {
        value.source = ValueSource::KnownDiscriminant(value.z3_term.clone());
    }
    value
}

#[cfg(not(rapx_ge_99))]
pub(crate) fn eval_shallow_init_box<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    operand: &Operand<'tcx>,
) -> VmValue<'z3, 'tcx> {
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    let val = state.value_of_operand(operand);
    VmValue {
        z3_term: val.z3_term,
        ty: dest_ty,
        provenance: val.provenance,
        facts: val.facts,
        source: ValueSource::None,
    }
}

pub(crate) fn eval_copy_for_deref<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    place: &Place<'tcx>,
) -> VmValue<'z3, 'tcx> {
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    if let Some(val) = state.value_of_place(place) {
        val
    } else {
        let term = state.fresh_int("copy_for_deref");
        VmValue::new(term, dest_ty)
    }
}

pub(crate) fn eval_fresh_value<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    name: &str,
) -> VmValue<'z3, 'tcx> {
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    let term = state.fresh_int(name);
    VmValue::new(term, dest_ty)
}

pub(crate) fn eval_thread_local_ref<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    def_id: DefId,
) -> VmValue<'z3, 'tcx> {
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    let Some(static_ty) = mir_utils::pointee_ty(dest_ty) else {
        state.unsupported_mir = true;
        return eval_fresh_value(state, dest_place, "thread_local");
    };
    let scalar = matches!(
        static_ty.kind(),
        TyKind::Int(_) | TyKind::Uint(_) | TyKind::Bool | TyKind::Char
    );
    let bytes = if scalar && !state.tcx.is_mutable_static(def_id) {
        state
            .tcx
            .eval_static_initializer(def_id)
            .ok()
            .map(|allocation| {
                let allocation = allocation.inner();
                allocation
                    .inspect_with_uninit_and_ptr_outside_interpreter(0..allocation.len())
                    .to_vec()
            })
    } else {
        None
    };
    let size = state.size_of_ty(static_ty);
    if let Some(bytes) = bytes
        && size > 0
        && size <= 8
        && bytes.len() == size as usize
    {
        let value = if state.tcx.data_layout.endian == rustc_abi::Endian::Little {
            bytes
                .iter()
                .rev()
                .fold(0_u64, |value, byte| (value << 8) | u64::from(*byte))
        } else {
            bytes
                .iter()
                .fold(0_u64, |value, byte| (value << 8) | u64::from(*byte))
        };
        let align = state.align_sym(static_ty);
        let (alloc_id, base) =
            state.allocate(Int::from_u64(state.z3_ctx, size), align, Some(static_ty));
        state.content_mut(alloc_id).facts.initialized = true;
        let scalar_value = VmValue::new(Int::from_u64(state.z3_ctx, value), static_ty);
        state
            .content_mut(alloc_id)
            .values
            .insert((static_ty, vec![]), scalar_value);
        return VmValue {
            z3_term: base,
            ty: dest_ty,
            provenance: Some(Provenance {
                alloc_id,
                offset: Int::from_u64(state.z3_ctx, 0),
                offset_kind: None,
            }),
            facts: ValueFacts {
                non_null: true,
                init: true,
                in_bounds: true,
                ..Default::default()
            },
            source: ValueSource::None,
        };
    }
    state.unsupported_mir = true;
    eval_fresh_value(state, dest_place, "thread_local")
}

pub(crate) fn eval_repeat<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    operand: &Operand<'tcx>,
) -> VmValue<'z3, 'tcx> {
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    let TyKind::Array(_, length) = dest_ty.kind() else {
        state.unsupported_mir = true;
        return eval_fresh_value(state, dest_place, "repeat");
    };
    if length.try_to_target_usize(state.tcx).is_none() {
        state.unsupported_mir = true;
        return eval_fresh_value(state, dest_place, "repeat");
    }
    let value = state.value_of_operand(operand);
    let mut field_path = Vec::new();
    for projection in dest_place.projection.iter() {
        let index = match projection {
            rustc_middle::mir::ProjectionElem::Field(index, _) => index.as_usize(),
            rustc_middle::mir::ProjectionElem::Index(local) => {
                let Some(index) = state.local_value(local)
                    .and_then(|value| value.z3_term.simplify().as_u64())
                    .and_then(|index| usize::try_from(index).ok()) else {
                    state.unsupported_mir = true;
                    return eval_fresh_value(state, dest_place, "repeat");
                };
                index
            }
            rustc_middle::mir::ProjectionElem::ConstantIndex { offset, from_end: false, .. } => offset as usize,
            _ => {
                state.unsupported_mir = true;
                return eval_fresh_value(state, dest_place, "repeat");
            }
        };
        field_path.push(index);
    }
    if let Some(alloc_id) = state
        .current_frame
        .local_alloc
        .get(&dest_place.local)
        .copied()
    {
        let view_ty = state.body().local_decls[dest_place.local].ty;
        state.content_mut(alloc_id).values.retain(|(ty, path), _| {
            *ty != view_ty || path.len() <= field_path.len() || !path.starts_with(&field_path)
        });
    }
    field_path.push(REPEATED_ARRAY_ELEMENT);
    state.set_field_value(dest_place.local, field_path.clone(), value);
    if let Some(source) = operand.place()
        && source.projection.is_empty()
    {
        let nested = state.field_paths(source.local)
            .into_iter()
            .filter_map(|path| {
                state.field_value(source.local, &path).cloned().map(|value| (path, value))
            })
            .collect::<Vec<_>>();
        for (path, value) in nested {
            let mut full = field_path.clone();
            full.extend(path);
            state.set_field_value(dest_place.local, full, value);
        }
    }
    eval_fresh_value(state, dest_place, "repeat")
}

pub(crate) fn eval_wrap_unsafe_binder<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    operand: &Operand<'tcx>,
) -> VmValue<'z3, 'tcx> {
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    let mut value = state.value_of_operand(operand);
    value.ty = dest_ty;
    value
}

#[cfg(not(rapx_ge_95))]
pub(crate) fn eval_nullary_op<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    op: &impl std::fmt::Debug,
) -> VmValue<'z3, 'tcx> {
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    let term = state.fresh_int("nullary");
    let op_debug = format!("{:?}", op);
    let is_align_of = op_debug.contains("AlignOf") || op_debug.contains("min_align_of");
    let is_size_of = op_debug.contains("SizeOf");
    if is_align_of || is_size_of {
        let one = Int::from_u64(state.z3_ctx, 1);
        state.constraints.assertions.push(term.ge(&one));
    }
    VmValue::new(term, dest_ty)
}

#[cfg(rapx_rvalue_has_reborrow)]
pub(crate) fn eval_reborrow<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    source_place: &Place<'tcx>,
) -> VmValue<'z3, 'tcx> {
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    let source_ty = source_place.ty(state.body(), state.tcx).ty;
    let same_adt = matches!(
        (source_ty.kind(), dest_ty.kind()),
        (rustc_middle::ty::TyKind::Adt(source, _), rustc_middle::ty::TyKind::Adt(dest, _))
            if source.did() == dest.did()
    );
    #[cfg(rapx_has_phantom_deref)]
    let has_phantom_deref = source_place.projection.iter().any(|projection| {
        matches!(
            projection.kind(),
            rustc_middle::mir::ProjectionElem::PhantomDeref
        )
    });
    #[cfg(not(rapx_has_phantom_deref))]
    let has_phantom_deref = false;
    if !same_adt || has_phantom_deref {
        state.unsupported_mir = true;
        return eval_fresh_value(state, dest_place, "reborrow");
    }
    let mut value = state
        .value_of_place(source_place)
        .unwrap_or_else(|| eval_fresh_value(state, dest_place, "reborrow"));
    value.ty = dest_ty;
    value
}

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// Compute provenance for a binary operation on pointer values.
    /// Propagates provenance with adjusted offset for pointer arithmetic
    /// (`ptr + offset`, `ptr - offset`, `Offset`).
    fn provenance_for_binary_op(
        &self,
        op: BinOp,
        lhs: &VmValue<'z3, 'tcx>,
        rhs: &VmValue<'z3, 'tcx>,
    ) -> Option<Provenance<'z3>> {
        if rhs.is_pointer() && !matches!(op, BinOp::Div | BinOp::Rem) {
            return None;
        }
        match op {
            BinOp::Add | BinOp::AddWithOverflow | BinOp::AddUnchecked | BinOp::Offset => {
                lhs.provenance.as_ref().map(|prov| Provenance {
                    alloc_id: prov.alloc_id,
                    offset: Int::add(self.z3_ctx, &[&prov.offset, &rhs.z3_term]),
                    offset_kind: None,
                })
            }
            BinOp::Sub | BinOp::SubWithOverflow | BinOp::SubUnchecked => {
                lhs.provenance.as_ref().map(|prov| Provenance {
                    alloc_id: prov.alloc_id,
                    offset: Int::sub(self.z3_ctx, &[&prov.offset, &rhs.z3_term]),
                    offset_kind: None,
                })
            }
            BinOp::BitAnd => {
                lhs.provenance.as_ref().map(|prov| Provenance {
                    alloc_id: prov.alloc_id,
                    // Alignment rounding changes the intra-allocation offset
                    // unpredictably; use a fresh symbolic offset constrained
                    // by the BitAnd path conditions emitted in eval_binary_op.
                    offset: self.fresh_int("align_offset"),
                    offset_kind: None,
                })
            }
            BinOp::BitXor | BinOp::Shr | BinOp::ShrUnchecked => lhs.provenance.clone(),
            BinOp::BitOr | BinOp::Shl | BinOp::ShlUnchecked => {
                lhs.provenance.as_ref().map(|prov| Provenance {
                    alloc_id: prov.alloc_id,
                    offset: Int::add(self.z3_ctx, &[&prov.offset, &rhs.z3_term]),
                    offset_kind: None,
                })
            }
            BinOp::Mul | BinOp::MulWithOverflow | BinOp::MulUnchecked => {
                lhs.provenance.as_ref().map(|prov| Provenance {
                    alloc_id: prov.alloc_id,
                    offset: Int::mul(self.z3_ctx, &[&prov.offset, &rhs.z3_term]),
                    offset_kind: None,
                })
            }
            BinOp::Div | BinOp::Rem => lhs.provenance.clone(),
            _ => None,
        }
    }

    /// Compute facts for a binary operation.
    /// Propagates non_null from pointer arithmetic and align_n from compatible ops.
    fn facts_for_binary_op(
        &self,
        op: BinOp,
        lhs: &VmValue<'z3, 'tcx>,
        rhs: &VmValue<'z3, 'tcx>,
        provenance: &Option<Provenance<'z3>>,
    ) -> ValueFacts<'z3> {
        // A bitwise AND may clear the low bits entirely (`ptr & mask == 0` for a
        // small/aligned-to-zero pointer), so the result is not guaranteed
        // non-null even when the lhs pointer is.  Other pointer arithmetic
        // (`add`/`sub`/`offset`) preserves non-nullness under the VM's
        // no-wrap assumption.
        let non_null = !matches!(op, BinOp::BitAnd) && provenance.is_some() && lhs.facts.non_null;

        let align_n = match op {
            BinOp::Add
            | BinOp::AddWithOverflow
            | BinOp::AddUnchecked
            | BinOp::Sub
            | BinOp::SubWithOverflow
            | BinOp::SubUnchecked
            | BinOp::Offset => {
                match (&lhs.facts.align_n, &rhs.facts.align_n) {
                    (Some(a), Some(b)) if a == b => Some(a.clone()),
                    (Some(a), None) => match a.simplify().as_u64() {
                        Some(au) => {
                            let c = rhs.z3_term.as_u64().unwrap_or(1);
                            if c.is_multiple_of(au) {
                                Some(a.clone())
                            } else {
                                None
                            }
                        }
                        // Symbolic alignment: only a zero RHS is a guaranteed
                        // multiple of `align_T`.
                        None => {
                            if rhs.z3_term.as_u64() == Some(0) {
                                Some(a.clone())
                            } else {
                                None
                            }
                        }
                    },
                    (Some(a), _) if self.rhs_is_aligned_multiple(rhs, a) => Some(a.clone()),
                    _ => None,
                }
            }
            BinOp::Mul | BinOp::MulWithOverflow | BinOp::MulUnchecked => match rhs.z3_term.as_u64()
            {
                Some(c) => pow2_factor(c).map(|p| Int::from_u64(self.z3_ctx, p)),
                None => lhs
                    .z3_term
                    .as_u64()
                    .and_then(pow2_factor)
                    .map(|p| Int::from_u64(self.z3_ctx, p)),
            },
            _ => lhs.facts.align_n.clone(),
        };

        ValueFacts {
            non_null,
            align_n,
            ..Default::default()
        }
    }

    /// Check if a value is known to be a multiple of `align` (e.g. the result
    /// of a Mul by a constant factor of `align`).
    fn rhs_is_aligned_multiple(&self, val: &VmValue<'z3, 'tcx>, align: &Int<'z3>) -> bool {
        if let Some(au) = align.simplify().as_u64() {
            if let Some(a) = val
                .facts
                .align_n
                .as_ref()
                .and_then(|a| a.simplify().as_u64())
                && a >= au
                && a % au == 0
            {
                return true;
            }
            if let Some(c) = val.z3_term.as_u64()
                && c % au == 0
            {
                return true;
            }
        }
        false
    }
}

/// Largest power-of-two factor of a non-negative constant (the alignment
/// implied by multiplying by `c`): `c` itself if it is a power of two,
/// otherwise `2^trailing_zeros(c)`.
fn pow2_factor(c: u64) -> Option<u64> {
    if c > 0 && c.is_power_of_two() {
        Some(c)
    } else if c > 0 {
        let factor = 1u64 << c.trailing_zeros();
        if factor > 1 { Some(factor) } else { None }
    } else {
        None
    }
}
