//! API call and type classification helpers.
//!
//! Each classifier answers "what kind of operation is this call?" (pointer
//! arithmetic, raw memory access, ownership transfer, …). Callers — the path
//! graph, VM, alias/hazard scanner, and call-summary registry — use these to pick
//! a modelling strategy or discharge a safety obligation.
//!
//! # Matching mechanism
//!
//! Most classifiers match callees or ADT types by `DefId`, using identities
//! from [`crate::def_ids::intrinsic_api`],
//! [`crate::def_ids::nomir_ffi`], [`crate::def_ids::other_api`], and
//! [`crate::def_ids::type_ids`].

use crate::def_ids::{
    intrinsic_api,
    lang_api::{self, LangItem},
    nomir_ffi, other_api, type_ids,
};
use crate::verify::pointer_origin;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::Operand,
    ty::{Mutability, Ty, TyCtxt, TyKind},
};

fn intrinsic_named(callee: Option<DefId>, names: &[&str]) -> bool {
    intrinsic_api::name(callee).is_some_and(|name| names.contains(&name.as_str()))
}

/// Recognize a mutating Range call that returns an optional element.
pub(crate) fn is_range_advancing_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    func: &Operand<'tcx>,
) -> bool {
    let Some(callee) = crate::helpers::mir_utils::dep_callee_resolved_def_id(tcx, caller, func)
    else {
        return false;
    };
    let sig = tcx.fn_sig(callee).skip_binder();
    let inputs = sig.inputs().skip_binder();
    let range_owner = crate::helpers::name::get_struct_self_ty(tcx, callee).is_some_and(|ty| {
        matches!(ty.kind(), TyKind::Adt(adt, _)
            if lang_api::matches(tcx, adt.did(), LangItem::Range)
                || lang_api::matches(tcx, adt.did(), LangItem::RangeInclusiveStruct))
    });
    inputs.len() == 1
        && matches!(
            inputs.first().map(|ty| ty.kind()),
            Some(TyKind::Ref(_, _, Mutability::Mut))
        )
        && range_owner
        && matches!(
            sig.output().skip_binder().kind(),
            TyKind::Adt(adt, _) if tcx.is_diagnostic_item(rustc_span::sym::Option, adt.did())
        )
        && crate::verify::call_summary::callsite_write_args(tcx, caller, func)
            .is_some_and(|args| args.contains(&0))
}

pub(crate) fn is_std_box_value_constructor(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    let Some(impl_id) = tcx.inherent_impl_of_assoc(callee) else {
        return false;
    };
    let self_ty = tcx.type_of(impl_id).instantiate_identity();
    #[cfg(rapx_ge_99)]
    let self_ty = self_ty.skip_norm_wip();
    let TyKind::Adt(adt, args) = self_ty.kind() else {
        return false;
    };
    if !is_std_box(adt.did()) {
        return false;
    }
    let Some(pointee) = args.first().and_then(|arg| arg.as_type()) else {
        return false;
    };
    let sig = tcx.fn_sig(callee).skip_binder();
    let output = sig.output().skip_binder();
    matches!(output.kind(), TyKind::Adt(def, output_args)
        if def.did() == adt.did()
            && output_args.first().and_then(|arg| arg.as_type()) == Some(pointee))
        && sig.inputs().skip_binder().first() == Some(&pointee)
}

/// Whether `callee` is `ManuallyDrop::<T>::drop` — the *manual* drop that frees
/// the pointee's allocation without the `ManuallyDrop` wrapper's own (no-op)
/// drop glue.
pub fn is_manually_drop_drop(callee: Option<DefId>) -> bool {
    callee.is_some_and(|c| other_api::manually_drop() == Some(c))
}

/// Whether `callee` is `std::mem::drop` / `core::mem::drop`.
pub fn is_std_drop(callee: Option<DefId>) -> bool {
    callee.is_some_and(|c| other_api::drop() == Some(c))
}

// ── Pointer extraction / cast ─────────────────────────────────────

/// Whether `callee` produces a raw pointer (or `NonNull`) alias of its first
/// argument: `as_ptr`/`as_mut_ptr`, `into_raw`, and pointer `cast` (incl.
/// `cast_mut`/`cast_const`). `as_ptr_range`/`as_mut_ptr_range` are excluded
/// because they return a `Range` of two pointers rather than a single pointer;
/// `NonNull::new_unchecked` constructs a wrapper from a pointer; `as_ref` and
/// `as_mut` produce references. None extracts a raw pointer from its argument.
/// Other pointer-returning calls are recognized from their MIR.
pub fn is_as_ptr(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[
            other_api::const_ptr_slice_as_ptr(),
            other_api::mut_ptr_slice_as_mut_ptr(),
            other_api::const_ptr_cast(),
            other_api::const_ptr_cast_mut(),
            other_api::const_ptr_cast_array(),
            other_api::mut_ptr_cast(),
            other_api::mut_ptr_cast_const(),
            other_api::mut_ptr_cast_array(),
            other_api::nonnull_cast(),
        ],
    ) || callee
        .is_some_and(|id| crate::verify::pointer_origin::return_source_arg(tcx, id) == Some(0))
}

// ── Pointer arithmetic ────────────────────────────────────────────
// Direction (`add` vs `sub`) and granularity (`element` vs `byte`) are two
// orthogonal axes. Each of the four combinations is a first-class classifier
// below; the aggregate predicates at the end are unions over a single axis,
// for callers that only care about one dimension.

/// Element-strided `add`/`wrapping_add` and signed `offset`/`wrapping_offset`
/// (stride = `size_of::<T>()`). `offset_from`/`offset_from_unsigned` are *not*
/// matched (they subtract two pointers into an `isize`).
fn is_element_ptr_add(callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[
            other_api::const_ptr_add(),
            other_api::const_ptr_wrapping_add(),
            other_api::const_ptr_offset(),
            other_api::const_ptr_wrapping_offset(),
            other_api::mut_ptr_add(),
            other_api::mut_ptr_wrapping_add(),
            other_api::mut_ptr_offset(),
            other_api::mut_ptr_wrapping_offset(),
            other_api::nonnull_add(),
            other_api::nonnull_offset(),
        ],
    )
}

/// Element-strided `sub`/`wrapping_sub` (stride = `size_of::<T>()`).
fn is_element_ptr_sub(callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[
            other_api::const_ptr_sub(),
            other_api::const_ptr_wrapping_sub(),
            other_api::mut_ptr_sub(),
            other_api::mut_ptr_wrapping_sub(),
            other_api::nonnull_sub(),
        ],
    )
}

/// Byte-granular `byte_add`/`wrapping_byte_add` and signed
/// `byte_offset`/`wrapping_byte_offset` (stride 1).
fn is_byte_ptr_add(callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[
            other_api::const_ptr_byte_add(),
            other_api::const_ptr_wrapping_byte_add(),
            other_api::const_ptr_byte_offset(),
            other_api::const_ptr_wrapping_byte_offset(),
            other_api::mut_ptr_byte_add(),
            other_api::mut_ptr_wrapping_byte_add(),
            other_api::mut_ptr_byte_offset(),
            other_api::mut_ptr_wrapping_byte_offset(),
            other_api::nonnull_byte_add(),
            other_api::nonnull_byte_offset(),
        ],
    )
}

/// Byte-granular `byte_sub`/`wrapping_byte_sub` (stride 1).
fn is_byte_ptr_sub(callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[
            other_api::const_ptr_byte_sub(),
            other_api::const_ptr_wrapping_byte_sub(),
            other_api::mut_ptr_byte_sub(),
            other_api::mut_ptr_wrapping_byte_sub(),
            other_api::nonnull_byte_sub(),
        ],
    )
}

/// Any pointer `add` (element or byte). `offset`/`byte_offset` take a signed
/// `isize`, so a negative offset is still classified here (the sign lives in
/// the argument); see [`is_pointer_sub`] for the positive-count `sub` family.
pub fn is_pointer_add(callee: Option<DefId>) -> bool {
    is_element_ptr_add(callee) || is_byte_ptr_add(callee)
}

/// Any pointer `sub` (element or byte): a positive count, `base - count * stride`.
pub fn is_pointer_sub(callee: Option<DefId>) -> bool {
    is_element_ptr_sub(callee) || is_byte_ptr_sub(callee)
}

fn is_intrinsic_copy(callee: Option<DefId>) -> bool {
    intrinsic_named(callee, &["copy", "copy_nonoverlapping"])
}

pub fn is_intrinsic_ptr_offset_from(callee: Option<DefId>) -> bool {
    intrinsic_named(callee, &["ptr_offset_from", "ptr_offset_from_unsigned"])
}

// ── Layout constants ──────────────────────────────────────────────

/// Whether `callee` is the compile-time layout constant `size_of::<T>()` or
/// `align_of::<T>()`. The runtime intrinsics (`size_of_val`, `align_of_val`,
/// `pref_align_of`, `*_val_raw`, …) are *not* classified here.
pub fn is_layout_constant(callee: Option<DefId>) -> bool {
    is_intrinsic_layout_constant(callee) || is_mem_layout_constant(callee)
}

fn is_intrinsic_layout_constant(callee: Option<DefId>) -> bool {
    intrinsic_named(callee, &["size_of", "align_of"])
}

pub fn is_mem_layout_constant(callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[other_api::mem_size_of(), other_api::mem_align_of()],
    )
}

/// Whether `callee` is `ptr::align_offset` / `NonNull::align_offset` /
/// `*const T::align_offset` / `*mut T::align_offset`.
pub fn is_align_offset(callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[
            other_api::ptr_align_offset(),
            other_api::nonnull_align_offset(),
            other_api::const_ptr_align_offset(),
            other_api::mut_ptr_align_offset(),
        ],
    )
}

// ── Raw pointer read / write ──────────────────────────────────────

/// Whether `callee` writes through a raw pointer to its first argument
/// (`ptr::write`, `write_bytes`, `write_unaligned`, `write_volatile`).
pub fn is_ptr_write(callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[
            other_api::ptr_write(),
            other_api::ptr_write_unaligned(),
            other_api::ptr_write_volatile(),
            other_api::ptr_write_bytes(),
        ],
    )
}

pub fn is_ptr_copy(callee: Option<DefId>) -> bool {
    is_intrinsic_copy(callee)
        || other_api::matches_any(
            callee,
            &[other_api::ptr_copy(), other_api::ptr_copy_nonoverlapping()],
        )
}

/// Whether `callee` reads through a raw pointer or copies memory
/// (`ptr::read`/`read_unaligned`/`read_volatile`, `copy_to`/`copy_from`,
/// `MaybeUninit::assume_init_read`, and intrinsics `copy`/`copy_nonoverlapping`).
pub fn is_ptr_read(callee: Option<DefId>) -> bool {
    is_intrinsic_copy(callee)
        || other_api::matches_any(
            callee,
            &[
                other_api::ptr_read(),
                other_api::ptr_read_unaligned(),
                other_api::ptr_read_volatile(),
                other_api::copy_to(),
                other_api::copy_to_nonoverlapping(),
                other_api::copy_from(),
                other_api::copy_from_nonoverlapping(),
                other_api::assume_init_read(),
            ],
        )
}

/// Copy/write operations that do not require initialized destination bytes:
/// intrinsic `copy`/`copy_nonoverlapping`, pointer `copy_to_nonoverlapping`/
/// `copy_from_nonoverlapping`, `write`, and `write_bytes`. Used by the checker
/// for `Init`/`Typed` obligations on `MaybeUninit` targets.
pub fn is_mem_copy_or_write(callee: Option<DefId>) -> bool {
    is_intrinsic_copy(callee)
        || other_api::matches_any(
            callee,
            &[
                other_api::copy_from_nonoverlapping(),
                other_api::copy_to_nonoverlapping(),
                other_api::ptr_write(),
                other_api::ptr_write_bytes(),
            ],
        )
}

// ── Slice / C-string ──────────────────────────────────────────────

/// `_unchecked` C-string constructors whose caller must guarantee NUL
/// termination (`CStr::from_bytes_with_nul_unchecked`,
/// `CString::from_vec_with_nul_unchecked`).
pub fn is_cstr_unchecked_constructor(callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[
            other_api::cstr_from_bytes_with_nul_unchecked(),
            nomir_ffi::cstring_from_vec_with_nul_unchecked(),
        ],
    )
}

// ── Vec constructors / methods ────────────────────────────────────

pub fn is_vec_push_or_reserve(callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[
            other_api::vec_push(),
            other_api::vec_reserve(),
            other_api::vec_reserve_exact(),
        ],
    )
}
// ── Alias-hazard classification ───────────────────────────────────
// Ref-counted reconstruction retains a dedicated rule until the alias model
// accounts for shared ownership and clone counts.
pub fn is_ref_counted_from_raw(callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[
            other_api::arc_from_raw(),
            other_api::rc_from_raw(),
            other_api::arc_from_raw_in(),
            other_api::rc_from_raw_in(),
        ],
    )
}

/// Whether `callee` is `NonNull::as_ref` or `NonNull::as_mut`.
pub fn is_nonnull_as_ref_as_mut(callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[other_api::nonnull_as_ref(), other_api::nonnull_as_mut()],
    )
}

/// Whether `callee` is `NonNull::as_mut` (produces an exclusive `&mut`).
pub fn is_nonnull_as_mut(callee: Option<DefId>) -> bool {
    other_api::matches_any(callee, &[other_api::nonnull_as_mut()])
}

/// Whether `callee` mutates a `Vec` in a way relevant to outstanding
/// raw-pointer views (including length changes, element moves, and reallocation).
pub fn is_vec_invalidating_method(callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[
            other_api::vec_push(),
            other_api::vec_reserve(),
            other_api::vec_reserve_exact(),
            other_api::vec_shrink_to_fit(),
            other_api::vec_shrink_to(),
            other_api::vec_insert(),
            other_api::vec_remove(),
            other_api::vec_clear(),
            other_api::vec_truncate(),
            other_api::vec_set_len(),
        ],
    )
}

/// Whether `callee` returns ownership of an allocation as a raw pointer
/// (`Box::into_raw`, `CString::into_raw`, `Arc::into_raw`, `Rc::into_raw`, ...).
pub fn is_ownership_return(callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[
            other_api::box_into_raw(),
            other_api::cstring_into_raw(),
            other_api::arc_into_raw(),
            other_api::rc_into_raw(),
        ],
    )
}

/// Whether `callee` is a benign, read-only use of a raw-pointer origin
/// (`len`, `is_empty`, `is_null`, `addr`, `as_ptr`/`as_mut_ptr`, `cast`).
pub fn is_benign_origin_use(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[
            other_api::const_ptr_is_null(),
            other_api::const_ptr_addr(),
            other_api::const_ptr_cast(),
            other_api::const_ptr_cast_mut(),
            other_api::const_ptr_slice_is_empty(),
            other_api::const_ptr_slice_len(),
            other_api::const_ptr_slice_as_ptr(),
            other_api::mut_ptr_is_null(),
            other_api::mut_ptr_addr(),
            other_api::mut_ptr_cast(),
            other_api::mut_ptr_cast_const(),
            other_api::mut_ptr_slice_is_empty(),
            other_api::mut_ptr_slice_len(),
            other_api::mut_ptr_slice_as_mut_ptr(),
            other_api::nonnull_addr(),
            other_api::nonnull_cast(),
            other_api::nonnull_slice_is_empty(),
            other_api::nonnull_slice_len(),
            other_api::slice_len(),
            other_api::slice_is_empty(),
            other_api::str_len(),
            other_api::str_is_empty(),
            other_api::vec_len(),
            other_api::vec_is_empty(),
            other_api::string_len(),
            other_api::string_is_empty(),
            other_api::cstr_is_empty(),
        ],
    ) || callee.is_some_and(|did| pointer_origin::is_read_only_return(tcx, did))
}

// ── ADT type-name classifiers ─────────────────────────────────────
// *Shape* recognizers used by the VM to model repr(transparent) wrappers and
// fixed field layouts (`Vec` = ptr/cap/len, `slice::Iter` = ptr/end, …).
// Matched by `DefId` (resolved in [`crate::def_ids::type_ids`]).

pub fn is_std_vec(def_id: DefId) -> bool {
    type_ids::vec_types().contains(&def_id)
}
pub fn is_std_string(def_id: DefId) -> bool {
    type_ids::string_types().contains(&def_id)
}
pub fn is_std_box(def_id: DefId) -> bool {
    type_ids::box_types().contains(&def_id)
}
pub fn is_std_cstring(def_id: DefId) -> bool {
    type_ids::cstring_types().contains(&def_id)
}
pub fn is_std_nonnull(def_id: DefId) -> bool {
    type_ids::nonnull_types().contains(&def_id)
}
pub fn is_maybe_uninit_type(def_id: DefId) -> bool {
    type_ids::maybe_uninit_types().contains(&def_id)
}

/// Whether `ty` (peeling through `&` / `*mut` / `*const` / `[T]` / `[T; N]`) is
/// `MaybeUninit<...>`, i.e. carries no validity invariant (any bit pattern is a
/// valid value).  Shared by the VM (`init_parameters`) and the `Typed` checker.
pub fn is_maybe_uninit_ty(ty: Ty<'_>) -> bool {
    let mut t = ty;
    loop {
        match t.kind() {
            TyKind::Slice(e) | TyKind::Array(e, _) => t = *e,
            TyKind::RawPtr(e, _) | TyKind::Ref(_, e, _) => t = *e,
            TyKind::Adt(adt, _) => return is_maybe_uninit_type(adt.did()),
            _ => return false,
        }
    }
}
pub fn is_std_iter_or_itermut(def_id: DefId) -> bool {
    type_ids::iter_types().contains(&def_id)
}

pub fn is_std_ordering(def_id: DefId) -> bool {
    type_ids::ordering_types().contains(&def_id)
}

/// Whether `def_id` is `core::ops::index_range::IndexRange`.
pub fn is_index_range(def_id: DefId) -> bool {
    type_ids::index_range_types().contains(&def_id)
}
