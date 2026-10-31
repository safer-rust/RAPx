//! Standard-library API call classification helpers.
//!
//! Each classifier answers "what kind of operation is this call?" (pointer
//! arithmetic, raw memory access, ownership transfer, …). Callers — the path
//! graph, VM, alias/hazard scanner, and call-summary registry — use these to pick
//! a modelling strategy or discharge a safety obligation.
//!
//! # Matching mechanism
//!
//! Every classifier takes a `DefId` — `fn(Option<DefId>) -> bool` for callee
//! matching, or `fn(DefId) -> bool` for ADT *type* matching — and answers via
//! exact identities from [`crate::def_ids::intrinsic_api`],
//! [`crate::def_ids::nomir_ffi`], [`crate::def_ids::other_api`], and
//! [`crate::def_ids::type_ids`]. Some standard-library method sets in
//! `other_api` are collected by name patterns before being matched by `DefId`.

use crate::def_ids::intrinsic_api;
use crate::def_ids::nomir_ffi;
use crate::def_ids::other_api;
use crate::def_ids::type_ids;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::Ty;

/// Whether `callee` is `Some` and matches any resolved DefId in the slice.
fn any_def(callee: Option<DefId>, defs: &[DefId]) -> bool {
    callee.is_some_and(|c| defs.contains(&c))
}

// ── Ownership reconstruction ──────────────────────────────────────

/// Whether `callee` reconstructs an owned value, taking ownership of the
/// pointed-to memory: from a single raw pointer (`Box::from_raw`,
/// `CString::from_raw`, `Arc::from_raw`, `Rc::from_raw`) or from a `Vec<u8>`
/// (`CString::from_vec_with_nul_unchecked`). Distinct from
/// [`is_from_raw_parts`], which builds a slice/`Vec` from `(ptr, len[, cap])`.
pub fn is_ownership_reconstruction(callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[
            other_api::box_from_raw(),
            nomir_ffi::cstring_from_raw(),
            other_api::arc_from_raw(),
            other_api::rc_from_raw(),
            other_api::box_from_raw_in(),
            other_api::arc_from_raw_in(),
            other_api::rc_from_raw_in(),
            nomir_ffi::cstring_from_vec_with_nul_unchecked(),
        ],
    )
}

/// Whether `callee` is `ManuallyDrop::<T>::drop` — the *manual* drop that frees
/// the pointee's allocation without the `ManuallyDrop` wrapper's own (no-op)
/// drop glue.
pub fn is_manually_drop_drop(callee: Option<DefId>) -> bool {
    callee.is_some_and(|c| other_api::manually_drop() == Some(c))
}

/// Whether `callee` is `std::mem::drop` / `core::mem::drop` — the value drop
/// that frees the argument's heap allocation.
pub fn is_std_drop(callee: Option<DefId>) -> bool {
    callee.is_some_and(|c| other_api::drop() == Some(c))
}

/// Whether `callee` is `drop_in_place::<T>` — the MIR drop shim that drops the
/// pointee in place and (for an owning pointee like `Box`/`Vec`) frees its
/// heap allocation.
pub fn is_drop_in_place(callee: Option<DefId>) -> bool {
    callee.is_some_and(|c| other_api::drop_in_place() == Some(c))
}

// ── Pointer extraction / cast ─────────────────────────────────────

/// Whether `callee` produces a raw pointer (or `NonNull`) alias of its first
/// argument: `as_ptr`/`as_mut_ptr`, `into_raw`, and pointer `cast` (incl.
/// `cast_mut`/`cast_const`). `as_ptr_range`/`as_mut_ptr_range` are excluded
/// because they return a `Range` of two pointers rather than a single pointer;
/// `NonNull::new_unchecked`/`as_ref`/`as_mut` are excluded because they do not
/// produce a raw pointer (and `new_unchecked` must not mark its result
/// non-null, or it would hide `new_unchecked(null)` unsoundness).
pub fn is_as_ptr(callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[
            other_api::slice_as_ptr(),
            other_api::slice_as_mut_ptr(),
            other_api::str_as_ptr(),
            other_api::str_as_mut_ptr(),
            other_api::vec_as_ptr(),
            other_api::vec_as_mut_ptr(),
            other_api::cstr_as_ptr(),
            other_api::nonnull_as_ptr(),
            other_api::const_ptr_slice_as_ptr(),
            other_api::mut_ptr_slice_as_mut_ptr(),
            other_api::nonnull_slice_as_mut_ptr(),
            other_api::box_as_ptr(),
            other_api::box_as_mut_ptr(),
            other_api::maybe_uninit_as_ptr(),
            other_api::maybe_uninit_as_mut_ptr(),
            other_api::arc_as_ptr(),
            other_api::rc_as_ptr(),
            other_api::const_ptr_cast(),
            other_api::const_ptr_cast_mut(),
            other_api::const_ptr_cast_array(),
            other_api::mut_ptr_cast(),
            other_api::mut_ptr_cast_const(),
            other_api::mut_ptr_cast_array(),
            other_api::nonnull_cast(),
            other_api::box_into_raw(),
            other_api::cstring_into_raw(),
            other_api::arc_into_raw(),
            other_api::rc_into_raw(),
        ],
    )
}

// ── Pointer arithmetic ────────────────────────────────────────────
// Direction (`add` vs `sub`) and granularity (`element` vs `byte`) are two
// orthogonal axes. Each of the four combinations is a first-class classifier
// below; the aggregate predicates at the end are unions over a single axis,
// for callers that only care about one dimension.

/// Element-strided `add`/`wrapping_add` and signed `offset`/`wrapping_offset`
/// (stride = `size_of::<T>()`). `offset_from`/`offset_from_unsigned` are *not*
/// matched (they subtract two pointers into an `isize`).
pub(crate) fn is_element_ptr_add(callee: Option<DefId>) -> bool {
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
pub(crate) fn is_element_ptr_sub(callee: Option<DefId>) -> bool {
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
pub(crate) fn is_byte_ptr_add(callee: Option<DefId>) -> bool {
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
pub(crate) fn is_byte_ptr_sub(callee: Option<DefId>) -> bool {
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

pub fn is_intrinsic_copy(callee: Option<DefId>) -> bool {
    intrinsic_api::is_copy(callee) || intrinsic_api::is_copy_nonoverlapping(callee)
}

pub fn is_intrinsic_ptr_offset_from(callee: Option<DefId>) -> bool {
    intrinsic_api::is_ptr_offset_from(callee) || intrinsic_api::is_ptr_offset_from_unsigned(callee)
}

pub fn is_intrinsic_branch_hint(callee: Option<DefId>) -> bool {
    intrinsic_api::is_unlikely(callee) || intrinsic_api::is_likely(callee)
}

pub fn is_intrinsic_with_overflow(callee: Option<DefId>) -> bool {
    intrinsic_api::is_add_with_overflow(callee)
        || intrinsic_api::is_sub_with_overflow(callee)
        || intrinsic_api::is_mul_with_overflow(callee)
}

pub fn is_intrinsic_nonzero_preserving(callee: Option<DefId>) -> bool {
    intrinsic_api::is_bswap(callee)
        || intrinsic_api::is_ctpop(callee)
        || intrinsic_api::is_bitreverse(callee)
        || intrinsic_api::is_rotate_left(callee)
        || intrinsic_api::is_rotate_right(callee)
}

pub fn is_intrinsic_pure_opaque(callee: Option<DefId>) -> bool {
    intrinsic_api::is_float_to_int_unchecked(callee)
        || intrinsic_api::is_vtable_size(callee)
        || intrinsic_api::is_vtable_align(callee)
}

// ── Layout constants ──────────────────────────────────────────────

/// Whether `callee` is the compile-time layout constant `size_of::<T>()` or
/// `align_of::<T>()`. The runtime intrinsics (`size_of_val`, `align_of_val`,
/// `pref_align_of`, `*_val_raw`, …) are *not* classified here.
pub fn is_layout_constant(callee: Option<DefId>) -> bool {
    intrinsic_api::is_size_of(callee)
        || intrinsic_api::is_align_of(callee)
        || other_api::matches_any(
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

// ── MaybeUninit ───────────────────────────────────────────────────

/// Whether `callee` is `MaybeUninit::write`, which initializes the slot (unlike
/// raw `ptr::write`, handled by [`is_mem_copy_or_write`]).
pub fn is_maybe_uninit_write(callee: Option<DefId>) -> bool {
    other_api::matches_any(callee, &[other_api::maybe_uninit_write()])
}

/// Whether `callee` is `MaybeUninit::uninit` (a new uninitialized slot).
pub fn is_maybe_uninit_uninit(callee: Option<DefId>) -> bool {
    other_api::matches_any(callee, &[other_api::maybe_uninit_uninit()])
}

/// Whether `callee` is a `MaybeUninit` "assume initialized" accessor
/// (`assume_init`, `assume_init_read`, `assume_init_ref`, `assume_init_mut`).
pub fn is_maybe_uninit_assume_init(callee: Option<DefId>) -> bool {
    other_api::matches_any(
        callee,
        &[
            other_api::maybe_uninit_assume_init(),
            other_api::assume_init_read(),
            other_api::maybe_uninit_assume_init_ref(),
            other_api::maybe_uninit_assume_init_mut(),
        ],
    )
}

/// Memory copy/write intrinsics that legitimately write through a raw pointer
/// without requiring the target bytes to be pre-initialized (e.g. `ptr::write`,
/// `write_bytes`, `copy_nonoverlapping`, `ptr::copy`). Used by the checker to
/// discharge `Init`/`Typed` obligations on `MaybeUninit` targets.
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

// ── Queries and unwrap ────────────────────────────────────────────

// ── Slice / C-string ──────────────────────────────────────────────

/// Whether `callee` is a `from_raw_parts` constructor (`slice`/`str`/`ptr`/
/// `String`/`Vec`/`NonNull`). Matched by `DefId` via
/// [`crate::def_ids::other_api::from_raw_parts_fns`] in the standard-library crates.
pub fn is_from_raw_parts(callee: Option<DefId>) -> bool {
    any_def(callee, other_api::from_raw_parts_fns())
}

/// Whether `callee` is a `from_raw_parts_mut` constructor.
pub fn is_from_raw_parts_mut(callee: Option<DefId>) -> bool {
    any_def(callee, other_api::from_raw_parts_mut_fns())
}

pub fn is_cstr_from_ptr(callee: Option<DefId>) -> bool {
    other_api::matches_any(callee, &[other_api::cstr_from_ptr()])
}

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
// These are the single home for "what does this raw-pointer API do" used by the
// alias/hazard scanner. `is_ownership_transfer` is the raw-pointer subset of
// [`is_ownership_reconstruction`]: it excludes `from_vec_with_nul_unchecked`
// (which consumes a `Vec<u8>` rather than a raw pointer). `Vec::from_raw_parts`
// / `from_parts` ownership transfer is matched separately by
// [`is_vec_ownership_transfer`].

pub fn is_ownership_transfer(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    is_ownership_reconstruction(Some(callee))
        && !other_api::contains(&[nomir_ffi::cstring_from_vec_with_nul_unchecked()], callee)
}

pub fn is_vec_ownership_transfer(callee: Option<DefId>) -> bool {
    any_def(callee, other_api::vec_ownership_transfer_fns())
}

/// Whether `callee` is `NonNull::new` (the null-checked constructor).
pub(crate) fn is_nonnull_checked_new(callee: Option<DefId>) -> bool {
    other_api::matches_any(callee, &[other_api::nonnull_new()])
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

/// Whether `callee` is a `Vec` method that may reallocate (invalidating any
/// outstanding raw pointers derived from it).
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
pub fn is_benign_origin_use(callee: Option<DefId>) -> bool {
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
            other_api::nonnull_as_ptr(),
            other_api::nonnull_slice_is_empty(),
            other_api::nonnull_slice_len(),
            other_api::nonnull_slice_as_mut_ptr(),
            other_api::slice_len(),
            other_api::slice_is_empty(),
            other_api::slice_as_ptr(),
            other_api::slice_as_mut_ptr(),
            other_api::str_len(),
            other_api::str_is_empty(),
            other_api::str_as_ptr(),
            other_api::str_as_mut_ptr(),
            other_api::vec_len(),
            other_api::vec_is_empty(),
            other_api::vec_as_ptr(),
            other_api::vec_as_mut_ptr(),
            other_api::string_len(),
            other_api::string_is_empty(),
            other_api::cstr_as_ptr(),
            other_api::cstr_is_empty(),
        ],
    )
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
    use rustc_middle::ty::TyKind;
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

// ── Arithmetic / collection-operation classifiers ─────────────────
// Matched by `DefId` via [`other_api::OP_FNS`] (resolved from `fn_defs()`).
// [`crate::def_ids::other_api`] for the exact method-name patterns each group collects.

pub fn is_integer_wrapping_sub_method(callee: Option<DefId>) -> bool {
    any_def(callee, other_api::integer_wrapping_sub_fns())
}
pub fn is_split_at(callee: Option<DefId>) -> bool {
    any_def(callee, other_api::split_at_fns())
}

// ── Open-ended operation classifiers ──────────────────────────────
// These match standard-library methods through the name-scanned `fn_defs()`
// groups in [`crate::def_ids::other_api`].

/// Whether `callee` is `Range::next` / `RangeInclusive::next` (or their
/// `spec_next` impls). Distinct from the slice-side getters above: the receiver
/// is `&mut Range<A>`, and the returned element is the current `start`.
pub fn is_range_next(callee: Option<DefId>) -> bool {
    any_def(callee, other_api::range_next_fns())
}

/// Whether `callee` is a slice iterator's `next` (`Iter::next` /
/// `IterMut::next`, or the `Iterator::next` trait method they forward to).
pub fn is_iter_next(callee: Option<DefId>) -> bool {
    any_def(callee, other_api::iter_next_fns())
}

/// Whether `callee` is a slice iterator's `len` (`Iter::len` / `IterMut::len`).
pub fn is_iter_len(callee: Option<DefId>) -> bool {
    any_def(callee, other_api::iter_len_fns())
}

/// Whether `callee` is `<Option<T> as Try>::branch`.
pub fn is_branch(callee: Option<DefId>) -> bool {
    any_def(callee, other_api::branch_fns())
}

/// Whether `callee` is a `gcd` const fn.
pub fn is_gcd(callee: Option<DefId>) -> bool {
    any_def(callee, other_api::gcd_fns())
}

/// Whether `def_id` is `core::ops::index_range::IndexRange`.
pub fn is_index_range(def_id: DefId) -> bool {
    type_ids::index_range_types().contains(&def_id)
}
