//! Standard-library API call classification helpers.
//!
//! Each classifier answers "what kind of operation is this call?" (pointer
//! arithmetic, raw memory access, ownership transfer, …). Callers — the VM,
//! the alias/hazard scanner, and the call-summary registry — use these to pick
//! a modelling strategy or discharge a safety obligation.
//!
//! # Matching mechanism
//!
//! Every classifier takes a `DefId` — `fn(Option<DefId>) -> bool` for callee
//! matching, or `fn(DefId) -> bool` for ADT *type* matching — and answers via
//! exact set membership in [`crate::def_id`] rather than substring-matching a
//! `def_path_str`. [`crate::def_id`] resolves the well-known `std`/`core`/`alloc`
//! items (by lang/diagnostic item, explicit path, or — for the open-ended
//! groups and the std-challenge suites' local re-implementations — by
//! name-scanning `fn_defs()` at init), so a call site is matched by identity
//! without the false positives of per-call-site name matching.

use rustc_hir::def_id::DefId;

// ── Ownership reconstruction ──────────────────────────────────────

/// Whether `callee` reconstructs an owned value, taking ownership of the
/// pointed-to memory: from a single raw pointer (`Box::from_raw`,
/// `CString::from_raw`, `Arc::from_raw`, `Rc::from_raw`) or from a `Vec<u8>`
/// (`CString::from_vec_with_nul_unchecked`). Distinct from
/// [`is_from_raw_parts`], which builds a slice/`Vec` from `(ptr, len[, cap])`.
pub fn is_ownership_reconstruction(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::box_from_raw(),
            crate::def_id::cstring_from_raw(),
            crate::def_id::arc_from_raw(),
            crate::def_id::rc_from_raw(),
            crate::def_id::box_from_raw_in(),
            crate::def_id::arc_from_raw_in(),
            crate::def_id::rc_from_raw_in(),
            crate::def_id::cstring_from_vec_with_nul_unchecked(),
        ],
        callee,
    )
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
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::slice_as_ptr(),
            crate::def_id::slice_as_mut_ptr(),
            crate::def_id::str_as_ptr(),
            crate::def_id::str_as_mut_ptr(),
            crate::def_id::vec_as_ptr(),
            crate::def_id::vec_as_mut_ptr(),
            crate::def_id::cstr_as_ptr(),
            crate::def_id::nonnull_as_ptr(),
            crate::def_id::const_ptr_slice_as_ptr(),
            crate::def_id::mut_ptr_slice_as_mut_ptr(),
            crate::def_id::nonnull_slice_as_mut_ptr(),
            crate::def_id::box_as_ptr(),
            crate::def_id::box_as_mut_ptr(),
            crate::def_id::maybe_uninit_as_ptr(),
            crate::def_id::maybe_uninit_as_mut_ptr(),
            crate::def_id::arc_as_ptr(),
            crate::def_id::rc_as_ptr(),
            crate::def_id::const_ptr_cast(),
            crate::def_id::const_ptr_cast_mut(),
            crate::def_id::mut_ptr_cast(),
            crate::def_id::mut_ptr_cast_const(),
            crate::def_id::nonnull_cast(),
            crate::def_id::box_into_raw(),
            crate::def_id::cstring_into_raw(),
            crate::def_id::arc_into_raw(),
            crate::def_id::rc_into_raw(),
        ],
        callee,
    )
}

/// Whether `callee` is a raw-pointer `cast`/`cast_mut`/`cast_const`. These only
/// *reinterpret* the address — they preserve null-ness and provenance, but do
/// not establish that the result is non-null, aligned, or points at initialized
/// memory. Distinguished from [`is_as_ptr`] so [`is_as_ptr_valid`] can keep
/// them on the MIR-inlining path rather than the `ReturnPointerFromArg` model
/// (which asserts those facts).
pub(crate) fn is_raw_ptr_cast(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::const_ptr_cast(),
            crate::def_id::const_ptr_cast_mut(),
            crate::def_id::mut_ptr_cast(),
            crate::def_id::mut_ptr_cast_const(),
        ],
        callee,
    )
}

/// [`is_as_ptr`] restricted to the *pointer-validity-establishing* subset:
/// `as_ptr`/`as_mut_ptr`, `into_raw`, and `NonNull::cast` — which expose a
/// non-null, aligned, initialized backing pointer. Raw-pointer `cast`/
/// `cast_mut`/`cast_const` are excluded because they only reinterpret the
/// address (preserving null-ness) and are left to MIR inlining.
pub fn is_as_ptr_valid(callee: Option<DefId>) -> bool {
    is_as_ptr(callee) && !is_raw_ptr_cast(callee)
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
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::const_ptr_add(),
            crate::def_id::const_ptr_wrapping_add(),
            crate::def_id::const_ptr_offset(),
            crate::def_id::const_ptr_wrapping_offset(),
            crate::def_id::mut_ptr_add(),
            crate::def_id::mut_ptr_wrapping_add(),
            crate::def_id::mut_ptr_offset(),
            crate::def_id::mut_ptr_wrapping_offset(),
            crate::def_id::nonnull_add(),
            crate::def_id::nonnull_offset(),
        ],
        callee,
    )
}

/// Element-strided `sub`/`wrapping_sub` (stride = `size_of::<T>()`).
pub(crate) fn is_element_ptr_sub(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::const_ptr_sub(),
            crate::def_id::const_ptr_wrapping_sub(),
            crate::def_id::mut_ptr_sub(),
            crate::def_id::mut_ptr_wrapping_sub(),
            crate::def_id::nonnull_sub(),
        ],
        callee,
    )
}

/// Byte-granular `byte_add`/`wrapping_byte_add` and signed
/// `byte_offset`/`wrapping_byte_offset` (stride 1).
pub(crate) fn is_byte_ptr_add(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::const_ptr_byte_add(),
            crate::def_id::const_ptr_wrapping_byte_add(),
            crate::def_id::const_ptr_byte_offset(),
            crate::def_id::const_ptr_wrapping_byte_offset(),
            crate::def_id::mut_ptr_byte_add(),
            crate::def_id::mut_ptr_wrapping_byte_add(),
            crate::def_id::mut_ptr_byte_offset(),
            crate::def_id::mut_ptr_wrapping_byte_offset(),
            crate::def_id::nonnull_byte_add(),
            crate::def_id::nonnull_byte_offset(),
        ],
        callee,
    )
}

/// Byte-granular `byte_sub`/`wrapping_byte_sub` (stride 1).
pub(crate) fn is_byte_ptr_sub(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::const_ptr_byte_sub(),
            crate::def_id::const_ptr_wrapping_byte_sub(),
            crate::def_id::mut_ptr_byte_sub(),
            crate::def_id::mut_ptr_wrapping_byte_sub(),
            crate::def_id::nonnull_byte_sub(),
        ],
        callee,
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

/// Any byte-granular pointer arithmetic (stride 1), regardless of direction.
pub fn is_byte_ptr_arith(callee: Option<DefId>) -> bool {
    is_byte_ptr_add(callee) || is_byte_ptr_sub(callee)
}

// ── Layout constants ──────────────────────────────────────────────

/// Whether `callee` is the compile-time layout constant `size_of::<T>()` or
/// `align_of::<T>()`. The runtime intrinsics (`size_of_val`, `align_of_val`,
/// `pref_align_of`, `*_val_raw`, …) are *not* classified here.
pub fn is_layout_constant(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::mem_size_of(),
            crate::def_id::mem_align_of(),
            crate::def_id::intrinsics_size_of(),
            crate::def_id::intrinsics_align_of(),
        ],
        callee,
    )
}

/// Whether `callee` is `ptr::align_offset` / `NonNull::align_offset` /
/// `*const T::align_offset` / `*mut T::align_offset`.
pub fn is_align_offset(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::ptr_align_offset(),
            crate::def_id::nonnull_align_offset(),
            crate::def_id::const_ptr_align_offset(),
            crate::def_id::mut_ptr_align_offset(),
        ],
        callee,
    )
}

// ── Raw pointer read / write ──────────────────────────────────────

/// Whether `callee` writes through a raw pointer to its first argument
/// (`ptr::write`, `write_bytes`, `write_unaligned`, `write_volatile`).
pub fn is_ptr_write(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::ptr_write(),
            crate::def_id::ptr_write_unaligned(),
            crate::def_id::ptr_write_volatile(),
            crate::def_id::ptr_write_bytes(),
        ],
        callee,
    )
}

/// Whether `callee` reads through a raw pointer or copies memory
/// (`ptr::read`/`read_unaligned`/`read_volatile`, `copy_to`/`copy_from`,
/// `MaybeUninit::assume_init_read`, and intrinsics `copy`/`copy_nonoverlapping`).
pub fn is_ptr_read(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::ptr_read(),
            crate::def_id::ptr_read_unaligned(),
            crate::def_id::ptr_read_volatile(),
            crate::def_id::copy_to(),
            crate::def_id::copy_to_nonoverlapping(),
            crate::def_id::copy_from(),
            crate::def_id::copy_from_nonoverlapping(),
            crate::def_id::assume_init_read(),
            crate::def_id::intrinsics_copy(),
            crate::def_id::intrinsics_copy_nonoverlapping(),
        ],
        callee,
    )
}

// ── MaybeUninit ───────────────────────────────────────────────────

/// Whether `callee` is `MaybeUninit::write`, which initializes the slot (unlike
/// raw `ptr::write`, handled by [`is_mem_copy_or_write`]).
pub fn is_maybe_uninit_write(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(&[crate::def_id::maybe_uninit_write()], callee)
}

/// Whether `callee` is `MaybeUninit::uninit` (a new uninitialized slot).
pub fn is_maybe_uninit_uninit(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(&[crate::def_id::maybe_uninit_uninit()], callee)
}

/// Whether `callee` is a `MaybeUninit` "assume initialized" accessor
/// (`assume_init`, `assume_init_read`, `assume_init_ref`, `assume_init_mut`).
pub fn is_maybe_uninit_assume_init(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::maybe_uninit_assume_init(),
            crate::def_id::assume_init_read(),
            crate::def_id::maybe_uninit_assume_init_ref(),
            crate::def_id::maybe_uninit_assume_init_mut(),
        ],
        callee,
    )
}

/// Memory copy/write intrinsics that legitimately write through a raw pointer
/// without requiring the target bytes to be pre-initialized (e.g. `ptr::write`,
/// `write_bytes`, `copy_nonoverlapping`, `ptr::copy`). Used by the checker to
/// discharge `Init`/`Typed` obligations on `MaybeUninit` targets.
pub fn is_mem_copy_or_write(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::intrinsics_copy(),
            crate::def_id::intrinsics_copy_nonoverlapping(),
            crate::def_id::copy_from_nonoverlapping(),
            crate::def_id::copy_to_nonoverlapping(),
            crate::def_id::ptr_write(),
            crate::def_id::ptr_write_bytes(),
        ],
        callee,
    )
}

// ── Queries and unwrap ────────────────────────────────────────────

/// Whether `callee` is a `len` query method. Matched by `DefId` via
/// [`crate::def_id::len_fns`], which resolves every `::len` `fn_def` in the std
/// crates *and* the local crate — so the std-challenge suites' re-implemented
/// `len` methods are modelled too, without substring-matching a `def_path_str`.
pub fn is_len(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::len_fns().contains(&callee)
}

/// Whether `callee` is a `capacity` query method.
pub fn is_capacity(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::capacity_fns().contains(&callee)
}

pub fn is_unwrap(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::option_unwrap(),
            crate::def_id::option_expect(),
            crate::def_id::option_unwrap_unchecked(),
            crate::def_id::result_unwrap(),
            crate::def_id::result_unwrap_err(),
            crate::def_id::result_expect(),
            crate::def_id::result_expect_err(),
            crate::def_id::result_unwrap_unchecked(),
        ],
        callee,
    )
}

// ── Slice / C-string ──────────────────────────────────────────────

/// Whether `callee` is a `from_raw_parts` constructor (`slice`/`str`/`ptr`/
/// `String`/`Vec`/`NonNull`). Matched by `DefId` via
/// [`crate::def_id::from_raw_parts_fns`] (resolved from `fn_defs()`, including
/// local re-implementations), instead of substring-matching `def_path_str`.
pub fn is_from_raw_parts(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::from_raw_parts_fns().contains(&callee)
}

/// Whether `callee` is a `from_raw_parts_mut` constructor.
pub fn is_from_raw_parts_mut(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::from_raw_parts_mut_fns().contains(&callee)
}

pub fn is_cstr_from_ptr(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(&[crate::def_id::cstr_from_ptr()], callee)
}

/// `_unchecked` C-string constructors whose caller must guarantee NUL
/// termination (`CStr::from_bytes_with_nul_unchecked`,
/// `CString::from_vec_with_nul_unchecked`).
pub fn is_cstr_unchecked_constructor(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::cstr_from_bytes_with_nul_unchecked(),
            crate::def_id::cstring_from_vec_with_nul_unchecked(),
        ],
        callee,
    )
}

// ── Vec constructors / methods ────────────────────────────────────

pub fn is_vec_push_or_reserve(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::vec_push(),
            crate::def_id::vec_reserve(),
            crate::def_id::vec_reserve_exact(),
        ],
        callee,
    )
}
pub fn is_vec_alloc_constructor(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(&[crate::def_id::vec_from_elem()], callee)
}
pub fn is_vec_from_box(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::slice_into_vec(),
            crate::def_id::box_assume_init_into_vec_unsafe(),
        ],
        callee,
    )
}
/// `Vec::with_capacity` — matched by `DefId` via
/// [`crate::def_id::with_capacity_fns`].
pub fn is_vec_with_capacity(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::with_capacity_fns().contains(&callee)
}
pub fn is_into_boxed_slice(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(&[crate::def_id::vec_into_boxed_slice()], callee)
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
        && !crate::def_id::contains(
            &[crate::def_id::cstring_from_vec_with_nul_unchecked()],
            callee,
        )
}

pub fn is_vec_ownership_transfer(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::vec_ownership_transfer_fns().contains(&callee)
}

/// Whether `callee` is `NonNull::new` (the null-checked constructor).
pub(crate) fn is_nonnull_checked_new(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(&[crate::def_id::nonnull_new()], callee)
}

/// Whether `callee` is `NonNull::as_ref` or `NonNull::as_mut`.
pub fn is_nonnull_as_ref_as_mut(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::nonnull_as_ref(),
            crate::def_id::nonnull_as_mut(),
        ],
        callee,
    )
}

/// Whether `callee` is a `Vec` method that may reallocate (invalidating any
/// outstanding raw pointers derived from it).
pub fn is_vec_invalidating_method(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::vec_push(),
            crate::def_id::vec_reserve(),
            crate::def_id::vec_reserve_exact(),
            crate::def_id::vec_shrink_to_fit(),
            crate::def_id::vec_shrink_to(),
            crate::def_id::vec_insert(),
            crate::def_id::vec_remove(),
            crate::def_id::vec_clear(),
            crate::def_id::vec_truncate(),
            crate::def_id::vec_set_len(),
        ],
        callee,
    )
}

/// Whether `callee` returns ownership of an allocation as a raw pointer
/// (`Box::into_raw`, `CString::into_raw`, `Arc::into_raw`, `Rc::into_raw`, ...).
pub fn is_ownership_return(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::box_into_raw(),
            crate::def_id::cstring_into_raw(),
            crate::def_id::arc_into_raw(),
            crate::def_id::rc_into_raw(),
        ],
        callee,
    )
}

/// Whether `callee` is a benign, read-only use of a raw-pointer origin
/// (`len`, `is_empty`, `is_null`, `addr`, `as_ptr`/`as_mut_ptr`, `cast`).
pub fn is_benign_origin_use(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(
        &[
            crate::def_id::const_ptr_is_null(),
            crate::def_id::const_ptr_addr(),
            crate::def_id::const_ptr_cast(),
            crate::def_id::const_ptr_cast_mut(),
            crate::def_id::const_ptr_slice_is_empty(),
            crate::def_id::const_ptr_slice_len(),
            crate::def_id::const_ptr_slice_as_ptr(),
            crate::def_id::mut_ptr_is_null(),
            crate::def_id::mut_ptr_addr(),
            crate::def_id::mut_ptr_cast(),
            crate::def_id::mut_ptr_cast_const(),
            crate::def_id::mut_ptr_slice_is_empty(),
            crate::def_id::mut_ptr_slice_len(),
            crate::def_id::mut_ptr_slice_as_mut_ptr(),
            crate::def_id::nonnull_addr(),
            crate::def_id::nonnull_cast(),
            crate::def_id::nonnull_as_ptr(),
            crate::def_id::nonnull_slice_is_empty(),
            crate::def_id::nonnull_slice_len(),
            crate::def_id::nonnull_slice_as_mut_ptr(),
            crate::def_id::slice_len(),
            crate::def_id::slice_is_empty(),
            crate::def_id::slice_as_ptr(),
            crate::def_id::slice_as_mut_ptr(),
            crate::def_id::str_len(),
            crate::def_id::str_is_empty(),
            crate::def_id::str_as_ptr(),
            crate::def_id::str_as_mut_ptr(),
            crate::def_id::vec_len(),
            crate::def_id::vec_is_empty(),
            crate::def_id::vec_as_ptr(),
            crate::def_id::vec_as_mut_ptr(),
            crate::def_id::string_len(),
            crate::def_id::string_is_empty(),
            crate::def_id::cstr_as_ptr(),
            crate::def_id::cstr_is_empty(),
        ],
        callee,
    )
}

// ── ADT type-name classifiers ─────────────────────────────────────
// *Shape* recognizers used by the VM to model repr(transparent) wrappers and
// fixed field layouts (`Vec` = ptr/cap/len, `slice::Iter` = ptr/end, …).
// Matched by `DefId` (resolved in [`crate::def_id`]).

pub fn is_std_vec(def_id: DefId) -> bool {
    crate::def_id::vec_types().contains(&def_id)
}
pub fn is_std_box(def_id: DefId) -> bool {
    crate::def_id::box_types().contains(&def_id)
}
pub fn is_std_cstring(def_id: DefId) -> bool {
    crate::def_id::cstring_types().contains(&def_id)
}
pub fn is_std_nonnull(def_id: DefId) -> bool {
    crate::def_id::nonnull_types().contains(&def_id)
}
pub fn is_maybe_uninit_type(def_id: DefId) -> bool {
    crate::def_id::maybe_uninit_types().contains(&def_id)
}
pub fn is_std_iter_or_itermut(def_id: DefId) -> bool {
    crate::def_id::iter_types().contains(&def_id)
}
pub fn is_std_ordering(def_id: DefId) -> bool {
    crate::def_id::ordering_types().contains(&def_id)
}

// ── Arithmetic / collection-operation classifiers ─────────────────
// Matched by `DefId` via [`crate::def_id::OP_FNS`] (resolved from `fn_defs()`).
// These were previously name-based in the call-summary registry; see
// [`crate::def_id`] for the exact method-name patterns each group collects.

pub fn is_min_like(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::min_like_fns().contains(&callee)
}
pub fn is_max(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::max_fns().contains(&callee)
}
pub fn is_clamp(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::clamp_fns().contains(&callee)
}
pub fn is_abs(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::abs_fns().contains(&callee)
}
pub fn is_neg(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::neg_fns().contains(&callee)
}
pub fn is_sat_unchecked_add(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::sat_unchecked_add_fns().contains(&callee)
}
pub fn is_sat_unchecked_mul(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::sat_unchecked_mul_fns().contains(&callee)
}
pub fn is_checked_add(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::checked_add_fns().contains(&callee)
}
pub fn is_checked_mul(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::checked_mul_fns().contains(&callee)
}
pub fn is_overflowing_abs_neg(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::overflowing_nz_fns().contains(&callee)
}
pub fn is_bit_preserving_nz(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::bit_preserving_nz_fns().contains(&callee)
}
pub fn is_checked_nonzero_iff(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::checked_nonzero_iff_fns().contains(&callee)
}
pub fn is_checked_next_pow2(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::checked_next_pow2_fns().contains(&callee)
}
pub fn is_layout_align(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::layout_align_fns().contains(&callee)
}
pub fn is_split_at(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::split_at_fns().contains(&callee)
}

// ── Open-ended operation classifiers ──────────────────────────────
// These match the std-challenge suites' local `_ext` re-implementations and
// generic trait-method patterns. They cannot be tied to a *closed* hard-coded
// set, so they are resolved by name-scanning `fn_defs()` in [`crate::def_id`]
// (which also collects the local crate's re-implementations) and matched by
// `DefId` like the other classifiers.

pub fn is_align_to_local(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::align_to_local_fns().contains(&callee)
}
pub fn is_iter_position(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::iter_position_fns().contains(&callee)
}
pub fn is_strlen(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::strlen_fns().contains(&callee)
}
pub fn is_slice_get_unchecked(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::slice_get_unchecked_fns().contains(&callee)
}

/// Whether `callee` is `SliceIndex::get_unchecked`/`get_unchecked_mut` (the
/// trait method, whose receiver is the *index* and whose first argument is the
/// slice pointer). Distinct from [`is_slice_get_unchecked`] (the slice-side
/// methods whose receiver is the slice): the result aliases argument 1, not
/// argument 0.
pub fn is_sliceindex_get_unchecked(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::sliceindex_get_unchecked_fns().contains(&callee)
}
