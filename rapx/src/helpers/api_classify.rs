//! Standard-library API call classification helpers.
//!
//! Each classifier answers "what kind of operation is this call?" (pointer
//! arithmetic, raw memory access, ownership transfer, …). Callers — the VM,
//! the alias/hazard scanner, and the call-summary registry — use these to pick
//! a modelling strategy or discharge a safety obligation.
//!
//! # Two matching mechanisms
//!
//! A classifier takes either a `DefId` or a name string, depending on what it
//! targets:
//!
//! - **`fn(Option<DefId>) -> bool`** — for a *closed* set of well-known
//!   `std`/`core`/`alloc` items that [`crate::def_id`] can resolve (e.g.
//!   [`is_ptr_read`], [`is_unwrap`], [`is_maybe_uninit_assume_init`]). These
//!   match the callee `DefId` exactly via [`crate::def_id::contains`] and avoid
//!   the false positives of substring matching.
//! - **`fn(&str) -> bool`** — kept name-based when the target is not a closed
//!   set of resolvable items, or when the match must also cover the
//!   std-challenge test suites' *re-implementations* of std types under the
//!   same names: generic query names ([`is_len`], [`is_capacity`]), APIs that
//!   `rustc_public` does not emit as `fn_def` ([`is_from_raw_parts`], since
//!   `Vec::from_raw_parts` cannot be resolved to a `DefId`), and the ADT
//!   *type*-name classifiers at the bottom ([`is_std_vec`], [`is_std_box`],
//!   …).
//!
//! Prefer the `DefId` form for any new closed-set classifier; use the name
//! form only when the set is open-ended or unresolvable.

use rustc_hir::def_id::DefId;

// ── Ownership reconstruction ──────────────────────────────────────

/// Whether `callee` reconstructs an owned value from a single raw pointer
/// (`Box::from_raw`, `CString::from_raw`, `Arc::from_raw`, `Rc::from_raw`,
/// `CString::from_vec_with_nul_unchecked`), taking ownership of the pointed-to
/// memory. Distinct from [`is_from_raw_parts`], which builds a slice/`Vec`
/// from `(ptr, len[, cap])`.
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

/// Whether `name` is a `len` query. Kept name-based: the std-challenge test
/// suites re-implement slice/`Vec`-like types under their own names, and the
/// VM must model those local `len` methods too (a `DefId`-only matcher would
/// inline them and lose the length abstraction).
pub fn is_len(name: &str) -> bool { name.contains("::len") }

/// Whether `name` is a `capacity` query.
pub fn is_capacity(name: &str) -> bool { name.contains("::capacity") }

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

/// Whether `name` is a `from_raw_parts` constructor (`slice`/`str`/`ptr`/
/// `String`/`Vec`/`NonNull`).  Kept name-based because `Vec::from_raw_parts`
/// is not emitted as a `fn_def` in `rustc_public`, so it cannot be resolved to
/// a `DefId` by [`crate::def_id`].
pub fn is_from_raw_parts(name: &str) -> bool { name.contains("::from_raw_parts") }
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

pub fn is_vec_push(callee: Option<DefId>) -> bool {
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
/// `Vec::with_capacity` — `#[inline]` const fn, not emitted by `fn_defs()`.
pub fn is_vec_with_capacity(name: &str) -> bool {
    (name.contains("::Vec::") && name.ends_with("::with_capacity"))
        || name == "with_capacity"
}
pub fn is_into_boxed_slice(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(&[crate::def_id::vec_into_boxed_slice()], callee)
}

// ── Alias-hazard classification ───────────────────────────────────
// These are the single home for "what does this raw-pointer API do" used by the
// alias/hazard scanner. Note: `is_ownership_transfer` is *not* the same as
// [`is_ownership_reconstruction`]: it also matches `Vec::from_raw_parts` /
// `from_parts` (ownership transfer) — handled separately by
// [`is_vec_ownership_transfer`] because `Vec::from_raw_parts` is not resolvable
// via [`crate::def_id`] — but not `from_vec_with_nul_unchecked`.

pub fn is_ownership_transfer(callee: Option<DefId>) -> bool {
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
        ],
        callee,
    )
}

pub fn is_vec_ownership_transfer(name: &str) -> bool {
    (name.contains("from_raw_parts") || name.contains("from_parts"))
        && (name.contains("Vec") || name.contains("vec::"))
}

/// Whether `callee` is `NonNull::new` (the null-checked constructor).
pub(crate) fn is_nonnull(callee: Option<DefId>) -> bool {
    let Some(callee) = callee else { return false };
    crate::def_id::contains(&[crate::def_id::nonnull_new()], callee)
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
// These match a type's `def_path_str` (not a `DefId`) on purpose: they are
// *shape* recognizers used by the VM to model repr(transparent) wrappers and
// fixed field layouts (`Vec` = ptr/cap/len, `slice::Iter` = ptr/end, …).  The
// std-challenge test suites re-implement these std types under the same names,
// so matching by name is what lets the VM model those re-implementations too.

pub fn is_std_vec(name: &str) -> bool { name.ends_with("::Vec") || name == "Vec" }
pub fn is_std_box(name: &str) -> bool { name.ends_with("::Box") || name == "Box" }
pub fn is_std_cstring(name: &str) -> bool {
    name.ends_with("::CString") || name == "CString"
}
pub fn is_std_nonnull(name: &str) -> bool {
    name == "NonNull" || name.contains("::NonNull")
}
pub fn is_std_iter_or_itermut(name: &str) -> bool {
    name.ends_with("::Iter") || name == "Iter"
        || name.ends_with("::IterMut") || name == "IterMut"
}
pub fn is_std_ordering(name: &str) -> bool { name.ends_with("cmp::Ordering") }