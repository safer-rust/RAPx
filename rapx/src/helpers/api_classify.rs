//! Standard-library API name classification helpers.
//!
//! Each function matches a specific pattern in a MIR callee's
//! `def_path_str` to determine what kind of operation it performs
//! (pointer arithmetic, memory access, ownership transfer, etc.).

// ── Ownership reconstruction ──────────────────────────────────────

/// Whether `name` reconstructs an owned value from a single raw pointer
/// (`Box::from_raw`, `CString::from_raw`, `Arc::from_raw`, `Rc::from_raw`,
/// `CString::from_vec_with_nul_unchecked`), taking ownership of the pointed-to
/// memory. Distinct from [`is_from_raw_parts`], which builds a slice/`Vec`
/// from `(ptr, len[, cap])`.
pub fn is_ownership_reconstruction(name: &str) -> bool {
    (name.contains("from_raw") && !name.contains("from_raw_parts")
        && (name.contains("boxed") || name.contains("Box")
            || name.contains("CString") || name.contains("ffi::c_str")
            || name.contains("::Arc") || name.contains("::Rc")))
        || name.contains("from_vec_with_nul_unchecked")
}

// ── Pointer extraction / cast ─────────────────────────────────────

/// Whether `name` produces a raw pointer (or `NonNull`) alias of its first
/// argument: `as_ptr`/`as_mut_ptr`, `into_raw`/`into_raw_mut`, pointer `cast`
/// (incl. `cast_mut`/`cast_const`), and the `NonNull` accessors
/// (`from`, `new_unchecked`, `as_ptr`, `as_ref`, `as_mut`). `as_ptr_range` /
/// `as_mut_ptr_range` are excluded because they return a `Range` of two
/// pointers rather than a single pointer.
pub fn is_as_ptr(name: &str) -> bool {
    (name.contains("::as_ptr") && !name.ends_with("::as_ptr_range"))
        || name.ends_with("::into_raw")
        || (name.contains("::as_mut_ptr") && !name.ends_with("::as_mut_ptr_range"))
        || name.ends_with("::into_raw_mut")
        || (name.contains("::cast") && !name.contains("::cast_to"))
        || (name.contains("ptr::non_null")
            && (name.ends_with("::from")
                || name.ends_with("::new_unchecked")
                || name.ends_with("::as_ref")
                || name.ends_with("::as_mut")))
}

// ── Pointer arithmetic ────────────────────────────────────────────
// Direction (`add` vs `sub`) and granularity (`element` vs `byte`) are two
// orthogonal axes. Each of the four combinations is a first-class classifier
// below; the aggregate predicates at the end are unions over a single axis,
// for callers that only care about one dimension.

/// Element-strided `add`/`wrapping_add` and signed `offset`/`wrapping_offset`
/// (stride = `size_of::<T>()`).
pub(crate) fn is_element_ptr_add(name: &str) -> bool {
    name.ends_with("::add")
        || name.ends_with("::wrapping_add")
        || name.contains("::offset")
        || name.contains("::wrapping_offset")
}

/// Element-strided `sub`/`wrapping_sub` (stride = `size_of::<T>()`).
pub(crate) fn is_element_ptr_sub(name: &str) -> bool {
    name.ends_with("::sub") || name.ends_with("::wrapping_sub")
}

/// Byte-granular `byte_add`/`wrapping_byte_add` and signed
/// `byte_offset`/`wrapping_byte_offset` (stride 1).
pub(crate) fn is_byte_ptr_add(name: &str) -> bool {
    name.contains("::byte_add")
        || name.contains("::wrapping_byte_add")
        || name.contains("::byte_offset")
        || name.contains("::wrapping_byte_offset")
}

/// Byte-granular `byte_sub`/`wrapping_byte_sub` (stride 1).
pub(crate) fn is_byte_ptr_sub(name: &str) -> bool {
    name.contains("::byte_sub") || name.contains("::wrapping_byte_sub")
}

/// Any pointer `add` (element or byte). `offset`/`byte_offset` take a signed
/// `isize`, so a negative offset is still classified here (the sign lives in
/// the argument); see [`is_pointer_sub`] for the positive-count `sub` family.
pub fn is_pointer_add(name: &str) -> bool {
    is_element_ptr_add(name) || is_byte_ptr_add(name)
}

/// Any pointer `sub` (element or byte): a positive count, `base - count * stride`.
pub fn is_pointer_sub(name: &str) -> bool {
    is_element_ptr_sub(name) || is_byte_ptr_sub(name)
}

/// Any byte-granular pointer arithmetic (stride 1), regardless of direction.
pub fn is_byte_ptr_arith(name: &str) -> bool {
    is_byte_ptr_add(name) || is_byte_ptr_sub(name)
}

// ── Layout constants ──────────────────────────────────────────────

/// Whether `name` is the compile-time layout constant `size_of::<T>()` or
/// `align_of::<T>()`. Matched with a suffix boundary so the runtime
/// intrinsics (`size_of_val`, `align_of_val`, `pref_align_of`,
/// `*_val_raw`, …) are *not* classified here.
pub fn is_layout_constant(name: &str) -> bool {
    name.ends_with("::size_of") || name.ends_with("::align_of")
}

/// Whether `name` is `ptr::align_offset` / `NonNull::align_offset`.
pub fn is_align_offset(name: &str) -> bool {
    name.ends_with("::align_offset")
}

// ── Raw pointer read / write ──────────────────────────────────────

/// Whether `name` writes through a raw pointer to its first argument
/// (`ptr::write`, `write_bytes`, `write_unaligned`, `write_volatile`).
pub fn is_ptr_write(name: &str) -> bool {
    name.contains("::write") || name == "write"
}

/// Whether `name` reads through a raw pointer or copies memory
/// (`ptr::read`/`read_unaligned`/`read_volatile`, `copy_to`/`copy_from`,
/// `MaybeUninit::assume_init_read`, and intrinsics `copy`/`copy_nonoverlapping`).
pub fn is_ptr_read(name: &str) -> bool {
    if name.contains("::ptr::") {
        if name.ends_with("::read")
            || name.ends_with("::read_unaligned")
            || name.ends_with("::read_volatile")
            || name.ends_with("::copy_to")
            || name.ends_with("::copy_to_nonoverlapping")
            || name.ends_with("::copy_from")
            || name.ends_with("::copy_from_nonoverlapping")
        {
            return true;
        }
    }
    if name.ends_with("::assume_init_read") {
        return true;
    }
    if name.contains("::intrinsics::")
        && (name.ends_with("::copy") || name.ends_with("::copy_nonoverlapping"))
    {
        return true;
    }
    false
}

// ── MaybeUninit ───────────────────────────────────────────────────

/// Whether `name` is `MaybeUninit::write`, which initializes the slot (unlike
/// raw `ptr::write`, handled by [`is_mem_copy_or_write`]).
pub fn is_maybe_uninit_write(name: &str) -> bool {
    name.contains("MaybeUninit") && name.ends_with("::write")
        && !name.contains("write_bytes")
}

/// Whether `name` is `MaybeUninit::uninit` (a new uninitialized slot).
pub fn is_maybe_uninit_uninit(name: &str) -> bool {
    name.contains("MaybeUninit") && name.ends_with("::uninit")
}

/// Whether `name` is a `MaybeUninit` "assume initialized" accessor
/// (`assume_init`, `assume_init_read`, `assume_init_ref`, `assume_init_mut`).
pub fn is_maybe_uninit_assume_init(name: &str) -> bool {
    name.contains("MaybeUninit")
        && (name.ends_with("::assume_init")
            || name.ends_with("::assume_init_read")
            || name.ends_with("::assume_init_ref")
            || name.ends_with("::assume_init_mut"))
}

/// Memory copy/write intrinsics that legitimately write through a raw pointer
/// without requiring the target bytes to be pre-initialized (e.g. `ptr::write`,
/// `write_bytes`, `copy_nonoverlapping`, `ptr::copy`). Used by the checker to
/// discharge `Init`/`Typed` obligations on `MaybeUninit` targets.
pub fn is_mem_copy_or_write(name: &str) -> bool {
    name.contains("copy_nonoverlapping")
        || name == "copy"
        || name.ends_with("::copy")
        || name.contains("write_bytes")
        || name.contains("ptr::write")
}

// ── Queries and unwrap ────────────────────────────────────────────

pub fn is_len(name: &str) -> bool { name.contains("::len") }
pub fn is_capacity(name: &str) -> bool { name.contains("::capacity") }

pub fn is_unwrap(name: &str) -> bool {
    (name.contains("Option") || name.contains("Result"))
        && (name.ends_with("::expect")
            || name.ends_with("::expect_err")
            || name.ends_with("::unwrap")
            || name.ends_with("::unwrap_unchecked")
            || name.ends_with("::unwrap_err"))
}

// ── Slice / C-string ──────────────────────────────────────────────

pub fn is_from_raw_parts(name: &str) -> bool { name.contains("::from_raw_parts") }
pub fn is_cstr_from_ptr(name: &str) -> bool {
    name.contains("CStr") && name.ends_with("::from_ptr")
}

/// `_unchecked` C-string constructors whose caller must guarantee NUL
/// termination (`CStr::from_bytes_with_nul_unchecked`,
/// `CString::from_vec_with_nul_unchecked`).
pub fn is_cstr_unchecked_constructor(name: &str) -> bool {
    (name.contains("CStr") && name.ends_with("::from_bytes_with_nul_unchecked"))
        || name.contains("from_vec_with_nul_unchecked")
}

// ── Vec constructors / methods ────────────────────────────────────

pub fn is_vec_push(name: &str) -> bool {
    (name.ends_with("::push") || name.ends_with("::reserve") || name.ends_with("::reserve_exact"))
        && name.contains("::Vec::")
}
pub fn is_vec_alloc_constructor(name: &str) -> bool {
    name.contains("::vec::from_elem")
        || name == "from_elem"
}
pub fn is_vec_from_box(name: &str) -> bool {
    name.contains("::into_vec")
        || name.contains("box_assume_init_into_vec_unsafe")
}
pub fn is_vec_with_capacity(name: &str) -> bool {
    (name.contains("::Vec::") && name.ends_with("::with_capacity"))
        || name == "with_capacity"
}
pub fn is_into_boxed_slice(name: &str) -> bool {
    name.ends_with("::into_boxed_slice")
}

// ── Alias-hazard classification ───────────────────────────────────
// These are the single home for "what does this raw-pointer API do" used by the
// alias/hazard scanner. Note: `is_ownership_transfer` is *not* the same as
// [`is_ownership_reconstruction`]: it also matches `Vec::from_raw_parts` /
// `from_parts` (ownership transfer), but not `from_vec_with_nul_unchecked`.

pub fn is_ownership_transfer(name: &str) -> bool {
    if is_vec_ownership_transfer(name) {
        return true;
    }
    name.contains("from_raw")
        && (name.contains("boxed")
            || name.contains("Box")
            || name.contains("ffi::c_str")
            || name.contains("CString"))
}

pub fn is_vec_ownership_transfer(name: &str) -> bool {
    (name.contains("from_raw_parts") || name.contains("from_parts"))
        && (name.contains("Vec") || name.contains("vec::"))
}

pub(crate) fn is_nonnull(name: &str) -> bool {
    name.contains("ptr::non_null") || name.contains("ptr::NonNull")
}

/// Whether `name` is a `Vec` method that may reallocate (invalidating any
/// outstanding raw pointers derived from it).
pub fn is_vec_invalidating_method(name: &str) -> bool {
    (name.contains("::Vec::") || name.contains("vec::"))
        && (name.contains("::push")
            || name.contains("::reserve")
            || name.contains("::reserve_exact")
            || name.contains("::shrink_to_fit")
            || name.contains("::shrink_to")
            || name.contains("::insert")
            || name.contains("::remove")
            || name.contains("::clear")
            || name.contains("::truncate")
            || name.contains("::set_len"))
}

/// Whether `name` returns ownership of an allocation as a raw pointer
/// (`Box::into_raw`, `CString::into_raw`, ...).
pub fn is_ownership_return(name: &str) -> bool {
    name.contains("into_raw")
        && (name.contains("boxed")
            || name.contains("Box")
            || name.contains("ffi::c_str")
            || name.contains("CString"))
}

/// Whether `name` terminates or reconstructs ownership of an allocation
/// (`from_raw` or `drop_in_place`).
pub fn is_ownership_transfer_terminator(name: &str) -> bool {
    (name.contains("::from_raw") && !name.contains("from_raw_parts"))
        || name.contains("::drop_in_place")
}

/// Whether `name` is a benign, read-only use of a raw-pointer origin
/// (`as_ptr`, `len`, `is_empty`, `is_null`, `addr`, `cast`).
pub fn is_benign_origin_use(name: &str) -> bool {
    is_as_ptr(name)
        || name.ends_with("::len")
        || name.ends_with("::is_empty")
        || name.ends_with("::is_null")
        || name.ends_with("::addr")
}

// ── ADT type-name classifiers (match def_path_str of ADT types) ───

pub fn is_std_vec(name: &str) -> bool { name.ends_with("::Vec") || name == "Vec" }
pub fn is_std_box(name: &str) -> bool { name.ends_with("::Box") || name == "Box" }
pub fn is_std_cstring(name: &str) -> bool {
    name.ends_with("::CString") || name == "CString"
}
pub fn is_std_nonnull(name: &str) -> bool {
    name == "NonNull" || name.contains("::NonNull")
}
pub fn is_std_option(name: &str) -> bool {
    name == "Option" || name.contains("::Option")
}
pub fn is_std_iter_or_itermut(name: &str) -> bool {
    name.ends_with("::Iter") || name == "Iter"
        || name.ends_with("::IterMut") || name == "IterMut"
}
pub fn is_std_ordering(name: &str) -> bool { name.contains("cmp::Ordering") }

// ── Function-name classifiers ─────────────────────────────────────

pub fn is_select_unpredictable(name: &str) -> bool { name.contains("select_unpredictable") }