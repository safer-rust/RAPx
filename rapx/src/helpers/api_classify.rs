//! Standard-library API name classification helpers.
//!
//! Each function matches a specific pattern in a MIR callee's
//! `def_path_str` to determine what kind of operation it performs
//! (pointer arithmetic, memory access, ownership transfer, etc.).

/// Whether `name` reconstructs an owned value from a single raw pointer
/// (`Box::from_raw`, `CString::from_raw`, `Arc::from_raw`, `Rc::from_raw`,
/// `CString::from_vec_with_nul_unchecked`), taking ownership of the pointed-to
/// memory. Distinct from [`is_from_raw_parts`], which builds a slice/`Vec`
/// from `(ptr, len[, cap])`.
pub fn is_ownership_reconstruction(name: &str) -> bool {
    name.contains("from_raw") && !name.contains("from_raw_parts")
        && (name.contains("boxed") || name.contains("Box")
            || name.contains("CString") || name.contains("ffi::c_str")
            || name.contains("::Arc") || name.contains("::Rc"))
        || name.contains("from_vec_with_nul_unchecked")
}

pub fn is_as_ptr(name: &str) -> bool {
    name.contains("::as_ptr") && !name.ends_with("::as_ptr_range")
        || name.ends_with("::into_raw")
        || name.contains("::as_mut_ptr") && !name.ends_with("::as_mut_ptr_range")
        || name.ends_with("::into_raw_mut")
        || (name.contains("::cast") && !name.contains("::cast_to"))
        || name.ends_with("::from") && name.contains("ptr::non_null")
        || name.ends_with("::new_unchecked") && name.contains("ptr::non_null")
        || name.ends_with("::as_ref") && name.contains("ptr::non_null")
        || name.ends_with("::as_mut") && name.contains("ptr::non_null")
}

pub fn is_pointer_add(name: &str) -> bool {
    name.ends_with("::add") || name.ends_with("::wrapping_add")
        || name.contains("::offset") || name.contains("::wrapping_offset")
        || name.contains("::byte_add") || name.contains("::wrapping_byte_add")
        || name.contains("::byte_offset") || name.contains("::wrapping_byte_offset")
}

pub fn is_pointer_sub(name: &str) -> bool {
    name.ends_with("::sub") || name.ends_with("::wrapping_sub")
        || name.contains("::byte_sub") || name.contains("::wrapping_byte_sub")
}

pub fn is_byte_ptr_arith(name: &str) -> bool {
    name.contains("::byte_add") || name.contains("::wrapping_byte_add")
        || name.contains("::byte_sub") || name.contains("::wrapping_byte_sub")
        || name.contains("::byte_offset") || name.contains("::wrapping_byte_offset")
}

pub fn is_layout_constant(name: &str) -> bool { name.contains("align_of") || name.contains("size_of") }
pub fn is_align_offset(name: &str) -> bool { name.contains("::align_offset") }
pub fn is_ptr_write(name: &str) -> bool {
    (name.contains("::write") || name.ends_with("write"))
        && !name.contains("write_bytes") && !name.contains("write_unaligned")
        && !name.contains("write_volatile")
}
pub fn is_maybe_uninit_write(name: &str) -> bool {
    name.contains("MaybeUninit") && name.ends_with("::write")
        && !name.contains("write_bytes")
}

/// Memory copy/write intrinsics that legitimately write through a raw pointer
/// without requiring the target bytes to be pre-initialized (e.g. `ptr::write`,
/// `write_bytes`, `copy_nonoverlapping`, `ptr::copy`). Used by the checker to
/// discharge `Init`/`Typed` obligations on `MaybeUninit` targets.
pub fn is_mem_copy_or_write_api(name: &str) -> bool {
    name.contains("copy_nonoverlapping")
        || name == "copy"
        || name.ends_with("::copy")
        || name.contains("ptr::copy")
        || name.contains("write_bytes")
        || name.contains("ptr::write")
}
pub fn is_len(name: &str) -> bool { name.contains("::len") }
pub fn is_capacity(name: &str) -> bool { name.contains("::capacity") }
pub fn is_option_unwrap(name: &str) -> bool {
    (name.contains("Option") || name.contains("Result"))
        && (name.contains("::expect") || name.contains("::unwrap")
            || name.contains("::unwrap_unchecked"))
}
pub fn is_maybe_uninit_uninit(name: &str) -> bool {
    name.contains("MaybeUninit") && name.ends_with("::uninit")
}
pub fn is_maybe_uninit_assume_init(name: &str) -> bool {
    name.contains("MaybeUninit") && (name.ends_with("::assume_init") || name.ends_with("::assume_init_read"))
}
pub fn is_from_raw_parts(name: &str) -> bool { name.contains("::from_raw_parts") }
pub fn is_cstr_from_ptr(name: &str) -> bool {
    name.contains("CStr") && name.ends_with("::from_ptr")
}
pub fn is_cstr_from_bytes_with_nul_unchecked(name: &str) -> bool {
    name.contains("CStr") && name.ends_with("::from_bytes_with_nul_unchecked")
}

/// Strict C-string constructors whose caller must guarantee NUL termination
/// (`CStr::from_bytes_with_nul_unchecked`, `CString::from_vec_with_nul_unchecked`).
pub fn is_cstr_strict_constructor(name: &str) -> bool {
    is_cstr_from_bytes_with_nul_unchecked(name) || name.contains("from_vec_with_nul_unchecked")
}
pub fn is_vec_push(name: &str) -> bool {
    (name.ends_with("::push") || name.ends_with("::reserve") || name.ends_with("::reserve_exact"))
        && name.contains("Vec")
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
    (name.contains("::Vec") && name.ends_with("::with_capacity"))
        || name == "with_capacity"
}
pub fn is_into_boxed_slice(name: &str) -> bool {
    name.ends_with("::into_boxed_slice")
}

// ── Alias-hazard classification ─────────────────────────────────────
// These are the single home for "what does this raw-pointer API do" used by the
// alias/hazard scanner. Note: `is_ownership_transfer_api` is *not* the same as
// [`is_ownership_reconstruction`]: it also matches `Vec::from_raw_parts` /
// `from_parts` (ownership transfer), but not `from_vec_with_nul_unchecked`.

pub fn is_read_api(name: &str) -> bool {
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

pub fn is_ownership_transfer_api(name: &str) -> bool {
    if is_vec_ownership_transfer_api(name) {
        return true;
    }
    name.contains("from_raw")
        && (name.contains("boxed")
            || name.contains("Box")
            || name.contains("ffi::c_str")
            || name.contains("CString"))
}

pub fn is_vec_ownership_transfer_api(name: &str) -> bool {
    (name.contains("from_raw_parts") || name.contains("from_parts"))
        && (name.contains("Vec") || name.contains("vec::"))
}

pub(crate) fn is_nonnull_api(name: &str) -> bool {
    name.contains("ptr::non_null") || name.contains("ptr::NonNull")
}

/// Whether `name` is a `Vec` method that may reallocate (invalidating any
/// outstanding raw pointers derived from it).
pub fn is_vec_invalidating_method(name: &str) -> bool {
    (name.contains("Vec") || name.contains("vec::"))
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
pub fn is_ownership_return_api(name: &str) -> bool {
    name.contains("into_raw")
        && (name.contains("boxed")
            || name.contains("Box")
            || name.contains("ffi::c_str")
            || name.contains("CString"))
}

/// Whether `name` terminates or reconstructs ownership of an allocation
/// (`from_raw` or `drop_in_place`).
pub fn is_ownership_transfer_terminator_api(name: &str) -> bool {
    name.contains("::from_raw") || name.contains("::drop_in_place")
}

/// Whether `name` is a benign, read-only use of a raw-pointer origin
/// (`as_ptr`, `len`, `is_empty`, `is_null`, `addr`, `cast`).
pub fn is_benign_origin_use_api(name: &str) -> bool {
    is_as_ptr(name)
        || name.ends_with("::len")
        || name.ends_with("::is_empty")
        || name.ends_with("::is_null")
        || name.ends_with("::addr")
}

// ── ADT type-name classifiers (match def_path_str of ADT types) ──────

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

// ── Function-name classifiers ────────────────────────────────────────

pub fn is_select_unpredictable(name: &str) -> bool { name.contains("select_unpredictable") }
pub fn is_post_inc_start(name: &str) -> bool { name.contains("::post_inc_start") }
pub fn is_pre_dec_end(name: &str) -> bool { name.contains("::pre_dec_end") }
pub fn is_iter_ptr_adj(name: &str) -> bool { is_post_inc_start(name) || is_pre_dec_end(name) }
pub fn is_eq_or_partial_eq(name: &str) -> bool { name.contains("::eq") || name.contains("PartialEq") }
pub fn is_vec_or_cstring_call(name: &str) -> bool { name.contains("::Vec") || name.contains("::CString") }
