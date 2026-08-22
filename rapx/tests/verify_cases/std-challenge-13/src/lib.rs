#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]

// ========================================================================
// Challenge 13: Safety of `CStr`
//
// A faithful, self-contained port of `library/core/src/ffi/c_str.rs`
// (see
// https://model-checking.github.io/verify-rust-std/challenges/0013-cstr.html).
//
// `CStr` is a borrowed, null-terminated byte string: `#[repr(transparent)]`
// over a `[c_char]` slice (the `inner: [u8]` field below — `c_char` is `u8`
// on the target). Its safety invariant — the challenge's `Invariant` trait —
// states that the underlying byte buffer is
//
//     !bytes.is_empty() && bytes[bytes.len() - 1] == 0
//         && !bytes[..bytes.len() - 1].contains(&0)
//
// RAPx encodes that invariant with the `ValidCStr` primitive property, which
// the unsafe constructors carry as `#[rapx::requires]` contracts (mirroring
// RAPx's bundled `core::ffi::c_str::{from_ptr, from_bytes_with_nul_unchecked}`
// contracts). The safe methods route through those constructors, so their
// proof obligation is exactly to establish the `ValidCStr` invariant before
// the reborrow.
//
// The function bodies are kept as close to `std` as possible. The only
// unavoidable deviations are:
//
//   * `memchr::memchr(0, bytes)` becomes a plain `bytes.iter().position`
//     scan (the `memchr` crate is not a dependency of this test crate).
//   * `strlen`'s `const_eval_select`/libc split collapses to the const
//     branch's simple loop.
//   * `CloneToUninit` (an unstable `core::clone` trait) is reproduced locally
//     as an `unsafe trait`; its `CStr` impl delegates to a local `[u8]` impl
//     exactly as `std` delegates to `[c_char]`/`[u8]`.
// ========================================================================

use std::ops::{Index, RangeFrom};
use std::slice;

// ========================================================================
// CStr
// ========================================================================

/// `#[repr(transparent)]` over `[u8]`, the target's `c_char` representation.
///
/// Faithful to `std`'s `core::ffi::CStr`: a dynamically-sized slice of bytes
/// whose safety invariant (`ValidCStr`) is a non-empty, null-terminated
/// buffer with no interior null bytes.
#[repr(transparent)]
#[rapx::invariant(ValidCStr(inner, inner.len()))]
pub struct CStr {
    inner: [u8],
}

/// An error indicating that a nul byte was not in the expected position.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FromBytesWithNulError {
    /// Data provided contains an interior nul byte at byte `position`.
    InteriorNul { position: usize },
    /// Data provided is not nul terminated.
    NotNulTerminated,
}

/// An error indicating that no nul byte was present.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FromBytesUntilNulError(());

// ========================================================================
// Constructors
// ========================================================================

impl CStr {
    /// Creates a C string wrapper from a byte slice with any number of nuls,
    /// ending the string at the first nul byte.
    #[rapx::verify]
    pub fn from_bytes_until_nul(bytes: &[u8]) -> Result<&CStr, FromBytesUntilNulError> {
        let nul_pos = bytes.iter().position(|&b| b == 0);
        match nul_pos {
            Some(nul_pos) => {
                // SAFETY: nul_pos + 1 <= bytes.len() because the nul byte is
                // inside the slice, so the subslice ending at (and including)
                // the nul is a well-formed C string.
                let subslice = unsafe { slice::from_raw_parts(bytes.as_ptr(), nul_pos + 1) };
                Ok(unsafe { CStr::from_bytes_with_nul_unchecked(subslice) })
            }
            None => Err(FromBytesUntilNulError(())),
        }
    }

    /// Creates a C string wrapper from a byte slice with exactly one nul
    /// terminator (no interior nul bytes).
    #[rapx::verify]
    pub fn from_bytes_with_nul(bytes: &[u8]) -> Result<&CStr, FromBytesWithNulError> {
        let nul_pos = bytes.iter().position(|&b| b == 0);
        match nul_pos {
            Some(nul_pos) if nul_pos + 1 == bytes.len() => {
                // SAFETY: there is exactly one nul byte, at the end of the
                // slice, so the slice is a well-formed C string.
                Ok(unsafe { CStr::from_bytes_with_nul_unchecked(bytes) })
            }
            Some(position) => Err(FromBytesWithNulError::InteriorNul { position }),
            None => Err(FromBytesWithNulError::NotNulTerminated),
        }
    }

    /// Unsafely creates a C string wrapper from a byte slice.
    ///
    /// # Safety
    ///
    /// The provided slice **must** be nul-terminated and not contain any
    /// interior nul bytes (the `ValidCStr` invariant).
    #[rapx::verify]
    #[rapx::requires(ValidCStr(bytes, bytes.len()))]
    pub unsafe fn from_bytes_with_nul_unchecked(bytes: &[u8]) -> &CStr {
        // SAFETY: Casting to CStr is safe because its internal representation
        // is a [u8] too. Dereferencing the obtained pointer is safe because it
        // comes from a reference. Making a reference is then safe because its
        // lifetime is bound by the lifetime of the given `bytes`.
        unsafe { &*(bytes as *const [u8] as *const CStr) }
    }

    /// Wraps a raw C string with a safe C string wrapper.
    ///
    /// # Safety
    ///
    /// The memory pointed to by `ptr` must contain a valid nul terminator at
    /// the end of the string; `ptr` must be valid for reads of bytes up to and
    /// including the nul terminator (in particular: the entire range must be
    /// within a single allocation, and `ptr` must be non-null even for a
    /// zero-length cstr).
    #[rapx::verify]
    #[rapx::requires(Allocated(ptr, u8, 1, global))]
    #[rapx::requires(ValidCStr(ptr, 1))]
    #[rapx::requires(NonNull(ptr))]
    #[rapx::requires(Alias(ptr, return))]
    #[rapx::requires(Alive(ptr, 'a))]
    pub unsafe fn from_ptr<'a>(ptr: *const u8) -> &'a CStr {
        // SAFETY: The caller has provided a pointer that points to a valid C
        // string with a NUL terminator less than `isize::MAX` from `ptr`.
        let len = unsafe { strlen(ptr) };

        // SAFETY: The caller has provided a valid pointer with length less than
        // `isize::MAX`, so `from_raw_parts` is safe. The content remains valid
        // and doesn't change for the lifetime of the returned `CStr`. This
        // means the call to `from_bytes_with_nul_unchecked` is correct.
        unsafe { CStr::from_bytes_with_nul_unchecked(slice::from_raw_parts(ptr, len + 1)) }
    }
}

/// Calculate the length of a nul-terminated string.
///
/// # Safety
///
/// The pointer must point to a valid buffer that contains a NUL terminator.
/// The NUL must be located within `isize::MAX` from `ptr`.
#[rapx::verify]
#[rapx::requires(ValidCStr(ptr, 1))]
unsafe fn strlen(ptr: *const u8) -> usize {
    let mut len = 0;

    // SAFETY: Outer caller has provided a pointer to a valid C string.
    while unsafe { *ptr.add(len) } != 0 {
        len += 1;
    }

    len
}

// ========================================================================
// Accessors
// ========================================================================

impl CStr {
    /// Returns the inner pointer to this C string.
    #[rapx::verify]
    pub fn as_ptr(&self) -> *const u8 {
        self.inner.as_ptr()
    }

    /// Returns the length of `self`, not including the nul terminator.
    #[rapx::verify]
    pub fn count_bytes(&self) -> usize {
        self.inner.len() - 1
    }

    /// Returns `true` if `self.to_bytes()` has a length of 0.
    #[rapx::verify]
    pub fn is_empty(&self) -> bool {
        // SAFETY: We know there is at least one byte; for empty strings it
        // is the NUL terminator.
        unsafe { *self.inner.as_ptr() == 0 }
    }

    /// Converts this C string to a byte slice without the trailing nul.
    #[rapx::verify]
    pub fn to_bytes(&self) -> &[u8] {
        let bytes = self.to_bytes_with_nul();
        // SAFETY: to_bytes_with_nul returns slice with length at least 1
        unsafe { slice::from_raw_parts(bytes.as_ptr(), bytes.len() - 1) }
    }

    /// Converts this C string to a byte slice containing the trailing nul.
    #[rapx::verify]
    pub fn to_bytes_with_nul(&self) -> &[u8] {
        // SAFETY: Transmuting a slice of `u8`s to a slice of `u8`s is safe on
        // all supported targets.
        unsafe { &*((&raw const self.inner) as *const [u8]) }
    }

    /// Yields a `&str` if the `CStr` contains valid UTF-8.
    #[rapx::verify]
    pub fn to_str(&self) -> Result<&str, std::str::Utf8Error> {
        std::str::from_utf8(self.to_bytes())
    }

    /// Iterates over the bytes in this C string, without the nul terminator.
    #[rapx::verify]
    pub fn bytes(&self) -> Bytes<'_> {
        Bytes::new(self)
    }
}

// ========================================================================
// Iterator over the bytes of a CStr
// ========================================================================

/// An iterator over the bytes of a [`CStr`], without the nul terminator.
#[derive(Clone, Debug)]
pub struct Bytes<'a> {
    inner: &'a [u8],
}

impl<'a> Bytes<'a> {
    #[rapx::verify]
    fn new(cstr: &'a CStr) -> Bytes<'a> {
        Bytes {
            inner: cstr.to_bytes(),
        }
    }
}

impl<'a> Iterator for Bytes<'a> {
    type Item = u8;

    #[rapx::verify]
    fn next(&mut self) -> Option<u8> {
        let (&first, rest) = self.inner.split_first()?;
        self.inner = rest;
        Some(first)
    }
}

// ========================================================================
// Trait impls
// ========================================================================

/// `ops::Index<ops::RangeFrom<usize>>`: index into a `CStr` from a start
/// offset, returning the (non-empty) nul-terminated tail.
impl Index<RangeFrom<usize>> for CStr {
    type Output = CStr;

    #[rapx::verify]
    fn index(&self, index: RangeFrom<usize>) -> &CStr {
        let bytes = self.to_bytes_with_nul();
        // we need to manually check the starting index to account for the null
        // byte, since otherwise we could get an empty string that doesn't end
        // in a null.
        if index.start < bytes.len() {
            // SAFETY: Non-empty tail of a valid `CStr` is still a valid `CStr`.
            unsafe { CStr::from_bytes_with_nul_unchecked(&bytes[index.start..]) }
        } else {
            panic!(
                "index out of bounds: the len is {} but the index is {}",
                bytes.len(),
                index.start
            );
        }
    }
}

/// Local reproduction of the (unstable) `core::clone::CloneToUninit` trait.
///
/// # Safety
///
/// Implementors must guarantee `clone_to_uninit` initialises `dest` for
/// `size_of_val(self)` bytes.
pub unsafe trait CloneToUninit {
    /// Performs copy-assignment from `self` to `dest`.
    ///
    /// # Safety
    ///
    /// `dest` must be valid for writes for `size_of_val(self)` bytes, and
    /// properly aligned to `align_of_val(self)`.
    unsafe fn clone_to_uninit(&self, dest: *mut u8);
}

unsafe impl CloneToUninit for [u8] {
    #[rapx::verify]
    #[rapx::requires(NonNull(dest))]
    unsafe fn clone_to_uninit(&self, dest: *mut u8) {
        // SAFETY: `dest` is valid for `self.len()` writes by the caller's
        // contract; `self` is a valid `&[u8]`. The two ranges are disjoint
        // because `self` is a shared reference and `dest` is a fresh output.
        unsafe { std::ptr::copy_nonoverlapping(self.as_ptr(), dest, self.len()) };
    }
}

unsafe impl CloneToUninit for CStr {
    #[rapx::verify]
    #[rapx::requires(NonNull(dest))]
    unsafe fn clone_to_uninit(&self, dest: *mut u8) {
        // SAFETY: For now, CStr is just a `#[repr(transparent)] [u8]` with some
        // invariants. And we can cast `[u8]` to `[u8]` on all supported
        // platforms (see: to_bytes_with_nul). The pointer metadata properly
        // preserves the length (so NUL is also copied).
        unsafe { self.to_bytes_with_nul().clone_to_uninit(dest) }
    }
}
