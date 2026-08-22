#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]

//! Challenge 13: Safety of `CStr` — a faithful, self-contained port of
//! `core::ffi::c_str`. `CStr` is `#[repr(transparent)]` over `[u8]`; its
//! safety invariant (the challenge's `Invariant`) is a non-empty,
//! null-terminated buffer with no interior nul, encoded by `ValidCStr`.

use std::ops::{Index, RangeFrom};
use std::slice;

/// `#[repr(transparent)]` over `[u8]`, the target's `c_char` representation.
#[repr(transparent)]
#[rapx::invariant(ValidCStr(inner, inner.len()))]
pub struct CStr {
    inner: [u8],
}

/// An error indicating that a nul byte was not in the expected position.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FromBytesWithNulError {
    InteriorNul { position: usize },
    NotNulTerminated,
}

/// An error indicating that no nul byte was present.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FromBytesUntilNulError(());

impl CStr {
    #[rapx::verify]
    pub fn from_bytes_until_nul(bytes: &[u8]) -> Result<&CStr, FromBytesUntilNulError> {
        let nul_pos = bytes.iter().position(|&b| b == 0);
        match nul_pos {
            Some(nul_pos) => {
                // SAFETY: the nul byte is inside the slice, so `nul_pos + 1 <= bytes.len()`.
                let subslice = unsafe { slice::from_raw_parts(bytes.as_ptr(), nul_pos + 1) };
                Ok(unsafe { CStr::from_bytes_with_nul_unchecked(subslice) })
            }
            None => Err(FromBytesUntilNulError(())),
        }
    }

    #[rapx::verify]
    pub fn from_bytes_with_nul(bytes: &[u8]) -> Result<&CStr, FromBytesWithNulError> {
        let nul_pos = bytes.iter().position(|&b| b == 0);
        match nul_pos {
            Some(nul_pos) if nul_pos + 1 == bytes.len() => {
                // SAFETY: there is exactly one nul byte, at the end of the slice.
                Ok(unsafe { CStr::from_bytes_with_nul_unchecked(bytes) })
            }
            Some(position) => Err(FromBytesWithNulError::InteriorNul { position }),
            None => Err(FromBytesWithNulError::NotNulTerminated),
        }
    }

    /// # Safety
    ///
    /// `bytes` must be nul-terminated and contain no interior nul bytes.
    #[rapx::verify]
    #[rapx::requires(ValidCStr(bytes, bytes.len()))]
    pub unsafe fn from_bytes_with_nul_unchecked(bytes: &[u8]) -> &CStr {
        // SAFETY: `CStr` is transparent over `[u8]`; the reborrow preserves the
        // slice metadata, and `ValidCStr` guarantees the buffer is well-formed.
        unsafe { &*(bytes as *const [u8] as *const CStr) }
    }

    /// # Safety
    ///
    /// `ptr` must be non-null and point to a valid, nul-terminated buffer.
    #[rapx::verify]
    #[rapx::requires(Allocated(ptr, u8, 1, global))]
    #[rapx::requires(ValidCStr(ptr, 1))]
    #[rapx::requires(NonNull(ptr))]
    #[rapx::requires(Alias(ptr, return))]
    #[rapx::requires(Alive(ptr, 'a))]
    pub unsafe fn from_ptr<'a>(ptr: *const u8) -> &'a CStr {
        // SAFETY: `ValidCStr` guarantees `ptr` is null-terminated.
        let len = unsafe { strlen(ptr) };
        // SAFETY: `ptr` is valid for `len + 1` bytes (up to and including the nul).
        unsafe { CStr::from_bytes_with_nul_unchecked(slice::from_raw_parts(ptr, len + 1)) }
    }
}

/// # Safety
///
/// `ptr` must point to a valid, nul-terminated buffer.
#[rapx::verify]
#[rapx::requires(ValidCStr(ptr, 1))]
unsafe fn strlen(ptr: *const u8) -> usize {
    let mut len = 0;
    // SAFETY: `ValidCStr` guarantees a nul terminator exists, so the scan terminates.
    while unsafe { *ptr.add(len) } != 0 {
        len += 1;
    }
    len
}

impl CStr {
    #[rapx::verify]
    pub fn as_ptr(&self) -> *const u8 {
        self.inner.as_ptr()
    }

    #[rapx::verify]
    pub fn count_bytes(&self) -> usize {
        self.inner.len() - 1
    }

    #[rapx::verify]
    pub fn is_empty(&self) -> bool {
        // SAFETY: the buffer is non-empty by `ValidCStr`.
        unsafe { *self.inner.as_ptr() == 0 }
    }

    #[rapx::verify]
    pub fn to_bytes(&self) -> &[u8] {
        let bytes = self.to_bytes_with_nul();
        // SAFETY: `to_bytes_with_nul` returns a slice of length at least 1.
        unsafe { slice::from_raw_parts(bytes.as_ptr(), bytes.len() - 1) }
    }

    #[rapx::verify]
    pub fn to_bytes_with_nul(&self) -> &[u8] {
        // SAFETY: `CStr` is transparent over `[u8]`, so the reinterpretation
        // preserves the slice metadata.
        unsafe { &*((&raw const self.inner) as *const [u8]) }
    }

    #[rapx::verify]
    pub fn to_str(&self) -> Result<&str, std::str::Utf8Error> {
        std::str::from_utf8(self.to_bytes())
    }

    #[rapx::verify]
    pub fn bytes(&self) -> Bytes<'_> {
        Bytes::new(self)
    }
}

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

impl Index<RangeFrom<usize>> for CStr {
    type Output = CStr;

    #[rapx::verify]
    fn index(&self, index: RangeFrom<usize>) -> &CStr {
        let bytes = self.to_bytes_with_nul();
        // Check against the length including the nul, so the tail stays non-empty.
        if index.start < bytes.len() {
            // SAFETY: a non-empty tail of a valid `CStr` is still a valid `CStr`.
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
    /// # Safety
    ///
    /// `dest` must be valid for writes for `size_of_val(self)` bytes, and
    /// aligned to `align_of_val(self)`.
    unsafe fn clone_to_uninit(&self, dest: *mut u8);
}

unsafe impl CloneToUninit for [u8] {
    #[rapx::verify]
    #[rapx::requires(NonNull(dest))]
    unsafe fn clone_to_uninit(&self, dest: *mut u8) {
        // SAFETY: `dest` is valid for `self.len()` writes; the ranges are disjoint.
        unsafe { std::ptr::copy_nonoverlapping(self.as_ptr(), dest, self.len()) };
    }
}

unsafe impl CloneToUninit for CStr {
    #[rapx::verify]
    #[rapx::requires(NonNull(dest))]
    unsafe fn clone_to_uninit(&self, dest: *mut u8) {
        // SAFETY: the metadata preserves the length, so the nul is copied too.
        unsafe { self.to_bytes_with_nul().clone_to_uninit(dest) }
    }
}
