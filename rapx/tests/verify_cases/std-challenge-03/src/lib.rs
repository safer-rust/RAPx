#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(offset_of_enum)]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]

use std::ptr;
use std::slice;

// ========================================================================
// Challenge 3: Verifying raw pointer arithmetic operations.
//
// The safety of code that relies on `*const T` / `*mut T` arithmetic
// (`add`, `sub`, `offset`, ...) and eventual raw-pointer access is proven by
// verifying safe abstractions that call these std methods directly.  Each
// unsafe call site is checked against the callee's bundled contract
// (`InBound`, `ValidPtr`, `Align`, ...), so the whole obligation chain stays
// self-contained within this crate.
// ========================================================================

/// `[u8]::is_ascii` (core::slice) — scans the bytes, relying on `*const T::add`
/// followed by a raw read.
#[rapx::verify]
pub fn is_ascii_ext(s: &[u8]) -> bool {
    let len = s.len();
    let ptr = s.as_ptr();
    let mut i = 0;
    while i < len {
        unsafe {
            if *ptr.add(i) >= 0x80 {
                return false;
            }
        }
        i += 1;
    }
    true
}

/// `Vec::swap_remove` (alloc::vec) — swaps the element at `index` with the last
/// element and removes the last, relying on `*const T::add` / `*mut T::add`.
///
/// `T: Copy` mirrors the `swap_remove` fast path: reading the element out
/// (`ptr::read`) is sound without an aliasing hazard because copying leaves the
/// original bit pattern intact.
#[rapx::verify]
pub fn swap_remove_ext<T: Copy>(v: &mut [T], index: usize) -> T {
    let len = v.len();
    assert!(index < len);
    unsafe {
        let value = ptr::read(v.as_ptr().add(index));
        let base = v.as_mut_ptr();
        ptr::copy(base.add(len - 1), base.add(index), 1);
        value
    }
}

/// `String::remove` (alloc::string) — removes the UTF-8 character at byte
/// position `idx` by copying the tail leftwards with `ptr::copy`, relying on
/// `*const T::add` / `*mut T::add` to compute the source and destination.
#[rapx::verify]
pub fn remove_ext(bytes: &mut [u8], idx: usize, ch_len: usize) {
    let len = bytes.len();
    assert!(idx < len);
    assert!(ch_len > 0);
    let next = idx + ch_len;
    assert!(next <= len);
    unsafe {
        ptr::copy(
            bytes.as_ptr().add(next),
            bytes.as_mut_ptr().add(idx),
            len - next,
        );
    }
}

/// `VecDeque::swap` (alloc::collections::vec_deque) — swaps the elements at
/// logical indices `i` and `j`, relying on `*mut T::add` to translate the
/// logical indices into physical ring-buffer indices before `ptr::swap`.
#[rapx::verify]
pub fn vecdeque_swap_ext<T>(buf: &mut [T], head: usize, i: usize, j: usize) {
    let cap = buf.len();
    assert!(i < cap);
    assert!(j < cap);
    let ri = (head + i) % cap;
    let rj = (head + j) % cap;
    let base = buf.as_mut_ptr();
    unsafe {
        ptr::swap(base.add(ri), base.add(rj));
    }
}

/// `Option::as_slice` (core::option) — returns the payload as a one-element
/// slice (`Some`) or an empty slice (`None`), relying on `*const T::byte_add`
/// to compute the payload address from the enum base pointer.
#[rapx::verify]
pub fn as_slice_ext<T>(opt: &Option<T>) -> &[T] {
    let len = if opt.is_some() { 1 } else { 0 };
    unsafe {
        slice::from_raw_parts(
            (opt as *const Option<T>)
                .byte_add(std::mem::offset_of!(Option<T>, Some.0))
                .cast::<T>(),
            len,
        )
    }
}
