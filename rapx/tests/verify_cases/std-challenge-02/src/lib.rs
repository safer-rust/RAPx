#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]
#![allow(unused_comparisons)]

use std::mem::{self, MaybeUninit};
use std::ptr;

/// ptr::copy_nonoverlapping — copies `count` elements from `src` to `dst`.
#[rapx::verify]
#[rapx::requires(Align(src, T))]
#[rapx::requires(Align(dst, T))]
#[rapx::requires(ValidPtr(src, T, count))]
#[rapx::requires(ValidPtr(dst, T, count))]
#[rapx::requires(NonOverlap(dst, src, T, count))]
unsafe fn copy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize) {
    if mem::size_of::<T>() == 0 {
        return;
    }
    ptr::copy_nonoverlapping(src, dst, count);
}

/// ptr::copy — copies `count` elements from `src` to `dst`, may overlap.
#[rapx::verify]
#[rapx::requires(Align(src, T))]
#[rapx::requires(Align(dst, T))]
#[rapx::requires(ValidPtr(src, T, count))]
#[rapx::requires(ValidPtr(dst, T, count))]
unsafe fn copy<T>(src: *const T, dst: *mut T, count: usize) {
    if mem::size_of::<T>() == 0 {
        return;
    }
    ptr::copy(src, dst, count);
}

/// ptr::swap — swaps two elements via a stack-local temporary.
#[rapx::verify]
#[rapx::requires(Align(x, T))]
#[rapx::requires(Align(y, T))]
#[rapx::requires(ValidPtr(x, T, 1))]
#[rapx::requires(ValidPtr(y, T, 1))]
pub unsafe fn swap<T>(x: *mut T, y: *mut T) {
    if mem::size_of::<T>() == 0 {
        return;
    }
    let mut tmp = MaybeUninit::<T>::uninit();
    unsafe {
        copy_nonoverlapping(x, tmp.as_mut_ptr(), 1);
        copy(y, x, 1);
        copy_nonoverlapping(tmp.as_ptr(), y, 1);
    }
}

/// ptr::swap_nonoverlapping — swaps `count` elements, no overlap.
#[rapx::verify]
#[rapx::requires(Align(x, T))]
#[rapx::requires(Align(y, T))]
#[rapx::requires(ValidPtr(x, T, count))]
#[rapx::requires(ValidPtr(y, T, count))]
#[rapx::requires(NonOverlap(x, y, T, count))]
pub unsafe fn swap_nonoverlapping<T>(x: *mut T, y: *mut T, count: usize) {
    if mem::size_of::<T>() == 0 || count == 0 {
        return;
    }
    let mut i = 0;
    while i < count {
        unsafe {
            let mut tmp = MaybeUninit::<T>::uninit();
            copy_nonoverlapping(x.add(i), tmp.as_mut_ptr(), 1);
            copy_nonoverlapping(y.add(i), x.add(i), 1);
            copy_nonoverlapping(tmp.as_ptr(), y.add(i), 1);
        }
        i += 1;
    }
}

/// mem::swap — safe wrapper, mirrors `core::mem::swap`.
#[rapx::verify]
pub fn mem_swap<T>(x: &mut T, y: &mut T) {
    unsafe { swap(x as *mut T, y as *mut T) };
}

/// MaybeUninit::zeroed — mirrors `core::mem::MaybeUninit::zeroed`.
#[rapx::verify]
pub fn zeroed<T>() -> MaybeUninit<T> {
    let mut u = MaybeUninit::<T>::uninit();
    if mem::size_of::<T>() > 0 {
        unsafe { ptr::write_bytes(u.as_mut_ptr(), 0u8, 1) };
    }
    u
}

/// copy_from_slice — mirrors `[T]::copy_from_slice`.
#[rapx::verify]
pub fn copy_from_slice<T: Copy>(dest: &mut [T], src: &[T]) {
    assert!(dest.len() == src.len());
    if dest.is_empty() {
        return;
    }
    unsafe {
        ptr::copy_nonoverlapping(src.as_ptr(), dest.as_mut_ptr(), dest.len());
    }
}

/// mem::size_of_val — mirrors `core::mem::size_of_val`.
#[rapx::verify]
pub fn size_of_val<T: ?Sized>(val: &T) -> usize {
    mem::size_of_val(val)
}

/// mem::align_of_val — mirrors `core::mem::align_of_val`.
#[rapx::verify]
pub fn align_of_val<T: ?Sized>(val: &T) -> usize {
    mem::align_of_val(val)
}

/// mem::min_align_of_val — mirrors deprecated `core::mem::min_align_of_val`.
#[rapx::verify]
pub fn min_align_of_val<T: ?Sized>(val: &T) -> usize {
    mem::align_of_val(val)
}
