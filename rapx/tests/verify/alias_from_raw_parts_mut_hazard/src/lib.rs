#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem;
use std::slice;

/// SOUND: `&mut u16` → `from_raw_parts_mut` → `&mut [u8]`.
#[rapx::verify]
pub fn as_bytes_mut_sound(x: &mut u16) -> &mut [u8] {
    unsafe { slice::from_raw_parts_mut(x as *mut u16 as *mut u8, mem::size_of::<u16>()) }
}

/// SOUND: `&u16` → `from_raw_parts` → `&[u8]`.
#[rapx::verify]
pub fn as_bytes_sound(x: &u16) -> &[u8] {
    unsafe { slice::from_raw_parts(x as *const u16 as *const u8, mem::size_of::<u16>()) }
}

/// UNSOUND: `&u16` → `from_raw_parts_mut` → `&mut [u8]`, shared→mutable.
#[rapx::verify]
pub fn as_bytes_mut_unsound(x: &u16) -> &mut [u8] {
    unsafe { slice::from_raw_parts_mut(x as *const u16 as *mut u8, mem::size_of::<u16>()) }
}

/// UNSOUND: `*mut u16` → `from_raw_parts_mut`, has NonNull/ValidPtr/Init/Alive
/// but *missing Alias* hazard contract.
#[rapx::verify]
#[rapx::requires(NonNull(ptr))]
#[rapx::requires(ValidPtr(ptr, u8, 2))]
#[rapx::requires(Init(ptr, u8, 2))]
#[rapx::requires(Alive(ptr, 'a))]
pub unsafe fn as_bytes_mut_ptr_missing_alias<'a>(ptr: *mut u16) -> &'a mut [u8] {
    unsafe { slice::from_raw_parts_mut(ptr.cast::<u8>(), mem::size_of::<u16>()) }
}

/// UNSOUND: same as above with explicit `len`, but *missing Alias*.
#[rapx::verify]
#[rapx::requires(NonNull(ptr))]
#[rapx::requires(ValidPtr(ptr, u8, len * 2))]
#[rapx::requires(Init(ptr, u8, len * 2))]
#[rapx::requires(Alive(ptr, 'a))]
pub unsafe fn as_bytes_mut_ptr_len_missing_alias<'a>(
    ptr: *mut u16,
    len: usize,
) -> &'a mut [u8] {
    unsafe { slice::from_raw_parts_mut(ptr.cast::<u8>(), len * mem::size_of::<u16>()) }
}
