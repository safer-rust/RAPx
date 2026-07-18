#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem;
use std::slice;

/// UNSOUND: `*const u16` → `from_raw_parts_mut` → `&mut [u8]`, missing Alias hazard.
#[rapx::requires(NonNull(ptr))]
#[rapx::requires(ValidPtr(ptr, u8, 2))]
#[rapx::requires(Align(ptr, u8))]
#[rapx::requires(Init(ptr, u8, 2))]
#[rapx::requires(Alive(ptr, 'a))]
#[rapx::requires(Owning(ptr))]
#[rapx::verify]
pub unsafe fn as_bytes_mut_unsound<'a>(ptr: *const u16) -> &'a mut [u8] {
    unsafe { slice::from_raw_parts_mut(ptr as *mut u8, mem::size_of::<u16>()) }
}
