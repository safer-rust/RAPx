#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem;
use std::slice;

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
