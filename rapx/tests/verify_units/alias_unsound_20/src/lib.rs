#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem;
use std::slice;

/// UNSOUND: same as above with explicit `len`, but *missing Alias*.
#[rapx::verify]
#[rapx::requires(NonNull(ptr))]
#[rapx::requires(ValidPtr(ptr, u8, len * 2))]
#[rapx::requires(Init(ptr, u8, len * 2))]
#[rapx::requires(Alive(ptr, 'a))]
#[rapx::requires(Owning(ptr))]
pub unsafe fn as_bytes_mut_ptr_len_missing_alias<'a>(
    ptr: *mut u16,
    len: usize,
) -> &'a mut [u8] {
    unsafe { slice::from_raw_parts_mut(ptr.cast::<u8>(), len * mem::size_of::<u16>()) }
}
