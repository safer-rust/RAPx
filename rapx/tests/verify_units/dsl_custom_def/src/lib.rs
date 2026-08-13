#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use rapx_macros::def_contract;

// Define a new contract tag with Rust function syntax (proc-macro),
// without recompiling rapx.
#[def_contract]
fn my_safe_read(p: Ptr, T: Ty, n: Expr) -> bool {
    NonNull(p) && Align(p, T) && Allocated(p, T, n)
}

// The unsafe callee references the custom tag `my_safe_read` in its precondition.
#[rapx::requires(my_safe_read(ptr, u8, len))]
pub unsafe fn read_byte(ptr: *const u8, len: usize) -> u8 {
    unsafe { *ptr }
}

// SOUND: a valid slice yields a non-null, aligned, allocated pointer.
#[rapx::verify]
pub fn sound_read(buf: &[u8]) -> u8 {
    unsafe { read_byte(buf.as_ptr(), buf.len()) }
}
