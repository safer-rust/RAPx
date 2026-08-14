#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use rapx_macros::pred;

// A named contract: `p` points to `n` live, `T`-aligned, initialized elements —
// the precondition for reading a byte slice through a raw pointer.
pred!(Readable(p: Ptr, T: Ty, n: Expr) { NonNull(p) && Align(p, T) && Allocated(p, T, n) && Init(p, T, n) });

#[rapx::requires(Readable(ptr, u8, len))]
unsafe fn read_byte(ptr: *const u8, len: usize) -> u8 {
    unsafe { *ptr }
}

#[rapx::verify]
pub fn sound_read(buf: &[u8]) -> u8 {
    unsafe { read_byte(buf.as_ptr(), buf.len()) }
}
