#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[repr(C)]
pub struct Pair {
    head: u32,
    tail: u32,
}

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_u32(_ptr: *const u32) {}

#[rapx::verify]
pub fn sound_repr_c_field(pair: &Pair) {
    let ptr = &pair.tail as *const u32;

    unsafe {
        require_align_u32(ptr);
    }
}
