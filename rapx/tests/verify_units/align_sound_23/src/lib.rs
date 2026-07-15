#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

pub struct Zst;

#[rapx::requires(Align(_ptr, Zst), kind = "precond")]
unsafe fn require_zst_align(_ptr: *const Zst) {}

#[rapx::verify]
pub fn sound_zst_trivial_alignment(ptr: *const Zst) {
    unsafe {
        require_zst_align(ptr);
    }
}
