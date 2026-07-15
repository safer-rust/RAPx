#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[repr(align(8))]
pub struct Align8 {
    value: u32,
}

#[rapx::requires(Align(_ptr, Align8), kind = "precond")]
unsafe fn require_align8(_ptr: *const Align8) {}

#[rapx::verify]
pub fn sound_repr_align_object(value: &Align8) {
    let ptr = value as *const Align8;

    unsafe {
        require_align8(ptr);
    }
}
