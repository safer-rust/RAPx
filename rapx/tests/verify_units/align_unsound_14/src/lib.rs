#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[repr(packed)]
pub struct Packed {
    pad: u8,
    value: u32,
}

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_u32(_ptr: *const u32) {}

#[rapx::verify]
pub fn unsound_repr_packed_field(value: &Packed) {
    let ptr = std::ptr::addr_of!(value.value);

    unsafe {
        require_align_u32(ptr);
    }
}
