#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 2), kind = "precond")]
unsafe fn require_two_allocated_u32(_ptr: *const u32) {}

// UNSOUND: only one element is backed, but the precondition asks for two.
#[rapx::verify]
pub fn unsound_slice_too_short_for_requested_len() {
    let data = [1_u32];
    let ptr = data.as_ptr();

    unsafe {
        require_two_allocated_u32(ptr);
    }
}
