#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 2), kind = "precond")]
unsafe fn require_two_allocated_u32(_ptr: *const u32) {}

// SOUND: the slice guard establishes that two elements are backed by the slice allocation.
#[rapx::verify]
pub fn sound_slice_prefix_allocated(data: &[u32]) {
    if data.len() >= 2 {
        let ptr = data.as_ptr();

        unsafe {
            require_two_allocated_u32(ptr);
        }
    }
}
