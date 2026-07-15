#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(_ptr, u32, 2), kind = "precond")]
unsafe fn require_from_raw_parts_two(_ptr: *const u32) {}

// SOUND: simulates `slice::from_raw_parts(ptr, 2)` after proving the slice has at least 2 elements.
#[rapx::verify]
pub fn sound_from_raw_parts_prefix_two(data: &[u32]) {
    if data.len() >= 2 {
        let ptr = data.as_ptr();

        unsafe {
            require_from_raw_parts_two(ptr);
        }
    }
}
