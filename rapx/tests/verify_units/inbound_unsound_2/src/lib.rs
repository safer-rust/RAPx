#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(_ptr, u32, 2), kind = "precond")]
unsafe fn require_from_raw_parts_two(_ptr: *const u32) {}

// UNSOUND: non-empty is not enough to construct a two-element slice.
#[rapx::verify]
pub fn unsound_from_raw_parts_two_only_nonempty(data: &[u32]) {
    if data.len() > 0 {
        let ptr = data.as_ptr();

        unsafe {
            require_from_raw_parts_two(ptr);
        }
    }
}
