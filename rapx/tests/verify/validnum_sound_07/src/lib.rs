#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidNum(_idx, "[0,_len)"), kind = "precond")]
unsafe fn require_index_interval(_idx: usize, _len: usize) {}

// SOUND: interval syntax expands to `0 <= idx && idx < len`.
#[rapx::verify]
pub fn sound_interval_guard(idx: usize, len: usize) {
    if idx < len {
        unsafe {
            require_index_interval(idx, len);
        }
    }
}
