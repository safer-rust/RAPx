#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidNum(_idx, "[0,_len)"), kind = "precond")]
unsafe fn require_index_interval(_idx: usize, _len: usize) {}

// UNSOUND: `idx <= len` still allows the exclusive upper bound to fail.
#[rapx::verify]
pub fn unsound_interval_inclusive_guard(idx: usize, len: usize) {
    if idx <= len {
        unsafe {
            require_index_interval(idx, len);
        }
    }
}
