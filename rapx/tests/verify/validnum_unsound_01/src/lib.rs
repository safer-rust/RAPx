#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidNum(_a < _b), kind = "precond")]
unsafe fn require_less_than(_a: usize, _b: usize) {}

// UNSOUND: the required relation is never checked before the unsafe call.
#[rapx::verify]
pub fn unsound_missing_less_than_guard(a: usize, b: usize) {
    unsafe {
        require_less_than(a, b);
    }
}
