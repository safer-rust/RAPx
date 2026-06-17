#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidNum(_a < _b), kind = "precond")]
unsafe fn require_less_than(_a: usize, _b: usize) {}

// SOUND: the call is dominated by the same `<` guard required by the callee.
#[rapx::verify]
pub fn sound_guarded_less_than(a: usize, b: usize) {
    if a < b {
        unsafe {
            require_less_than(a, b);
        }
    }
}
