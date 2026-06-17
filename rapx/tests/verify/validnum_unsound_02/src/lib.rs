#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidNum(_denom != 0), kind = "precond")]
unsafe fn require_nonzero_denom(_denom: usize) {}

// UNSOUND: the call may receive zero.
#[rapx::verify]
pub fn unsound_missing_nonzero_guard(denom: usize) {
    unsafe {
        require_nonzero_denom(denom);
    }
}
