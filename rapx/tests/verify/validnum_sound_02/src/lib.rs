#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidNum(_denom != 0), kind = "precond")]
unsafe fn require_nonzero_denom(_denom: usize) {}

// SOUND: the non-zero precondition is explicitly guarded.
#[rapx::verify]
pub fn sound_guarded_nonzero(denom: usize) {
    if denom != 0 {
        unsafe {
            require_nonzero_denom(denom);
        }
    }
}
