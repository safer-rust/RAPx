#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::num::NonZero;

#[rapx::requires(ValidNum(_x != 0), kind = "precond")]
unsafe fn require_nonzero(_x: usize) {}

// SOUND: the `NonZero<usize>` type invariant (inner value != 0) discharges
// the `_x != 0` precondition of `require_nonzero` via `nz.get()`.
#[rapx::verify]
pub fn sound_nonzero_type_invariant(nz: NonZero<usize>) {
    unsafe {
        require_nonzero(nz.get());
    }
}
