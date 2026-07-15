#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidNum(_a + _b < _cap), kind = "precond")]
unsafe fn require_sum_below_cap(_a: usize, _b: usize, _cap: usize) {}

// SOUND: the arithmetic predicate is true after binding all callsite constants.
#[rapx::verify]
pub fn sound_constant_sum_below_cap() {
    unsafe {
        require_sum_below_cap(1, 2, 4);
    }
}
