#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidNum(_a + _b < _cap), kind = "precond")]
unsafe fn require_sum_below_cap(_a: usize, _b: usize, _cap: usize) {}

// UNSOUND: guarding only `a < cap` says nothing about `a + b`.
#[rapx::verify]
pub fn unsound_partial_sum_guard(a: usize, b: usize, cap: usize) {
    if a < cap {
        unsafe {
            require_sum_below_cap(a, b, cap);
        }
    }
}
