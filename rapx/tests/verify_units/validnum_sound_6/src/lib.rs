#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidNum(_a + _b < _cap), kind = "precond")]
unsafe fn require_sum_below_cap(_a: usize, _b: usize, _cap: usize) {}

// SOUND: the checked-add temporary is guarded before the unsafe call.
#[rapx::verify]
pub fn sound_guarded_variable_sum(a: usize, b: usize, cap: usize) {
    let sum = a + b;
    if sum < cap {
        unsafe {
            require_sum_below_cap(a, b, cap);
        }
    }
}
