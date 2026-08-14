#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: for a sized `u32`, `size_of(u32) == 0` is false, so the else branch
// `_len` is selected and `_len <= _cap` is not guarded at the callsite.
#[rapx::requires(ValidNum((if size_of(u32) == 0 { 0 } else { _len }) <= _cap), kind = "precond")]
unsafe fn require_sized_ifelse(_len: usize, _cap: usize) {}

#[rapx::verify]
pub fn unsound_sized_ifelse(len: usize, cap: usize) {
    unsafe { require_sized_ifelse(len, cap); }
}
