#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: for a generic `T`, `size_of(T)` resolves to 0 in the contract, so the
// if-else takes the `0` branch and the bound is trivially satisfied.
#[rapx::requires(ValidNum((if size_of(T) == 0 { 0 } else { _len }) <= _cap), kind = "precond")]
unsafe fn require_zst_ifelse<T>(_len: usize, _cap: usize) {}

#[rapx::verify]
pub fn sound_zst_ifelse<T>(len: usize, cap: usize) {
    unsafe { require_zst_ifelse::<T>(len, cap); }
}
