#![feature(register_tool)]
#![feature(core_intrinsics)]
#![register_tool(rapx)]
#![allow(dead_code)]

// A struct with trailing padding: `u64` at offset 0, `u8` at offset 8, size 16.
pub struct Padded {
    a: u64,
    b: u8,
}

// UNSOUND: `Padded` has 7 trailing padding bytes, so `raw_eq`'s `NoPadding`
// requirement is violated — comparing the uninitialized padding bytes is UB.
#[rapx::verify]
pub unsafe fn unsound_raw_eq_padded(a: &Padded, b: &Padded) -> bool {
    unsafe { core::intrinsics::raw_eq(a, b) }
}
