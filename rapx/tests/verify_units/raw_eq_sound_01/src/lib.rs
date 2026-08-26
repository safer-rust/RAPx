#![feature(register_tool)]
#![feature(core_intrinsics)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: `u64` has no padding bytes, so `raw_eq`'s `NoPadding(u64)` holds.
#[rapx::verify]
pub unsafe fn sound_raw_eq_no_padding(a: &u64, b: &u64) -> bool {
    unsafe { core::intrinsics::raw_eq(a, b) }
}
