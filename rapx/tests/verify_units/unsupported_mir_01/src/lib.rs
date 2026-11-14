#![feature(register_tool, core_intrinsics)]
#![register_tool(rapx)]
#![allow(dead_code, internal_features)]

use std::arch::asm;

unsafe extern "C" {
    safe fn external_clobber(value: &mut u32);
}

#[rapx::requires(ValidNum(value != 0))]
unsafe fn need_nonzero(value: u32) {}

#[rapx::verify]
pub fn unknown_inline_asm_write() {
    let mut value = 1_u32;
    unsafe { asm!("xor {reg:e}, {reg:e}", reg = inout(reg) value); }
    unsafe { need_nonzero(value); }
}

#[rapx::verify]
pub fn unknown_external_call_without_mir() {
    let mut value = 1_u32;
    external_clobber(&mut value);
    unsafe { need_nonzero(value); }
}

#[rapx::verify]
pub fn unknown_fnmut_writes_argument<F: FnMut(&mut u32)>(mut callback: F) {
    let mut value = 1_u32;
    callback(&mut value);
    unsafe { need_nonzero(value); }
}

#[rapx::verify]
pub fn unsound_intrinsic_copy() {
    let source = 0_u32;
    let mut destination = 1_u32;
    unsafe { std::intrinsics::copy_nonoverlapping(&source, &mut destination, 1); }
    unsafe { need_nonzero(destination); }
}

#[rapx::verify]
pub unsafe fn unsound_direct_intrinsic_copy(pointer: *mut u32) {
    unsafe { std::intrinsics::copy_nonoverlapping(pointer, pointer, 1) };
}

#[rapx::verify]
pub unsafe fn unknown_direct_assume() {
    unsafe { std::intrinsics::assume(false) };
}
