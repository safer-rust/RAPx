#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code, unused_assignments)]

use std::mem::ManuallyDrop;

#[rapx::verify]
pub fn sound_reinitialize_after_drop() {
    let mut slot = ManuallyDrop::new(1u32);
    unsafe { ManuallyDrop::drop(&mut slot) };
    slot = ManuallyDrop::new(2u32);
    std::hint::black_box(&slot);
}

#[rapx::verify]
pub fn sound_reinitialize_box_after_drop() {
    let mut slot = ManuallyDrop::new(Box::new(1u8));
    unsafe { ManuallyDrop::drop(&mut slot) };
    slot = ManuallyDrop::new(Box::new(2u8));
    std::hint::black_box(&slot);
}

#[rapx::verify]
pub fn unsound_double_drop_box() {
    let mut slot = ManuallyDrop::new(Box::new(1u8));
    unsafe { ManuallyDrop::drop(&mut slot) };
    unsafe { ManuallyDrop::drop(&mut slot) };
}

#[rapx::verify]
pub fn unsound_branch_drop_then_use(first_branch: bool) {
    let mut first = ManuallyDrop::new(Box::new(1u8));
    let mut other = ManuallyDrop::new(Box::new(2u8));
    let target = if first_branch { &mut first } else { &mut other };
    unsafe { ManuallyDrop::drop(target) };
    if !first_branch {
        std::hint::black_box(&other);
    }
}
