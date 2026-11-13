#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// (1) Unsafe callee with a `requires` contract: the checkpoint must still be
//     enforced even when the callee is inlined.
#[rapx::requires(ValidPtr(ptr, u32, 1))]
#[rapx::verify]
pub unsafe fn read_ptr(ptr: *const u32) -> u32 {
    unsafe { *ptr }
}

#[rapx::verify]
pub fn nonnull_caller(ptr: *const u32) -> u32 {
    if ptr.is_null() {
        0
    } else {
        unsafe { read_ptr(ptr) }
    }
}

// A real allocation, rather than a null check, establishes ValidPtr.
#[rapx::verify]
pub fn sound_caller() -> u32 {
    let value = 7u32;
    unsafe { read_ptr(&value) }
}

#[rapx::verify]
pub fn unsound_caller(ptr: *const u32) -> u32 {
    unsafe { read_ptr(ptr) }
}

// (2) Unsafe callee whose return value (0/1) depends on a parameter; the caller
//     uses it to guard an `InBound` access. Inlining the callee must propagate
//     the branch so `return == 1` ⟹ `idx < len`.
#[rapx::verify]
pub unsafe fn is_within(idx: usize, len: usize) -> usize {
    if idx < len {
        1
    } else {
        0
    }
}

#[rapx::verify]
pub fn caller_uses_pred(idx: usize, data: &[u32]) -> u32 {
    if unsafe { is_within(idx, data.len()) } == 1 {
        unsafe { *data.as_ptr().add(idx) }
    } else {
        0
    }
}
