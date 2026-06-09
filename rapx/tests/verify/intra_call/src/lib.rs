#![feature(register_tool)]
#![register_tool(rapx)]

use std::mem::MaybeUninit;

// Local unsafe APIs used as focused verification targets.
//
// These calls make callee summaries observable at the caller boundary without
// mixing in the full std pointer-read contract.
#[rapx::requires(InBound(_ptr, u32, 1), kind = "precond")]
unsafe fn require_in_bound_arg0(_ptr: *const u32) {}

#[rapx::requires(Init(_ptr, u32, 1), kind = "precond")]
unsafe fn require_init_arg0(_ptr: *const u32) {}

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_arg0(_ptr: *const u32) {}

// A transparent helper whose return value depends on both arguments.
//
// A synthesized summary should export:
//   ret = data.as_ptr().add(index)
//   ret comes from the slice object
fn slice_add(data: &[u32], index: usize) -> *const u32 {
    let ptr = data.as_ptr();
    unsafe { ptr.add(index) }
}

// Positive transitive return-dependency case.
//
// The caller establishes `index < data.len()`. The callee summary should carry
// the slice object, length, and pointer-add relation back to the caller, so the
// caller can prove InBound for the returned pointer.
#[rapx::verify]
pub fn transitive_slice_add(data: &[u32], index: usize) {
    if index < data.len() {
        let current = slice_add(data, index);
        unsafe {
            require_in_bound_arg0(current);
        }
    }
}

// Negative transitive return-dependency case.
//
// The callee still returns `data.as_ptr().add(index)`, but the caller provides no
// bounds guard. The summary should not turn this into a must InBound fact.
#[rapx::verify]
pub fn transitive_slice_add_without_guard(data: &[u32], index: usize) {
    let current = slice_add(data, index);
    unsafe {
        require_in_bound_arg0(current);
    }
}

// A callee with two return alternatives guarded by a branch.
//
// Summary merge should not flatten the return relation into one arbitrary fact:
//   flag == true  => ret = data.as_ptr().add(index)
//   flag == false => ret = data.as_ptr()
// Both alternatives come from the same slice object, but they have different
// offsets.
fn choose_slice_ptr(data: &[u32], index: usize, flag: bool) -> *const u32 {
    let ptr = data.as_ptr();
    if flag {
        unsafe { ptr.add(index) }
    } else {
        ptr
    }
}

// Guarded-return positive case.
//
// If `index < data.len()`, both return alternatives are in bounds for one
// element: `ptr.add(index)` is guarded by the index check, and the base pointer
// alternative is in bounds because the same guard implies the slice is nonempty.
#[rapx::verify]
pub fn choose_slice_ptr_guarded(data: &[u32], index: usize, flag: bool) {
    if index < data.len() {
        let current = choose_slice_ptr(data, index, flag);
        unsafe {
            require_in_bound_arg0(current);
        }
    }
}

// Guarded-return negative case.
//
// Without a guard, neither alternative can be promoted to a must InBound fact.
#[rapx::verify]
pub fn choose_slice_ptr_without_guard(data: &[u32], index: usize, flag: bool) {
    let current = choose_slice_ptr(data, index, flag);
    unsafe {
        require_in_bound_arg0(current);
    }
}

// A callee whose write effect is conditional.
//
// Summary merge should produce a guarded effect:
//   flag == true  => Init(ptr, u32, 1)
//   flag == false => no write
// and a may-write effect for `ptr`.
fn maybe_write(ptr: *mut u32, value: u32, flag: bool) {
    if flag {
        unsafe {
            ptr.write(value);
        }
    }
}

// Conditional write with a known true guard.
//
// The caller passes `true`, so the guarded Init effect can be used after summary
// instantiation.
#[rapx::verify]
pub fn maybe_write_known_true(value: u32) {
    let mut slot = MaybeUninit::<u32>::uninit();
    let ptr = slot.as_mut_ptr();

    maybe_write(ptr, value, true);

    unsafe {
        require_init_arg0(ptr);
    }
}

// Conditional write with an unknown guard.
//
// The callee may or may not initialize the slot. A sound merge must keep Init as
// guarded rather than promoting it to a must postcondition.
#[rapx::verify]
pub fn maybe_write_unknown_flag(value: u32, flag: bool) {
    let mut slot = MaybeUninit::<u32>::uninit();
    let ptr = slot.as_mut_ptr();

    maybe_write(ptr, value, flag);

    unsafe {
        require_init_arg0(ptr);
    }
}

// Pointer arithmetic through a callee using `sub`.
//
// This fixture prevents the summary design from being tied only to `ptr.add`.
// The summary should represent pointer arithmetic generically, including the
// direction and stride of the operation.
fn slice_from_end(data: &[u32], back: usize) -> *const u32 {
    let end = unsafe { data.as_ptr().add(data.len()) };
    unsafe { end.sub(back) }
}

#[rapx::verify]
pub fn sub_from_slice_end(data: &[u32], back: usize) {
    if back > 0 && back <= data.len() {
        let current = slice_from_end(data, back);
        unsafe {
            require_in_bound_arg0(current);
        }
    }
}

// Pointer arithmetic through a callee using `offset`.
//
// `offset(0)` should preserve the base pointer address and object. This is a
// small alignment-oriented fixture for non-add pointer arithmetic.
fn offset_zero(ptr: *const u32) -> *const u32 {
    unsafe { ptr.offset(0) }
}

#[rapx::verify]
pub fn offset_zero_preserves_align(data: &[u32]) {
    let ptr = data.as_ptr();
    let current = offset_zero(ptr);
    unsafe {
        require_align_arg0(current);
    }
}
