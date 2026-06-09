#![feature(register_tool)]
#![register_tool(rapx)]

use std::mem::MaybeUninit;

// Local unsafe APIs used to exercise the property-specific SMT lowerings.
//
// They deliberately do not read from the pointer. This keeps each fixture
// focused on one required property instead of pulling in the full std
// `ptr::read` contract.
#[rapx::requires(InBound(0, u32, 1), kind = "precond")]
unsafe fn require_in_bound_arg0(_ptr: *const u32) {}

#[rapx::requires(Init(0, u32, 1), kind = "precond")]
unsafe fn require_init_arg0(_ptr: *const u32) {}

// Positive InBound case.
//
// The path condition `index < data.len()` should be enough to prove that the
// one-element pointer produced by `data.as_ptr().add(index)` is in bounds for
// `data`.
#[rapx::verify]
pub fn checked_slice_add(data: &[u32], index: usize) {
    if index < data.len() {
        let ptr = data.as_ptr();
        let current = unsafe { ptr.add(index) };

        unsafe {
            require_in_bound_arg0(current);
        }
    }
}

// Negative InBound case.
//
// There is no bounds guard, so the verifier should keep the result Unknown.
#[rapx::verify]
pub fn unchecked_slice_add(data: &[u32], index: usize) {
    let ptr = data.as_ptr();
    let current = unsafe { ptr.add(index) };

    unsafe {
        require_in_bound_arg0(current);
    }
}

// Positive Init case.
//
// A direct `ptr.write(value)` initializes one `u32` at `ptr`. The first Init
// lowering only targets this local one-element pattern; loop accumulation still
// needs a real loop summary.
#[rapx::verify]
pub fn write_then_require_init(value: u32) {
    let mut slot = MaybeUninit::<u32>::uninit();
    let ptr = slot.as_mut_ptr();

    unsafe {
        ptr.write(value);
        require_init_arg0(ptr);
    }
}
