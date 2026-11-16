#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(slice_index_methods)]

// Regression for https://github.com/safer-rust/RAPx/issues/334

use std::slice::SliceIndex;

/// UNSOUND: the returned `&'a T` points into `s: &'b [T]`, but `'a` is not
/// tied to `'b`, so the caller can keep the reference after the slice is freed.
/// Unlike `lifetime_escape_unsound_01`, the raw pointer is the return value of
/// a call, not a cast of the parameter.
#[rapx::verify]
#[rapx::requires(InBound(s, i))]
pub unsafe fn extend_via_call<'a, 'b, T>(s: &'b [T], i: usize) -> &'a T {
    unsafe { &*i.get_unchecked(s) }
}
