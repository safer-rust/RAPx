#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(slice_index_methods)]

// Regression for https://github.com/safer-rust/RAPx/issues/333

use std::ops::Range;
use std::slice::SliceIndex;

// `i` is in bounds of `s`, but the call uses a view of `s` with length 0.
// The view has the same address as `s`, so the `InBound(s, i)` fact used to
// match it.
#[rapx::verify]
#[rapx::requires(InBound(s, i))]
pub unsafe fn unsound_index_into_shorter_view<T>(s: &[T], i: usize) -> &T {
    let view: *const [T] = std::ptr::slice_from_raw_parts(s.as_ptr(), 0);
    unsafe { &*i.get_unchecked(view) }
}

// The same with a range index.
#[rapx::verify]
#[rapx::requires(InBound(s, r))]
pub unsafe fn unsound_range_into_shorter_view<T>(s: &[T], r: Range<usize>) -> &[T] {
    let view: *const [T] = std::ptr::slice_from_raw_parts(s.as_ptr(), 0);
    unsafe { &*r.get_unchecked(view) }
}
