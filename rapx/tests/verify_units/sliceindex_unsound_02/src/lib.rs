#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ops::Range;

#[rapx::requires(InBound(_slice, _range), kind = "precond")]
unsafe fn require_slice_range<T>(_slice: &[T], _range: Range<usize>) {}

// UNSOUND: the start is guarded, but the range end may exceed the slice length.
#[rapx::verify]
pub fn unsound_range_index_missing_end_guard(data: &[u32], start: usize, end: usize) {
    if start <= data.len() {
        unsafe {
            require_slice_range(data, start..end);
        }
    }
}
