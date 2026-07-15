#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ops::Range;

#[rapx::requires(InBound(index_access(_slice, _range)), kind = "precond")]
unsafe fn require_slice_range<T>(_slice: &[T], _range: Range<usize>) {}

// SOUND: the half-open range is ordered and its end is inside the slice.
#[rapx::verify]
pub fn sound_range_index_guard(data: &[u32], start: usize, end: usize) {
    if start <= end && end <= data.len() {
        unsafe {
            require_slice_range(data, start..end);
        }
    }
}
