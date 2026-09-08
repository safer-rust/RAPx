#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// `index - 1` lies in `[0, len)` when `index >= 1` and the caller contract
// establishes `InBound(data, index)` (i.e. `index < data.len()`), so the
// function is sound.
#[rapx::verify]
#[rapx::requires(InBound(data, index))]
pub unsafe fn derived_index_minus_one(data: &[u32], index: usize) -> u32 {
    if index >= 1 {
        unsafe { *data.get_unchecked(index - 1) }
    } else {
        0
    }
}
