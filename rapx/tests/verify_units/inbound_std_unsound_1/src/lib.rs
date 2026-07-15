#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: the guard checks `other`, but `get_unchecked` uses `index`.
#[rapx::verify]
pub fn unsound_std_get_unchecked_wrong_guard(
    data: &[u32],
    index: usize,
    other: usize,
) -> u32 {
    if other < data.len() {
        unsafe { *data.get_unchecked(index) }
    } else {
        0
    }
}
