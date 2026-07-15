#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: std range indexing is guarded by `start <= end <= data.len()`.
#[rapx::verify]
pub fn sound_std_range_get_unchecked(data: &[u32], start: usize, end: usize) -> usize {
    if start <= end && end <= data.len() {
        unsafe { data.get_unchecked(start..end).len() }
    } else {
        0
    }
}
