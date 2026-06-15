#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: `get_unchecked(index)` is guarded by `index < data.len()`.
#[rapx::verify]
pub fn sound_std_get_unchecked(data: &[u32], index: usize) -> u32 {
    if index < data.len() {
        unsafe { *data.get_unchecked(index) }
    } else {
        0
    }
}
