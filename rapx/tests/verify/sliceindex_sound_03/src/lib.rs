#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: std `get_unchecked` receives a scalar index protected by `index < len`.
#[rapx::verify]
pub fn sound_std_get_unchecked_sliceindex(data: &[u32], index: usize) -> u32 {
    if index < data.len() {
        unsafe { *data.get_unchecked(index) }
    } else {
        0
    }
}
