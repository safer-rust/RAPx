#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: `from_raw_parts` receives a constant length whose byte size is tiny.
#[rapx::verify]
pub fn sound_std_from_raw_parts_validnum() -> usize {
    let data = [1_u32, 2_u32];
    let ptr = data.as_ptr();
    let slice = unsafe { std::slice::from_raw_parts(ptr, 2) };
    slice.len()
}
