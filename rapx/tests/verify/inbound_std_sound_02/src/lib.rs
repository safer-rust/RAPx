#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: the symbolic `count` is bounded by both source and destination lengths.
#[rapx::verify]
pub fn sound_std_copy_nonoverlapping(src: &[u32], dst: &mut [u32], count: usize) {
    if count <= src.len() && count <= dst.len() {
        unsafe {
            std::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), count);
        }
    }
}
