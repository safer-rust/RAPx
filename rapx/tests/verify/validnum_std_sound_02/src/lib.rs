#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: copy count is constant and fits the `size_of(T) * count` numeric bound.
#[rapx::verify]
pub fn sound_std_copy_nonoverlapping_validnum(src: &[u32], dst: &mut [u32]) {
    if src.len() >= 1 && dst.len() >= 1 {
        unsafe {
            std::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), 1);
        }
    }
}
