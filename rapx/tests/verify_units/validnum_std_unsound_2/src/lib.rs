#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: the copy count can violate the `size_of(T) * count <= isize::MAX` bound.
#[rapx::verify]
pub fn unsound_std_copy_nonoverlapping_validnum(src: &[u32], dst: &mut [u32]) {
    unsafe {
        std::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), usize::MAX);
    }
}
