#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: copy_nonoverlapping copies between disjoint ranges of the same array.
#[rapx::verify]
pub fn sound_copy_nonoverlapping_disjoint(data: &mut [u32; 8]) {
    let src = data.as_ptr();
    let dst = unsafe { data.as_mut_ptr().add(4) };
    unsafe {
        std::ptr::copy_nonoverlapping(src, dst, 4);
    }
}
