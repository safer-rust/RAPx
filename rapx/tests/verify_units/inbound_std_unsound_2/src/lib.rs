#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: `count` is bounded by the source length, but not by the destination length.
#[rapx::verify]
pub fn unsound_std_copy_nonoverlapping_dst_unguarded(
    src: &[u32],
    dst: &mut [u32],
    count: usize,
) {
    if count <= src.len() {
        unsafe {
            std::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), count);
        }
    }
}
