#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(_src, u32, 1), kind = "precond")]
#[rapx::requires(InBound(_dst, u32, 1), kind = "precond")]
unsafe fn require_copy_nonoverlapping_one(_src: *const u32, _dst: *mut u32) {}

// SOUND: simulates copying one element when both source and destination indices are guarded.
#[rapx::verify]
pub fn sound_copy_nonoverlapping_one(src: &[u32], dst: &mut [u32], i: usize, j: usize) {
    if i < src.len() && j < dst.len() {
        let src_ptr = src.as_ptr().wrapping_add(i);
        let dst_ptr = dst.as_mut_ptr().wrapping_add(j);

        unsafe {
            require_copy_nonoverlapping_one(src_ptr, dst_ptr);
        }
    }
}
