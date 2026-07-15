#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(_src, u32, 1), kind = "precond")]
#[rapx::requires(InBound(_dst, u32, 1), kind = "precond")]
unsafe fn require_copy_nonoverlapping_one(_src: *const u32, _dst: *mut u32) {}

// UNSOUND: source is guarded, but destination index is not.
#[rapx::verify]
pub fn unsound_copy_nonoverlapping_dst_unguarded(src: &[u32], dst: &mut [u32], i: usize, j: usize) {
    if i < src.len() {
        let src_ptr = unsafe { src.as_ptr().add(i) };
        let dst_ptr = unsafe { dst.as_mut_ptr().add(j) };

        unsafe {
            require_copy_nonoverlapping_one(src_ptr, dst_ptr);
        }
    }
}
