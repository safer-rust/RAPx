#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: `copy_nonoverlapping` receives overlapping source and destination ranges.
#[rapx::verify]
pub fn unsound_copy_nonoverlapping_overlap(data: &mut [u32; 4]) {
    let src = data.as_ptr();
    let dst = unsafe { data.as_mut_ptr().add(1) };
    unsafe {
        std::ptr::copy_nonoverlapping(src, dst, 2);
    }
}
