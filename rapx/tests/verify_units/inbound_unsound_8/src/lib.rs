#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(_ptr, u32, 1), kind = "precond")]
unsafe fn require_inbound(_ptr: *const u32) {}

#[rapx::verify]
pub fn unsound_inclusive_range_off_by_one() {
    let arr = [10, 20, 30, 40];
    let ptr = arr.as_ptr();
    for i in 0..=arr.len() {
        let current = unsafe { ptr.offset(i as isize) };
        unsafe {
            require_inbound(current);
        }
    }
}
