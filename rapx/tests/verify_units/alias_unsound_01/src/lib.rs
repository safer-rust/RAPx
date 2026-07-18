#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

/// UNSOUND: the raw pointer mutates memory while a shared slice from the same pointer is live.
#[rapx::requires(NonNull(ptr))]
#[rapx::requires(ValidPtr(ptr, u32, len))]
#[rapx::requires(Align(ptr, u32))]
#[rapx::requires(Init(ptr, u32, len))]
#[rapx::requires(Alive(ptr))]
#[rapx::requires(Owning(ptr))]
#[rapx::requires(ValidNum(size_of(u32) * len <= isize::MAX))]
#[rapx::verify]
pub unsafe fn unsound_shared_slice_then_raw_write(ptr: *mut u32, len: usize) -> u32 {
    let slice = unsafe { std::slice::from_raw_parts(ptr, len) };

    if !slice.is_empty() {
        unsafe {
            *ptr = 9;
        }
        slice[0]
    } else {
        0
    }
}
