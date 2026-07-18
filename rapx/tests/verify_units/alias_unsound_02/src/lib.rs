#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

/// UNSOUND: the original raw pointer is used while a mutable slice alias is live.
#[rapx::requires(NonNull(ptr))]
#[rapx::requires(ValidPtr(ptr, u32, len))]
#[rapx::requires(Align(ptr, u32))]
#[rapx::requires(Init(ptr, u32, len))]
#[rapx::requires(Typed(ptr, u32))]
#[rapx::requires(Alive(ptr))]
#[rapx::requires(Owning(ptr))]
#[rapx::requires(ValidNum(size_of(u32) * len <= isize::MAX))]
#[rapx::verify]
pub unsafe fn unsound_mut_slice_then_raw_read(ptr: *mut u32, len: usize) -> u32 {
    let slice = unsafe { std::slice::from_raw_parts_mut(ptr, len) };

    if !slice.is_empty() {
        slice[0] = 1;
        let read_back = unsafe { *ptr };
        slice[0] + read_back
    } else {
        0
    }
}
