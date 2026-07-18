#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

fn make_mut_slice<'a>(ptr: *mut u32, len: usize) -> &'a mut [u32] {
    unsafe { std::slice::from_raw_parts_mut(ptr, len) }
}

fn raw_write(ptr: *mut u32, value: u32) {
    unsafe {
        *ptr = value;
    }
}

// UNSOUND: a helper returns a mutable slice, then another helper writes through the original pointer.
#[rapx::requires(NonNull(ptr))]
#[rapx::requires(ValidPtr(ptr, u32, len))]
#[rapx::requires(Align(ptr, u32))]
#[rapx::requires(Init(ptr, u32, len))]
#[rapx::requires(Alive(ptr))]
#[rapx::requires(Owning(ptr))]
#[rapx::requires(ValidNum(size_of(u32) * len <= isize::MAX))]
#[rapx::verify]
pub unsafe fn unsound_cross_function_raw_write(ptr: *mut u32, len: usize) -> u32 {
    let slice = make_mut_slice(ptr, len);
    if !slice.is_empty() {
        raw_write(ptr, 21);
        slice[0]
    } else {
        0
    }
}
