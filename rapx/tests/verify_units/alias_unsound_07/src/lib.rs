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
#[rapx::verify]
pub fn unsound_cross_function_raw_write(data: &mut [u32]) -> u32 {
    let ptr = data.as_mut_ptr();
    let slice = make_mut_slice(ptr, data.len());
    if !slice.is_empty() {
        raw_write(ptr, 21);
        slice[0]
    } else {
        0
    }
}
