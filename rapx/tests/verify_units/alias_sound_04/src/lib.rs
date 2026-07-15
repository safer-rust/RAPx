#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

pub struct RawBuf {
    ptr: *mut u32,
    len: usize,
}

impl RawBuf {
    fn as_slice_mut<'a>(&self) -> &'a mut [u32] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, self.len) }
    }
}

// SOUND: the struct exposes a mutable slice and then uses only that slice.
#[rapx::verify]
pub fn sound_struct_slice_only(data: &mut [u32]) -> u32 {
    let raw = RawBuf {
        ptr: data.as_mut_ptr(),
        len: data.len(),
    };
    let slice = raw.as_slice_mut();
    if !slice.is_empty() {
        slice[0] = 7;
        slice[0]
    } else {
        0
    }
}
