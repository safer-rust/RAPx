#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: `from_raw_parts` creates a shared slice and the raw pointer is not used to mutate it.
#[rapx::verify]
pub fn sound_shared_slice_no_raw_mutation(data: &[u32]) -> u32 {
    let ptr = data.as_ptr();
    let slice = unsafe { std::slice::from_raw_parts(ptr, data.len()) };
    slice.first().copied().unwrap_or(0)
}
