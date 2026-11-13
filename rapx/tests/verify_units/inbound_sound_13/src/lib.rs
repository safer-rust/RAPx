#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// Regression for https://github.com/safer-rust/RAPx/issues/338

// Forming a one-past pointer is permitted; the returned raw pointer is not dereferenced.
#[rapx::verify]
pub fn sound_pushed_vec_one_past_capacity() -> *const u8 {
    let mut data = vec![7u8];
    data.push(8);
    unsafe { data.as_ptr().add(data.capacity()) }
}

#[rapx::verify]
pub fn sound_reserved_vec_one_past_capacity() -> *const u8 {
    let mut data = vec![7u8];
    data.reserve(1);
    unsafe { data.as_ptr().add(data.capacity()) }
}

#[rapx::verify]
pub fn sound_pushed_zst_vec_one_past_capacity() -> *const () {
    let mut data = vec![()];
    data.push(());
    unsafe { data.as_ptr().add(data.capacity()) }
}
