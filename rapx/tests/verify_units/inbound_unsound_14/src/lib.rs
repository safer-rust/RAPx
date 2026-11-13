#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// Regression for https://github.com/safer-rust/RAPx/issues/338

// A large offset can exceed the allocation after Vec growth.
#[rapx::verify]
pub fn unsound_pushed_vec_far_add() -> *const u8 {
    let mut data = vec![7u8];
    data.push(8);
    unsafe { data.as_ptr().add(1024) }
}

// Reserving additional capacity does not permit arbitrary offsets.
#[rapx::verify]
pub fn unsound_reserved_vec_far_add() -> *const u8 {
    let mut data = vec![7u8];
    data.reserve(1);
    unsafe { data.as_ptr().add(1024) }
}

// capacity() + 1 exceeds the one-past boundary.
#[rapx::verify]
pub fn unsound_pushed_vec_past_capacity() -> *const u8 {
    let mut data = vec![7u8];
    data.push(8);
    unsafe { data.as_ptr().add(data.capacity() + 1) }
}
