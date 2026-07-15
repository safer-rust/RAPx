#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

pub struct Marker;

#[rapx::requires(ValidPtr(_ptr, T, _len), kind = "precond")]
unsafe fn require_valid_ptr<T>(_ptr: *const T, _len: usize) {}

// SOUND: ZST pointers satisfy ValidPtr through the Size(T, 0) branch.
#[rapx::verify]
pub fn sound_zst_dangling_valid_for_any_len(len: usize) {
    let ptr = std::ptr::NonNull::<Marker>::dangling().as_ptr();

    unsafe {
        require_valid_ptr::<Marker>(ptr, len);
    }
}
