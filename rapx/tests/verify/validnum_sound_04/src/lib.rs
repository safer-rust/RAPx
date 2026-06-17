#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

pub trait TinyElem {}
impl TinyElem for u8 {}
impl TinyElem for u16 {}

#[rapx::requires(ValidNum(size_of(T) * _len <= isize::MAX), kind = "precond")]
unsafe fn require_slice_layout_limit<T: TinyElem>(_len: usize) {}

// SOUND: every TinyElem candidate is small and the length is bounded.
#[rapx::verify]
pub fn sound_trait_bound_size_limit<T: TinyElem>(len: usize) {
    if len <= 1024 {
        unsafe {
            require_slice_layout_limit::<T>(len);
        }
    }
}
