#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

pub trait WideElem {}
impl WideElem for u64 {}
impl WideElem for u128 {}

#[rapx::requires(ValidNum(size_of(T) * _len <= isize::MAX), kind = "precond")]
unsafe fn require_slice_layout_limit<T: WideElem>(_len: usize) {}

// UNSOUND: the length is unconstrained, so the byte-size bound may fail.
#[rapx::verify]
pub fn unsound_trait_bound_missing_size_limit<T: WideElem>(len: usize) {
    unsafe {
        require_slice_layout_limit::<T>(len);
    }
}
