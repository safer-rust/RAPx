#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

pub trait SmallAlign {}
impl SmallAlign for u8 {}
impl SmallAlign for u16 {}

pub trait WideAlign {}
impl WideAlign for u64 {}
impl WideAlign for u128 {}

#[rapx::requires(Align(_ptr, U), kind = "precond")]
unsafe fn require_align_u<U>(_ptr: *const U) {}

// UNSOUND: T may be u8/u16 while U may require u64/u128 alignment.
#[rapx::verify]
pub fn unsound_trait_bound_cross_cast<T: SmallAlign, U: WideAlign>(data: &[T]) {
    let ptr = data.as_ptr() as *const U;

    unsafe {
        require_align_u::<U>(ptr);
    }
}
