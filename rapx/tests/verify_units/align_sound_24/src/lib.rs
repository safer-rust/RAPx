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

// SOUND: &[U] is at least 8-byte aligned, which satisfies every T candidate.
#[rapx::verify]
pub fn sound_trait_bound_cross_cast<T: SmallAlign, U: WideAlign>(data: &[U]) {
    let ptr = data.as_ptr() as *const T;

    unsafe {
        require_align_u::<T>(ptr);
    }
}
