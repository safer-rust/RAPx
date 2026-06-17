#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

pub trait SmallAlign {}
impl SmallAlign for u8 {}
impl SmallAlign for u16 {}

pub trait WideAlign {}
impl WideAlign for u64 {}
impl WideAlign for u128 {}

#[rapx::requires(ValidNum(align_of(T) <= align_of(U)), kind = "precond")]
unsafe fn require_alignment_order<T: SmallAlign, U: WideAlign>() {}

// SOUND: all local SmallAlign candidates have weaker alignment than WideAlign candidates.
#[rapx::verify]
pub fn sound_trait_bound_align_order<T: SmallAlign, U: WideAlign>() {
    unsafe {
        require_alignment_order::<T, U>();
    }
}
