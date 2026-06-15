#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

pub trait SmallAlign {}
impl SmallAlign for u8 {}
impl SmallAlign for u16 {}

pub trait WideAlign {}
impl WideAlign for u64 {}
impl WideAlign for u128 {}

#[rapx::requires(Align(_ptr, T), kind = "precond")]
unsafe fn require_align<T>(_ptr: *const T) {}

// SOUND: U's guaranteed alignment is stronger than every T candidate.
#[rapx::verify]
pub fn sound_contract_type_param_binds_generic<T: SmallAlign, U: WideAlign>(data: &[U]) {
    let ptr = data.as_ptr() as *const T;

    unsafe {
        require_align::<T>(ptr);
    }
}
