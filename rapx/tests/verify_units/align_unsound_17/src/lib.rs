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

// UNSOUND: T may require u64/u128 alignment, but the source may be u8/u16.
#[rapx::verify]
pub fn unsound_contract_type_param_binds_generic<T: SmallAlign, U: WideAlign>(data: &[T]) {
    let ptr = data.as_ptr() as *const U;

    unsafe {
        require_align::<U>(ptr);
    }
}
