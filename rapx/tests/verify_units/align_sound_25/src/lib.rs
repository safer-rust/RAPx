#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Align(_ptr, T), kind = "precond")]
unsafe fn require_align<T>(_ptr: *const T) {}

// SOUND: contract type parameter T is instantiated to concrete u32 at callsite.
#[rapx::verify]
pub fn sound_contract_type_param_binds_concrete(data: &[u32]) {
    let ptr = data.as_ptr();

    unsafe {
        require_align::<u32>(ptr);
    }
}
