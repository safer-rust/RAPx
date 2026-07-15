#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code, unused_assignments)]

#[derive(Clone, Copy)]
pub enum Selector {
    First,
    Second,
}

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_arg0(_ptr: *const u32) {}

// SOUND: named contract parameter `_ptr` must bind to this callsite argument.
#[rapx::verify]
pub fn sound_named_contract_binds_callsite_arg(data: &[u32]) {
    let ptr = data.as_ptr();

    unsafe {
        require_align_arg0(ptr);
    }
}
