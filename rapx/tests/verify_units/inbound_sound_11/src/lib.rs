#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(_ptr, u32, 2), kind = "precond")]
unsafe fn require_inbound_u32_two(_ptr: *const u32) {}

// SOUND: Vec::from_raw_parts retakes ownership of a non-empty allocation; the
// reconstructed Vec still points at >= 2 initialized u32s.
#[rapx::verify]
pub fn sound_vec_from_raw_parts_inbound(mut data: Vec<u32>) {
    if data.len() >= 2 {
        let ptr = data.as_mut_ptr();
        let len = data.len();
        let cap = data.capacity();
        std::mem::forget(data);

        let owned = unsafe { Vec::from_raw_parts(ptr, len, cap) };
        unsafe {
            require_inbound_u32_two(owned.as_ptr());
        }
        std::mem::forget(owned);
    }
}
