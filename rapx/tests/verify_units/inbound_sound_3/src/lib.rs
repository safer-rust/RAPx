#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(_ptr, T, 1), kind = "precond")]
unsafe fn require_get_unchecked_like<T>(_ptr: *const T) {}

// SOUND: simulates `slice::get_unchecked::<T>(index)` with a generic pointee type.
#[rapx::verify]
pub fn sound_get_unchecked_generic<T>(data: &[T], index: usize) {
    if index < data.len() {
        let ptr = data.as_ptr();
        let current = ptr.wrapping_add(index);

        unsafe {
            require_get_unchecked_like::<T>(current);
        }
    }
}
