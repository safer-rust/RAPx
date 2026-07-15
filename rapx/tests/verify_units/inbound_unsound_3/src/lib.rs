#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(_ptr, T, 1), kind = "precond")]
unsafe fn require_get_unchecked_like<T>(_ptr: *const T) {}

// UNSOUND: the guard checks `other`, but the unsafe access uses `index`.
#[rapx::verify]
pub fn unsound_get_unchecked_wrong_guard<T>(data: &[T], index: usize, other: usize) {
    if other < data.len() {
        let ptr = data.as_ptr();
        let current = unsafe { ptr.add(index) };

        unsafe {
            require_get_unchecked_like::<T>(current);
        }
    }
}
