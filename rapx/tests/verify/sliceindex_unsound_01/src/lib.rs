#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidNum(index_access(_slice, _index)), kind = "precond")]
unsafe fn require_slice_index<T>(_slice: &[T], _index: usize) {}

// UNSOUND: the guard checks a different value from the index used by the API.
#[rapx::verify]
pub fn unsound_scalar_index_wrong_guard(data: &[u32], index: usize, other: usize) {
    if other < data.len() {
        unsafe {
            require_slice_index(data, index);
        }
    }
}
