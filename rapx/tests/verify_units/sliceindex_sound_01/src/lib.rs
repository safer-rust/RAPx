#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(index_access(_slice, _index)), kind = "precond")]
unsafe fn require_slice_index<T>(_slice: &[T], _index: usize) {}

// SOUND: the scalar slice index is guarded by the matching slice length.
#[rapx::verify]
pub fn sound_scalar_index_guard(data: &[u32], index: usize) {
    if index < data.len() {
        unsafe {
            require_slice_index(data, index);
        }
    }
}
