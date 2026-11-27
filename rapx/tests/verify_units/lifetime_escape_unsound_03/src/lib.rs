#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(slice_index_methods)]

use std::slice::SliceIndex;

/// UNSOUND: the returned `&'a mut T` points into `s: &'b mut [T]`, but `'a`
/// is not tied to `'b`, so the caller can use the slice again while the
/// returned `&mut` is still alive. The `&mut` version of
/// `lifetime_escape_unsound_02`.
#[rapx::verify]
#[rapx::requires(InBound(s, i))]
pub unsafe fn extend_mut_via_call<'a, 'b, T>(s: &'b mut [T], i: usize) -> &'a mut T {
    unsafe { &mut *i.get_unchecked_mut(s) }
}
