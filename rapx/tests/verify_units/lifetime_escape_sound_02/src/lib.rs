#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(slice_index_methods)]

use std::slice::SliceIndex;

/// SOUND: the returned `&'a mut T` is re-borrowed from `s: &'a mut [T]`, the
/// same region, like `<[T]>::get_unchecked_mut`.
#[rapx::verify]
#[rapx::requires(InBound(s, i))]
pub unsafe fn same_region_mut<'a, T>(s: &'a mut [T], i: usize) -> &'a mut T {
    unsafe { &mut *i.get_unchecked_mut(s) }
}
