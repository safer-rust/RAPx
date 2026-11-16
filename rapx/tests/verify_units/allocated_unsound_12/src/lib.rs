#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(slice_index_methods)]
#![feature(ptr_metadata)]

// Regression for https://github.com/safer-rust/RAPx/issues/339

use std::ptr;
use std::slice::SliceIndex;

// UNSOUND: the pointer has the start of `a` and the length of `b`. Each one is
// in bounds of `s`, but the mix can go past the end (e.g. `a = 2..3`,
// `b = 0..4` on a slice of length 4). `I` stays generic, so the pointee type is
// `I::Output`, as in `<[T]>::get_unchecked`.
#[rapx::verify]
#[rapx::requires(InBound(s, a))]
#[rapx::requires(InBound(s, b))]
pub unsafe fn unsound_mixed_span<T, I: SliceIndex<[T]>>(s: &[T], a: I, b: I) -> &I::Output {
    let pa = unsafe { a.get_unchecked(s) };
    let pb = unsafe { b.get_unchecked(s) };
    let q: *const I::Output = ptr::from_raw_parts(pa as *const (), ptr::metadata(pb));
    unsafe { &*q }
}

// SOUND: dereference the result itself.
#[rapx::verify]
#[rapx::requires(InBound(s, a))]
#[rapx::requires(InBound(s, b))]
pub unsafe fn sound_same_span<T, I: SliceIndex<[T]>>(s: &[T], a: I, b: I) -> &I::Output {
    let pa = unsafe { a.get_unchecked(s) };
    let _pb = unsafe { b.get_unchecked(s) };
    unsafe { &*pa }
}
