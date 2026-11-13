#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(slice_index_methods)]

use std::slice::SliceIndex;

// UNSOUND: the pointer is one byte past an in-bounds element, so it is
// misaligned whenever `align_of::<I::Output>() > 1`. The pointee type in the
// generic MIR is the projection `<I as SliceIndex<[T]>>::Output`, whose
// alignment used to fall back to 1, so this was reported as `Align | Proved`.
#[rapx::verify]
#[rapx::requires(InBound(s, index))]
pub unsafe fn unsound_projection_pointee<T, I: SliceIndex<[T]>>(s: &[T], index: I) -> &I::Output
where
    I::Output: Sized,
{
    let p = unsafe { index.get_unchecked(s) } as *const u8;
    unsafe { &*(p.wrapping_add(1) as *const I::Output) }
}

// SOUND: the same shape as `<[T]>::get_unchecked`.
#[rapx::verify]
#[rapx::requires(InBound(s, index))]
pub unsafe fn sound_projection_pointee<T, I: SliceIndex<[T]>>(s: &[T], index: I) -> &I::Output {
    unsafe { &*index.get_unchecked(s) }
}
