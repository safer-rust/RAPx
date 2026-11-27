#![feature(register_tool)]
#![register_tool(rapx)]

/// UNSOUND: the same escape as `lifetime_escape_unsound_03`, but the `&mut`
/// view is produced by `from_raw_parts_mut` instead of a raw-pointer deref.
#[rapx::verify]
pub unsafe fn extend_mut_view<'a, 'b, T>(s: &'b mut [T]) -> &'a mut [T] {
    unsafe { std::slice::from_raw_parts_mut(s.as_mut_ptr(), s.len()) }
}
