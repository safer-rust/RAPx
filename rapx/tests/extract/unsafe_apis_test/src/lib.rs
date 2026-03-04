/// Dereferences a raw pointer.
///
/// # Safety
///
/// The pointer must be valid and non-null.
pub unsafe fn deref_raw(ptr: *const u8) -> u8 {
    *ptr
}

pub struct MyStruct;

impl MyStruct {
    /// Creates an instance from a raw pointer.
    ///
    /// # Safety
    ///
    /// The pointer must point to a valid `MyStruct`.
    pub unsafe fn from_raw(ptr: *mut MyStruct) -> &'static mut MyStruct {
        &mut *ptr
    }
}
