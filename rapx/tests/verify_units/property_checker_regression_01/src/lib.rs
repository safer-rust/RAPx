#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(p, u8, 2))]
unsafe fn needs_two_ref(p: &u8) {}

#[rapx::requires(Allocated(p, u8, 2))]
unsafe fn needs_two_alloc(p: *const u8) {}

#[rapx::requires(Owning(p))]
unsafe fn needs_owner(p: *mut u8) {}

#[rapx::requires(ValidNum(s.is_empty() == 0))]
unsafe fn needs_nonempty(s: &[u8]) {}

#[rapx::verify]
pub fn one_byte_reference() {
    let byte = 0u8;
    unsafe { needs_two_ref(&byte) }
}

#[rapx::verify]
pub fn one_byte_array() {
    let bytes = [0u8; 1];
    unsafe { needs_two_alloc(bytes.as_ptr()) }
}

#[rapx::verify]
pub fn unknown_utf8(bytes: &[u8]) -> &str {
    unsafe { std::str::from_utf8_unchecked(bytes) }
}

#[rapx::verify]
pub unsafe fn unknown_owner(p: *mut u8) {
    unsafe { needs_owner(p) }
}

#[rapx::verify]
pub fn borrowed_not_owner(value: &mut u8) {
    unsafe { needs_owner(value as *mut u8) }
}

#[rapx::verify]
pub fn stack_not_owner() {
    let mut value = 0u8;
    unsafe { needs_owner(&mut value as *mut u8) }
}

#[rapx::verify]
pub fn option_not_owner(ptr: Option<std::ptr::NonNull<u8>>) {
    if let Some(ptr) = ptr {
        unsafe { needs_owner(ptr.as_ptr()) }
    }
}

#[rapx::invariant(Owning(owner.unwrap_some()))]
pub struct TwoFields {
    owner: Option<std::ptr::NonNull<u8>>,
    value: u8,
}

impl TwoFields {
    #[rapx::verify]
    pub fn other_field_is_not_owned(&mut self) {
        unsafe { needs_owner(&mut self.value as *mut u8) }
    }
}

#[rapx::invariant(Owning(owner.unwrap_some()))]
pub struct TwoPointers {
    owner: Option<std::ptr::NonNull<u8>>,
    other: std::ptr::NonNull<u8>,
}

impl TwoPointers {
    #[rapx::verify]
    pub fn other_pointer_is_not_owned(&mut self) {
        unsafe { needs_owner(self.other.as_ptr()) }
    }
}

pub struct RawField {
    ptr: std::ptr::NonNull<u8>,
}

#[rapx::verify]
pub fn owned_struct_does_not_own_pointee(value: RawField) {
    unsafe { needs_owner(value.ptr.as_ptr()) }
}

#[rapx::requires(Owning(p))]
#[rapx::verify]
pub unsafe fn owner_from_precondition(p: *mut u8) {
    unsafe { needs_owner(p) }
}

#[rapx::requires(Owning(p))]
#[rapx::verify]
pub unsafe fn offset_is_not_owner(p: *mut u8) {
    unsafe { needs_owner(p.wrapping_add(1)) }
}

#[rapx::verify]
pub fn unknown_is_empty(s: &[u8]) {
    unsafe { needs_nonempty(s) }
}

// External CString buffers have an unknown extent in the VM. The legacy
// unbounded sentinel must not prove either of these range requirements.
#[rapx::requires(InBound(p, i8, 2))]
unsafe fn needs_two_external_inbound(p: *const i8) {}

#[rapx::requires(Allocated(p, i8, 2))]
unsafe fn needs_two_external_allocated(p: *const i8) {}

#[rapx::verify]
pub fn unknown_external_inbound(data: std::ffi::CString) {
    unsafe { needs_two_external_inbound(data.as_ptr()) }
}

#[rapx::verify]
pub fn unknown_external_allocated(data: std::ffi::CString) {
    unsafe { needs_two_external_allocated(data.as_ptr()) }
}

#[rapx::requires(Allocated(p, u8, 3))]
unsafe fn needs_three_alloc(p: *const u8) {}

#[rapx::invariant(Allocated(ptr, u8, 2))]
pub struct TwoByteBuffer {
    ptr: std::ptr::NonNull<u8>,
}

impl TwoByteBuffer {
    #[rapx::verify]
    pub fn covered_range(&self) {
        unsafe { needs_two_alloc(self.ptr.as_ptr()) }
    }

    #[rapx::verify]
    pub fn unknown_suffix(&self) {
        unsafe { needs_three_alloc(self.ptr.as_ptr()) }
    }

    #[rapx::verify]
    pub fn unknown_prefix(&self) -> *mut u8 {
        unsafe { self.ptr.as_ptr().sub(2) }
    }
}
