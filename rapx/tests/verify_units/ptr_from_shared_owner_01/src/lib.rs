#![feature(register_tool)]
#![register_tool(rapx)]

use std::{rc::Rc, sync::Arc};

#[rapx::verify]
pub fn rc_new_roundtrip() {
    let raw = Rc::into_raw(Rc::new(7_u8));
    unsafe { drop(Rc::from_raw(raw)); }
}

#[rapx::verify]
pub fn arc_new_roundtrip() {
    let raw = Arc::into_raw(Arc::new(7_u8));
    unsafe { drop(Arc::from_raw(raw)); }
}

#[rapx::verify]
pub fn rc_count_roundtrip() {
    let raw = Rc::into_raw(Rc::new(7_u8));
    unsafe {
        Rc::increment_strong_count(raw);
        Rc::decrement_strong_count(raw);
        drop(Rc::from_raw(raw));
    }
}

#[rapx::verify]
pub fn arc_count_roundtrip() {
    let raw = Arc::into_raw(Arc::new(7_u8));
    unsafe {
        Arc::increment_strong_count(raw);
        Arc::decrement_strong_count(raw);
        drop(Arc::from_raw(raw));
    }
}

#[rapx::verify]
pub fn rc_count_exhausted() {
    let raw = Rc::into_raw(Rc::new(7_u8));
    unsafe {
        Rc::decrement_strong_count(raw);
        drop(Rc::from_raw(raw));
    }
}

#[rapx::verify]
pub fn arc_count_exhausted() {
    let raw = Arc::into_raw(Arc::new(7_u8));
    unsafe {
        Arc::decrement_strong_count(raw);
        drop(Arc::from_raw(raw));
    }
}

#[rapx::verify]
pub fn raw_pointer_argument(raw: *const u8) {
    unsafe { drop(Rc::from_raw(raw)); }
}

#[rapx::verify]
pub fn rc_reference_argument(owner: &Rc<u8>) {
    let raw = Rc::into_raw(Rc::clone(owner));
    unsafe { drop(Rc::from_raw(raw)); }
}

#[rapx::verify]
pub fn reused_raw_with_other_share(owner: &Rc<u8>) {
    let first = Rc::into_raw(Rc::clone(owner));
    let second = Rc::into_raw(Rc::clone(owner));
    unsafe {
        drop(Rc::from_raw(first));
        drop(Rc::from_raw(first));
        drop(Rc::from_raw(second));
    }
}

struct CustomHeader<T> { strong: usize, value: T }
struct CustomRc<T> { ptr: *mut CustomHeader<T> }

impl<T> CustomRc<T> {
    #[rapx::requires(ValidNum(strong_ref_count(ptr, strong) > rc_owner_count(ptr, CustomRc)))]
    unsafe fn check_raw(ptr: *mut CustomHeader<T>) {
        let _ = ptr;
    }
}

#[rapx::verify]
pub fn custom_owner_contract() {
    let mut header = CustomHeader { strong: 1, value: 7_u8 };
    unsafe { CustomRc::<u8>::check_raw(&mut header); }
}
