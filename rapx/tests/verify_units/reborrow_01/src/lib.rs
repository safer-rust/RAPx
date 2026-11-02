#![feature(register_tool, reborrow)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::marker::{CoerceShared, PhantomData, Reborrow};

struct Mutable<'a>(u8, PhantomData<&'a mut ()>);

#[derive(Clone, Copy)]
struct Shared<'a>(u8, PhantomData<&'a mut ()>);

impl<'a> Reborrow for Mutable<'a> {}
impl<'a> CoerceShared<Shared<'a>> for Mutable<'a> {}

struct MutableRef<'a>(&'a mut u8);

#[derive(Clone, Copy)]
struct SharedRef<'a>(&'a u8);

impl<'a> Reborrow for MutableRef<'a> {}
impl<'a> CoerceShared<SharedRef<'a>> for MutableRef<'a> {}

#[rapx::requires(ValidNum(value == 1))]
unsafe fn expect_one(value: u8) {}

#[rapx::verify]
pub fn shared_reborrow_sound() {
    let wrapper = Mutable(1, PhantomData);
    let shared: Shared<'_> = wrapper;
    unsafe { expect_one(shared.0) };
}

#[rapx::verify]
pub fn shared_reborrow_unsound() {
    let wrapper = Mutable(0, PhantomData);
    let shared: Shared<'_> = wrapper;
    unsafe { expect_one(shared.0) };
}

#[rapx::verify]
pub fn reference_field_reborrow_sound(value: &mut u8) {
    *value = 1;
    let wrapper = MutableRef(value);
    let shared: SharedRef<'_> = wrapper;
    unsafe { expect_one(*shared.0) };
}

#[rapx::verify]
pub fn reference_field_reborrow_unsound(value: &mut u8) {
    *value = 0;
    let wrapper = MutableRef(value);
    let shared: SharedRef<'_> = wrapper;
    unsafe { expect_one(*shared.0) };
}
