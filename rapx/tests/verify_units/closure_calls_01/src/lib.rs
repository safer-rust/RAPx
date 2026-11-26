#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidNum(value > 0))]
unsafe fn require_positive(value: u32) { let _ = value; }

#[rapx::verify]
pub fn direct_closure(input: u32) {
    let value = || input | 1;
    unsafe { require_positive(value()) };
}

struct Token(u32);

impl Drop for Token {
    fn drop(&mut self) {}
}

#[rapx::verify]
pub fn direct_once_closure(input: u32) {
    let token = Token(input | 1);
    let consume = move || {
        let value = token.0;
        drop(token);
        value
    };
    unsafe { require_positive(consume()) };
}

#[rapx::verify]
pub fn generic_callback<F: FnMut(&mut u32)>(mut callback: F) {
    let mut value = 1_u32;
    callback(&mut value);
    unsafe { require_positive(value) };
}

#[rapx::verify]
pub fn generic_callback_checked<F: FnMut(&mut u32)>(mut callback: F) {
    let mut value = 1_u32;
    callback(&mut value);
    if value > 0 {
        unsafe { require_positive(value) };
    }
}

struct Pair { value: u32, other: u32 }

#[rapx::verify]
pub fn generic_field_callback<F: FnMut(&mut u32)>(mut callback: F) {
    let mut pair = Pair { value: 1, other: 1 };
    callback(&mut pair.value);
    unsafe { require_positive(pair.value) };
}

#[rapx::verify]
pub fn generic_field_callback_keeps_other<F: FnMut(&mut u32)>(mut callback: F) {
    let mut pair = Pair { value: 1, other: 1 };
    callback(&mut pair.value);
    unsafe { require_positive(pair.other) };
}

#[rapx::verify]
pub fn generic_readonly_callback<F: FnMut(&u32)>(mut callback: F) {
    let value = 1_u32;
    callback(&value);
    unsafe { require_positive(value) };
}

#[rapx::verify]
pub fn generic_bool_callback<F: FnMut(u32) -> bool>(mut callback: F) {
    let value = callback(0) as u32;
    if value > 0 {
        unsafe { require_positive(value) };
    }
}

#[rapx::verify]
pub fn generic_numeric_callback<F: FnMut(u32) -> u32>(mut callback: F) {
    unsafe { require_positive(callback(0)) };
}

#[rapx::verify]
pub fn generic_numeric_checked<F: FnMut(u32) -> u32>(mut callback: F) {
    let value = callback(0);
    if value > 0 {
        unsafe { require_positive(value) };
    }
}

#[rapx::verify]
pub fn generic_once_callback<F: FnOnce() -> u32>(callback: F) {
    unsafe { require_positive(callback()) };
}

#[rapx::verify]
pub fn array_map_closure(input: u32) {
    let values = [(); 2].map(|_| input | 1);
    unsafe { require_positive(values[0]) };
}

#[rapx::verify]
pub fn array_map_generic<const N: usize>(input: u32) {
    let values = [(); N].map(|_| input | 1);
    if let Some(value) = values.first() {
        unsafe { require_positive(*value) };
    }
}

#[rapx::verify]
pub fn array_map_generic_bad<const N: usize>() {
    let values = [(); N].map(|_| 0_u32);
    if N > 0 {
        unsafe { require_positive(values[0]) };
    }
}

#[rapx::verify]
pub fn array_map_generic_first_bad<const N: usize>() {
    let values = [(); N].map(|_| 0_u32);
    if let Some(value) = values.first() {
        unsafe { require_positive(*value) };
    }
}

#[rapx::verify]
pub fn array_simple_generic<const N: usize>() {
    let values = [1_u32; N];
    if N > 0 {
        unsafe { require_positive(values[0]) };
    }
}

#[rapx::verify]
pub fn array_simple_generic_bad<const N: usize>() {
    let values = [0_u32; N];
    if N > 0 {
        unsafe { require_positive(values[0]) };
    }
}
