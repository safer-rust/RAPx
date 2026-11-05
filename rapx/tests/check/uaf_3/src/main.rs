#![allow(unused)]

use std::mem::forget;

fn main() {
    let mut b1 = Box::new(99);
    let p = &mut *b1 as *mut i32;
    let other = unsafe { Box::from_raw(p) };
    let moved = other;
    let _moved_again = moved;
    panic!();
    forget(b1);
}
