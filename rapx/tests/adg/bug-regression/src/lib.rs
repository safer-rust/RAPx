#![feature(allocator_api)]
use std::alloc::Global;
// nested type
// fuzzable check should not cause stack overflow
pub struct A {
    pub a: Vec<A>,
    pub b: Vec<A>,
}

pub fn dummy(a: A) {}

pub fn higher_order_trait<T>()
where
    for<'a> &'a T: Default,
{
}
