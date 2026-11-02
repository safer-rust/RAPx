#![feature(register_tool, core_intrinsics, repr_simd, uint_carryless_mul)]
#![cfg_attr(not(rapx_ge_100), feature(funnel_shifts))]
#![register_tool(rapx)]
#![allow(dead_code, internal_features, unnecessary_transmutes, unused_variables)]

#[rapx::requires(ValidNum(value != 0))]
unsafe fn need_nonzero(value: u32) {}

#[repr(simd)]
#[derive(Clone, Copy)]
struct I8x16([i8; 16]);

#[repr(simd)]
#[derive(Clone, Copy)]
struct U32x16([u32; 16]);

#[repr(simd)]
#[derive(Clone, Copy)]
struct I32x4([i32; 4]);

#[repr(simd)]
#[derive(Clone, Copy)]
struct F32x4([f32; 4]);

#[repr(simd)]
#[derive(Clone, Copy)]
struct Ptrx4([*const i32; 4]);

#[repr(simd)]
#[derive(Clone, Copy)]
struct MutPtrx4([*mut i32; 4]);

#[repr(simd)]
#[derive(Clone, Copy)]
struct Isizex4([isize; 4]);

#[repr(simd)]
#[derive(Clone, Copy)]
struct Usizex4([usize; 4]);

mod atomic;
mod integer;
mod layout;
mod math;
mod memory;
mod simd;
