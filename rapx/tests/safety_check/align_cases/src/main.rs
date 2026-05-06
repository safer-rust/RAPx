#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]
#![allow(unused_variables)]

//! Focused examples for the current Senryx `Align` checker.
//!
//! The examples are grouped by the kinds of evidence `verification/align.rs`
//! can currently consume:
//!
//! - contract facts from RAPx annotations,
//! - direct pointer/object layout compatibility,
//! - pointer arithmetic summaries proved with Z3,
//! - path refinement from `ptr.is_aligned()`.
//!
//! Comments use "Senryx Align: Pass/Fail" to describe the expected result of
//! the alignment property only. Other contracts on the same unsafe API, such as
//! `ValidPtr` or `Typed`, may still fail until their checkers are stronger.

/// Senryx Align: Pass.
///
/// The caller precondition is stored as a contract fact on `ptr`, so
/// `ptr.read()` can discharge its `Align(ptr, u32)` obligation from facts.
#[rapx::inner(property = Align(ptr, u32), kind = "precond")]
unsafe fn pass_from_align_contract_fact(ptr: *const u32) -> u32 {
    unsafe { ptr.read() }
}

/// Senryx Align: Pass.
///
/// A Rust reference is treated as a trusted aligned source. After it is cast to
/// a raw pointer, the modeled pointee object still has `u32` alignment.
fn pass_from_reference_source(value: &u32) -> u32 {
    let ptr = value as *const u32;
    unsafe { ptr.read() }
}

/// Senryx Align: Pass.
///
/// `ptr.add(index)` advances by `index * size_of::<u32>()`; because `size_of`
/// is a multiple of `align_of::<u32>()`, the Z3 offset proof can show that the
/// derived pointer preserves alignment.
fn pass_from_typed_element_add(data: &[u32], index: usize) -> u32 {
    let ptr = data.as_ptr();
    let shifted = unsafe { ptr.add(index) };
    unsafe { shifted.read() }
}

/// Senryx Align: Pass.
///
/// On the true branch, `ptr.is_aligned()` refines the pointer's abstract
/// alignment state before `ptr.read()` is checked.
fn pass_from_runtime_is_aligned_guard(ptr: *const u32) -> u32 {
    if ptr.is_aligned() {
        unsafe { ptr.read() }
    } else {
        0
    }
}

/// Senryx Align: Fail.
///
/// The source object is byte-aligned (`u8`), but the unsafe read requires
/// `u32` alignment. The direct object-layout check should reject this cast.
fn fail_from_u8_object_cast(bytes: &[u8; 8]) -> u32 {
    let ptr = bytes.as_ptr() as *const u32;
    unsafe { ptr.read() }
}

/// Senryx Align: Fail.
///
/// `byte_add` records a byte-stride pointer offset. With an unconstrained byte
/// offset, Z3 cannot prove that the resulting `*mut u32` remains 4-byte aligned.
fn fail_from_unconstrained_byte_add(data: &mut [u32], byte_offset: usize) -> &'static mut [u32] {
    let ptr = data.as_mut_ptr();
    let shifted = unsafe { ptr.byte_add(byte_offset) };
    unsafe { std::slice::from_raw_parts_mut(shifted, 1) }
}

/// Senryx Align: Fail.
///
/// This branch deliberately reads only when `is_aligned()` is false. The current
/// visitor either refines this path to unaligned or leaves the raw pointer
/// without a positive alignment fact, so the `read` alignment obligation fails.
fn fail_from_negative_is_aligned_guard(ptr: *const u32) -> u32 {
    if !ptr.is_aligned() {
        unsafe { ptr.read() }
    } else {
        0
    }
}

fn main() {}
