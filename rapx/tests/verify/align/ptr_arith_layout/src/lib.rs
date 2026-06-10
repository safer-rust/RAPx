#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::{align_of, size_of};

#[repr(C)]
pub struct Pair {
    head: u32,
    tail: u32,
}

#[repr(align(8))]
pub struct Align8 {
    value: u32,
}

#[repr(packed)]
pub struct Packed {
    pad: u8,
    value: u32,
}

pub struct Zst;

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_u32(_ptr: *const u32) {}

#[rapx::requires(Align(_ptr, Align8), kind = "precond")]
unsafe fn require_align8(_ptr: *const Align8) {}

#[rapx::requires(Align(_ptr, Zst), kind = "precond")]
unsafe fn require_zst_align(_ptr: *const Zst) {}

// SOUND: add/sub chain preserves alignment when every byte offset is guarded.
// This checks pointer arithmetic beyond a single `ptr.add`.
#[rapx::verify]
pub fn sound_add_sub_chain(data: &[u8], add_a: usize, sub_b: usize) {
    let base = data.as_ptr();

    if (base as usize) % 4 == 0 && add_a % 4 == 0 && sub_b % 4 == 0 {
        let ptr = unsafe { base.add(add_a).sub(sub_b) as *const u32 };
        unsafe {
            require_align_u32(ptr);
        }
    }
}

// UNSOUND: subtracting an arbitrary byte count can break u32 alignment.
// Only the base and first add are guarded here.
#[rapx::verify]
pub fn unsound_sub_missing_guard(data: &[u8], add_a: usize, sub_b: usize) {
    let base = data.as_ptr();

    if (base as usize) % 4 == 0 && add_a % 4 == 0 {
        let ptr = unsafe { base.add(add_a).sub(sub_b) as *const u32 };
        unsafe {
            require_align_u32(ptr);
        }
    }
}

// SOUND: offset(0) preserves a typed slice pointer address.
// This is a non-add pointer arithmetic identity case.
#[rapx::verify]
pub fn sound_offset_zero_preserves_align(data: &[u32]) {
    let ptr = data.as_ptr();
    let shifted = unsafe { ptr.offset(0) };

    unsafe {
        require_align_u32(shifted);
    }
}

// UNSOUND: offsetting a byte pointer by one can produce an unaligned u32 pointer.
// The cast after byte arithmetic must not create an Align fact.
#[rapx::verify]
pub fn unsound_byte_offset_one(data: &[u8]) {
    let base = data.as_ptr();

    if (base as usize) % 4 == 0 {
        let ptr = unsafe { base.offset(1) as *const u32 };
        unsafe {
            require_align_u32(ptr);
        }
    }
}

// SOUND: usize round-trip without address changes preserves a guarded alignment.
// This covers pointer-to-integer-to-pointer transfer.
#[rapx::verify]
pub fn sound_usize_round_trip(data: &[u8]) {
    let base = data.as_ptr();
    let addr = base as usize;

    if addr % align_of::<u32>() == 0 {
        let ptr = addr as *const u32;
        unsafe {
            require_align_u32(ptr);
        }
    }
}

// SOUND: integer address arithmetic is aligned when the byte delta is guarded.
// The pointer is reconstructed only after the arithmetic chain.
#[rapx::verify]
pub fn sound_usize_add_guarded(data: &[u8], offset: usize) {
    let base = data.as_ptr();
    let addr = base as usize;

    if addr % 4 == 0 && offset % 4 == 0 {
        let ptr = (addr + offset) as *const u32;
        unsafe {
            require_align_u32(ptr);
        }
    }
}

// UNSOUND: integer address arithmetic needs an offset-alignment guard.
// A guarded base address alone does not constrain `addr + offset`.
#[rapx::verify]
pub fn unsound_usize_add_missing_offset_guard(data: &[u8], offset: usize) {
    let base = data.as_ptr();
    let addr = base as usize;

    if addr % 4 == 0 {
        let ptr = (addr + offset) as *const u32;
        unsafe {
            require_align_u32(ptr);
        }
    }
}

// SOUND: multiplication/division computes a byte offset divisible by four.
// This stresses arithmetic expressions before reconstructing a pointer.
#[rapx::verify]
pub fn sound_usize_mul_div_offset(data: &[u8], units: usize) {
    let base = data.as_ptr();
    let addr = base as usize;
    let offset = (units * size_of::<u64>()) / 2;

    if addr % 4 == 0 {
        let ptr = (addr + offset) as *const u32;
        unsafe {
            require_align_u32(ptr);
        }
    }
}

// SOUND: repr(C) u32 field address is naturally aligned.
// This checks layout-derived field pointer provenance.
#[rapx::verify]
pub fn sound_repr_c_field(pair: &Pair) {
    let ptr = &pair.tail as *const u32;

    unsafe {
        require_align_u32(ptr);
    }
}

// SOUND: repr(align(8)) object pointer satisfies its own alignment.
// The required type has stricter alignment than the inner u32.
#[rapx::verify]
pub fn sound_repr_align_object(value: &Align8) {
    let ptr = value as *const Align8;

    unsafe {
        require_align8(ptr);
    }
}

// UNSOUND: repr(packed) field pointer may be unaligned for u32.
// `addr_of!` avoids forming an intermediate reference to the packed field.
#[rapx::verify]
pub fn unsound_repr_packed_field(value: &Packed) {
    let ptr = std::ptr::addr_of!(value.value);

    unsafe {
        require_align_u32(ptr);
    }
}

// SOUND: ZST has 1-byte alignment, so the Align obligation is trivial.
// This guards against overfitting all Align checks to u32 modulus facts.
#[rapx::verify]
pub fn sound_zst_trivial_alignment(ptr: *const Zst) {
    unsafe {
        require_zst_align(ptr);
    }
}
