#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use core::mem::MaybeUninit;

#[repr(C)]
pub struct Pair {
    head: u32,
    tail: u64,
}

#[repr(u8)]
pub enum Tiny {
    Zero = 0,
    One = 1,
}

#[rapx::requires(Typed(_ptr, u32), kind = "precond")]
unsafe fn require_typed_u32(_ptr: *const u32) {}

#[rapx::requires(Typed(_ptr, bool), kind = "precond")]
unsafe fn require_typed_bool(_ptr: *const bool) {}

#[rapx::requires(Typed(_ptr, char), kind = "precond")]
unsafe fn require_typed_char(_ptr: *const char) {}

#[rapx::requires(Typed(_ptr, T), kind = "precond")]
unsafe fn require_typed_t<T>(_ptr: *const T) {}

#[rapx::requires(Typed(_ptr, Tiny), kind = "precond")]
unsafe fn require_typed_tiny(_ptr: *const Tiny) {}

// SOUND: a raw pointer derived from `&u32` keeps the original pointee type.
#[rapx::verify]
pub fn sound_reference_source(value: &u32) {
    let ptr = value as *const u32;
    unsafe {
        require_typed_u32(ptr);
    }
}

// SOUND: an in-bounds element pointer from `&[u32]` preserves the element type.
#[rapx::verify]
pub fn sound_slice_element_source(data: &[u32], index: usize) {
    if index < data.len() {
        let ptr = unsafe { data.as_ptr().add(index) };
        unsafe {
            require_typed_u32(ptr);
        }
    }
}

// SOUND: a `repr(C)` field pointer has the field's declared type.
#[rapx::verify]
pub fn sound_repr_c_field_source(pair: &Pair) {
    let ptr = &pair.head as *const u32;
    unsafe {
        require_typed_u32(ptr);
    }
}

// SOUND: generic typed provenance should instantiate `T` at the callsite.
#[rapx::verify]
pub fn sound_generic_reference_source<T>(value: &T) {
    let ptr = value as *const T;
    unsafe {
        require_typed_t::<T>(ptr);
    }
}

// SOUND: every branch selects a pointer to initialized `u32` storage.
#[rapx::verify]
pub fn sound_branch_all_sources_typed(left: &u32, right: &u32, choose_left: bool) {
    let ptr = if choose_left {
        left as *const u32
    } else {
        right as *const u32
    };
    unsafe {
        require_typed_u32(ptr);
    }
}

// SOUND: the SCC changes the source pointer, but all loop-carried sources are `u32`.
#[rapx::verify]
pub fn sound_scc_preserves_typed_source(left: &u32, right: &u32, mut rounds: usize) {
    let mut ptr = left as *const u32;
    while rounds > 0 {
        ptr = if rounds % 2 == 0 {
            left as *const u32
        } else {
            right as *const u32
        };
        rounds -= 1;
    }
    unsafe {
        require_typed_u32(ptr);
    }
}

// SOUND: after a write, the `MaybeUninit<u32>` storage contains a `u32` value.
#[rapx::verify]
pub fn sound_maybeuninit_after_write(value: u32) {
    let mut slot = MaybeUninit::<u32>::uninit();
    let ptr = slot.as_mut_ptr();
    unsafe {
        ptr.write(value);
        require_typed_u32(ptr);
    }
}

// SOUND: `align_to::<u32>` keeps the middle view typed as `u32` when source and target match.
#[rapx::verify]
pub fn sound_align_to_same_type(data: &[u32]) -> usize {
    let (_, middle, _) = unsafe { data.align_to::<u32>() };
    middle.len()
}

// UNSOUND: arbitrary `u8` bytes are not typed as `u32` merely because they are cast.
#[rapx::verify]
pub fn unsound_u8_bytes_as_u32(bytes: &[u8; 4]) {
    let ptr = bytes.as_ptr() as *const u32;
    unsafe {
        require_typed_u32(ptr);
    }
}

// UNSOUND: a `u16` slice cannot be reinterpreted as `u32` without a typed transmute proof.
#[rapx::verify]
pub fn unsound_u16_slice_as_u32(data: &[u16]) {
    if !data.is_empty() {
        let ptr = data.as_ptr() as *const u32;
        unsafe {
            require_typed_u32(ptr);
        }
    }
}

// UNSOUND: uninitialized storage is not a typed `u32` value yet.
#[rapx::verify]
pub fn unsound_uninit_memory_as_u32() {
    let slot = MaybeUninit::<u32>::uninit();
    let ptr = slot.as_ptr();
    unsafe {
        require_typed_u32(ptr);
    }
}

// UNSOUND: the byte value `2` is not a valid `bool`.
#[rapx::verify]
pub fn unsound_invalid_bool_bits() {
    let byte = 2_u8;
    let ptr = &byte as *const u8 as *const bool;
    unsafe {
        require_typed_bool(ptr);
    }
}

// UNSOUND: surrogate code point bits are not a valid Rust `char`.
#[rapx::verify]
pub fn unsound_invalid_char_bits() {
    let raw = 0xD800_u32;
    let ptr = &raw as *const u32 as *const char;
    unsafe {
        require_typed_char(ptr);
    }
}

// UNSOUND: `3_u8` is not a valid discriminant for `Tiny`.
#[rapx::verify]
pub fn unsound_invalid_enum_discriminant() {
    let byte = 3_u8;
    let ptr = &byte as *const u8 as *const Tiny;
    unsafe {
        require_typed_tiny(ptr);
    }
}

// UNSOUND: one branch can select storage whose dynamic type is only bytes.
#[rapx::verify]
pub fn unsound_branch_selects_untyped_source(good: &u32, bytes: &[u8; 4], choose_good: bool) {
    let ptr = if choose_good {
        good as *const u32
    } else {
        bytes.as_ptr() as *const u32
    };
    unsafe {
        require_typed_u32(ptr);
    }
}

// UNSOUND: the SCC may overwrite a typed source with byte storage.
#[rapx::verify]
pub fn unsound_scc_overwrites_with_untyped_source(
    good: &u32,
    bytes: &[u8; 4],
    mut rounds: usize,
) {
    let mut ptr = good as *const u32;
    while rounds > 0 {
        ptr = if rounds % 2 == 0 {
            good as *const u32
        } else {
            bytes.as_ptr() as *const u32
        };
        rounds -= 1;
    }
    unsafe {
        require_typed_u32(ptr);
    }
}
