#![feature(register_tool, core_intrinsics, thread_local)]
#![register_tool(rapx)]
#![allow(dead_code, internal_features, unused_variables)]

#[rapx::requires(ValidNum(value != 0))]
unsafe fn need_nonzero(value: u32) {}

#[rapx::requires(ValidNum(value != 0))]
unsafe fn need_nonzero_wide(value: u128) {}

#[thread_local]
static TLS_ONE: u32 = 7;

#[thread_local]
static TLS_ZERO: u32 = 0;

#[thread_local]
static TLS_WIDE: u128 = 1u128 << 80;

#[thread_local]
static mut TLS_MUT: u32 = 7;

struct ArrayHolder {
    values: [u32; 4],
}

#[rapx::verify]
pub fn sound_repeated_array_field() {
    let mut holder = ArrayHolder { values: [0_u32; 4] };
    holder.values = [1_u32; 4];
    unsafe { need_nonzero(holder.values[0]) };
}

#[rapx::verify]
pub fn unsound_repeated_array_field() {
    let mut holder = ArrayHolder { values: [1_u32; 4] };
    holder.values = [0_u32; 4];
    unsafe { need_nonzero(holder.values[0]) };
}

#[rapx::verify]
pub fn sound_symbolic_repeated_array_field(index: usize) {
    let holder = ArrayHolder { values: [1_u32; 4] };
    if index < holder.values.len() {
        unsafe { need_nonzero(holder.values[index]) };
    }
}

#[rapx::verify]
pub fn sound_thread_local_value() {
    unsafe { need_nonzero(TLS_ONE) };
}

#[rapx::verify]
pub fn unsound_thread_local_value() {
    unsafe { need_nonzero(TLS_ZERO) };
}

#[rapx::verify]
pub fn sound_thread_local_wide_value() {
    unsafe { need_nonzero_wide(TLS_WIDE) };
}

#[rapx::verify]
pub fn sound_thread_local_mut_write() {
    unsafe {
        TLS_MUT = 1;
        need_nonzero(TLS_MUT);
    }
}

#[rapx::verify]
pub fn unsound_thread_local_mut_write() {
    unsafe {
        TLS_MUT = 0;
        need_nonzero(TLS_MUT);
    }
}

#[rapx::verify]
pub fn unsound_thread_local_mut_initial() {
    unsafe { need_nonzero(TLS_MUT) };
}

fn overwrite_thread_local(value: *mut u32, replacement: u32) {
    unsafe { *value = replacement };
}

#[rapx::verify]
pub fn sound_thread_local_mut_inlined_write() {
    unsafe {
        overwrite_thread_local(&raw mut TLS_MUT, 1);
        need_nonzero(TLS_MUT);
    }
}

#[rapx::verify]
pub fn unsound_thread_local_mut_inlined_write() {
    unsafe {
        overwrite_thread_local(&raw mut TLS_MUT, 0);
        need_nonzero(TLS_MUT);
    }
}

fn fill_one(dest: &mut u32) {
    unsafe { std::intrinsics::write_bytes(dest, 1, 1) };
}

fn fill_zero(dest: &mut u32) {
    unsafe { std::intrinsics::write_bytes(dest, 0, 1) };
}

fn volatile_zero(dest: &mut u32) {
    unsafe { std::intrinsics::volatile_store(dest, 0_u32) };
}

#[rapx::verify]
pub fn unknown_volatile_store_wrapper() {
    let mut value = 1_u32;
    volatile_zero(&mut value);
    unsafe { need_nonzero(value) };
}

#[rapx::verify]
pub fn sound_unrelated_black_box() {
    let value = 1_u32;
    let _ = std::intrinsics::black_box(0_u32);
    unsafe { need_nonzero(value) };
}

#[rapx::verify]
pub fn sound_black_box_value() {
    let value = std::intrinsics::black_box(1_u32);
    unsafe { need_nonzero(value) };
}

#[rapx::verify]
pub fn unsound_black_box_value() {
    let value = std::intrinsics::black_box(0_u32);
    unsafe { need_nonzero(value) };
}

#[rapx::verify]
pub fn sound_inline_write_bytes() {
    let mut value = 0_u32;
    fill_one(&mut value);
    unsafe { need_nonzero(value) };
}

#[rapx::verify]
pub fn unsound_inline_write_bytes() {
    let mut value = 1_u32;
    fill_zero(&mut value);
    unsafe { need_nonzero(value) };
}

#[rapx::verify]
pub fn sound_direct_intrinsic_copy() {
    let source = 1_u32;
    let mut value = 0_u32;
    unsafe { std::intrinsics::copy_nonoverlapping(&source, &mut value, 1) };
    unsafe { need_nonzero(value) };
}

#[rapx::verify]
pub fn unsound_direct_intrinsic_copy() {
    let source = 0_u32;
    let mut value = 1_u32;
    unsafe { std::intrinsics::copy_nonoverlapping(&source, &mut value, 1) };
    unsafe { need_nonzero(value) };
}

#[rapx::verify]
pub fn sound_repeated_array_read() {
    let values = [1_u32; 4];
    unsafe { need_nonzero(values[0]) };
}

#[rapx::verify]
pub fn sound_large_repeated_array_read() {
    let values = [1_u32; 1025];
    unsafe { need_nonzero(values[0]) };
}

#[rapx::verify]
pub fn sound_large_symbolic_array_read(index: usize) {
    let values = [1_u32; 33];
    if index < values.len() {
        unsafe { need_nonzero(values[index]) };
    }
}

#[rapx::verify]
pub fn sound_reassigned_repeated_array() {
    let mut values = [1_u32; 4];
    values[0] = 0;
    values = [1_u32; 4];
    unsafe { need_nonzero(values[0]) };
}

#[rapx::verify]
pub fn sound_repeated_array_reference() {
    let values = [1_u32; 4];
    let view = &values;
    unsafe { need_nonzero(view[0]) };
}

#[rapx::verify]
pub fn sound_symbolic_array_write(index: usize) {
    let mut values = [1_u32; 4];
    if index < values.len() {
        values[index] = 1;
    }
    unsafe { need_nonzero(values[0]) };
}

#[rapx::verify]
pub fn unsound_symbolic_array_write(index: usize) {
    let mut values = [1_u32; 4];
    if index < values.len() {
        values[index] = 0;
        unsafe { need_nonzero(values[index]) };
    }
}

#[rapx::verify]
pub fn unsound_repeated_array_read() {
    let values = [0_u32; 4];
    unsafe { need_nonzero(values[0]) };
}

#[rapx::verify]
pub fn unsound_array_overwrite() {
    let mut values = [1_u32; 4];
    values[0] = 0;
    unsafe { need_nonzero(values[0]) };
}

#[rapx::verify]
pub fn sound_array_overwrite() {
    let mut values = [0_u32; 4];
    values[0] = 1;
    unsafe { need_nonzero(values[0]) };
}

#[rapx::verify]
pub fn sound_explicit_array_read() {
    let values = [1_u32, 1_u32, 1_u32, 1_u32];
    unsafe { need_nonzero(values[0]) };
}

#[rapx::verify]
pub fn sound_symbolic_array_read(index: usize) {
    let values = [1_u32; 4];
    if index < values.len() {
        unsafe { need_nonzero(values[index]) };
    }
}

#[rapx::verify]
pub fn unsound_symbolic_array_read(index: usize) {
    let values = [1_u32, 0_u32, 1_u32, 1_u32];
    if index < values.len() {
        unsafe { need_nonzero(values[index]) };
    }
}
