#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

// Regression: writing a byte through a `u8` pointer and then reinterpreting the
// buffer as a `repr(C)` struct must round-trip the byte into the struct field.
// Before the cast cross-view materialization, `decompose_pointee_fields` minted
// a *fresh* symbolic value for `len`, so `buf.add(len)`'s InBound obligation
// (`len < 16`) could not be discharged and the function reported UNSOUND.
#[repr(C)]
struct Header {
    len: u8,
    flag: u8,
}

#[rapx::verify]
unsafe fn roundtrip() -> u8 {
    let mut buf = vec![0u8; 16]; // internal (bounded) buffer
    let p = buf.as_mut_ptr();
    *p = 3; // write byte 3 at buf[0] (byte layer)
    let h = &*(p as *mut Header); // cast u8* -> Header* (field layer)
    let len = (*h).len as usize; // must be 3, not a fresh symbol
    std::mem::forget(buf);
    *p.add(len) // InBound requires len < 16
}
