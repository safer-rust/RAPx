#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

// Cast cross-view materialization (byte ↔ field).
//
//   * `roundtrip` writes a byte and reads it back as a struct field
//     (byte → field).
//
//   * `field_to_byte` writes a struct field and reads it back as a byte
//     (field → byte).
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

#[rapx::verify]
unsafe fn field_to_byte() -> u8 {
    let s = Header { len: 7, flag: 0 };
    let p = &s as *const Header as *const u8;
    let slice = core::slice::from_raw_parts(p, 1);
    let v = slice[0]; // must be 7, not the slice base address
    std::mem::forget(s);
    let arr = Box::new([0u8; 8]); // heap, bounded, alive at deref
    *arr.as_ptr().add(v as usize) // InBound requires v < 8
}
