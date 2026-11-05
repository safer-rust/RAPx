/*
 * This is a buggy case: double free
 */

fn main() {
    let mut s = String::from("a tmp string");
    let ptr = s.as_mut_ptr();
    let v = unsafe { Vec::from_raw_parts(ptr, s.len(), s.len()) };
    let nv = v;
    let _nnv = nv;
}
