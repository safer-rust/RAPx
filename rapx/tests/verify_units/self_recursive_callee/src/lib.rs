#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

fn walk(x: u32) -> u32 {
    if x <= 1 {
        x
    } else {
        walk(x >> 1)
    }
}

// `walk` returns 0 or 1 (the leading bit), self-recursive and truncated by the
// inline-depth bound. Its return value `n` feeds `ptr.add` as the offset; the
// base case (`n ∈ {0,1}`) bounds the offset, while the truncated recursion makes
// `n` unprovable (`Unknown (incomplete inline)`).
#[rapx::verify]
pub fn target(xs: &[u32]) -> u32 {
    let n = walk(xs[0]);
    unsafe { *xs.as_ptr().add(n as usize) }
}
