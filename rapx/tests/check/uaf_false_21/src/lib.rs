use std::alloc::{alloc, dealloc, realloc, Layout};

pub fn reallocate_and_free() {
    unsafe {
        let layout = Layout::from_size_align_unchecked(8, 8);
        let p = alloc(layout);
        if !p.is_null() {
            let q = realloc(p, layout, 16);
            if q.is_null() {
                dealloc(p, layout);
            } else {
                dealloc(q, Layout::from_size_align_unchecked(16, 8));
            }
        }
    }
}
