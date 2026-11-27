use std::alloc::{alloc, dealloc, realloc, Layout};

pub fn use_old_pointer_after_realloc() {
    unsafe {
        let layout = Layout::from_size_align_unchecked(8, 8);
        let p = alloc(layout);
        if !p.is_null() {
            p.write(1);
            let q = realloc(p, layout, 16);
            if q.is_null() {
                dealloc(p, layout);
            } else {
                p.read_volatile();
                dealloc(q, Layout::from_size_align_unchecked(16, 8));
            }
        }
    }
}
