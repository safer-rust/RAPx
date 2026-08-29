#![feature(unique_rc_arc)]
#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]

fn main() {
    mod cell {
        use std::cell::{Cell, LazyCell, RefCell, UnsafeCell};
        fn t() {
            let cell = Cell::new(1);
            let unsafe_cell = UnsafeCell::new(1);
            let ref_cell = RefCell::new(1);
            let lazy_cell = LazyCell::new(|| 92);
            println!("{:?}", (cell, unsafe_cell, ref_cell, lazy_cell));
        }
    }

    mod rc {
        use std::{
            rc::{Rc, UniqueRc, Weak as Weak1},
            sync::{Arc, Weak as Weak2},
        };
        fn t() {
            let rc = Rc::new(1);
            let arc = Arc::new(1);
            let unique_rc = UniqueRc::new(1);
            let weak_rc: Weak1<i32> = Weak1::new();
            let weak_arc: Weak2<i32> = Weak2::new();
            println!("{:?}", (rc, arc, unique_rc, weak_rc, weak_arc));
        }
    }
}
