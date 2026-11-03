pub fn call(p: *mut u8) -> *mut u8 {
    let pair = ({
        let inner = (p, String::from("inner"));
        inner.0
    }, String::from("outer")) else { panic!() };
    pair.0
}

pub fn call_without_else(p: *mut u8) -> *mut u8 {
    let pair = ({
        let inner = (p, String::from("inner"));
        inner.0
    }, String::from("outer"));
    pair.0
}
