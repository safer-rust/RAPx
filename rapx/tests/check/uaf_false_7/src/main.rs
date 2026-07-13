struct S {
    field: String,
}

fn main() {
    let s = S {
        field: String::new(),
    };
    let _ = &s;
}
