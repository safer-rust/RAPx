use std::env;

#[derive(Debug)]
struct MyRef<'a> {
    a: &'a str,
}

unsafe fn f<'a>(myref: MyRef<'a>) -> MyRef<'static> {
    unsafe { std::mem::transmute(myref) }
}

unsafe fn f_in_closure<'a>(r: MyRef<'a>) -> MyRef<'static> {
    (|| unsafe { std::mem::transmute(r) })()
}

fn main() {
    let string = "Hello World!".to_string();
    let args: Vec<String> = env::args().collect();
    let my_ref = unsafe { f(MyRef { a: &string }) };
    if args.len() > 2 {
        drop(string);
    }
    println!("{:?}", my_ref.a);
    irrefutable_let_else_uaf();
    moved_reference_uaf();
    closure_wrapper_uaf();
}

fn irrefutable_let_else_uaf() {
    let s = String::from("hello");
    let r = (unsafe { f(MyRef { a: &s }) }) else { panic!() };
    drop(s);
    println!("{}", r.a);
}

fn moved_reference_uaf() {
    let s = String::from("hello");
    let r = unsafe { f(MyRef { a: &s }) };
    let nr = r;
    drop(s);
    println!("{}", nr.a);
}

fn closure_wrapper_uaf() {
    let s = String::from("hello");
    let r = unsafe { f_in_closure(MyRef { a: &s }) };
    drop(s);
    println!("{}", r.a);
}
