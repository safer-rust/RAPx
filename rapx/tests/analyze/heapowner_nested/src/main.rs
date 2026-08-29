#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]

#[derive(Debug)]
struct X<A> {
    a: A,
}

#[derive(Debug)]
struct Y<B> {
    a: (i32, (f64, B)),
    b: X<i32>,
}

#[derive(Debug)]
struct Example<A, B, T, S> {
    a: X<A>,
    b: (i32, (f64, B)),
    c: [[S; 1]; 2],
    d: Vec<T>,
    e: Y<B>,
}

fn main() {
    let example = Example {
        a: X { a: 1 },
        b: (1, (1.0, 1)),
        c: [[1; 1]; 2],
        d: Vec::<i32>::new(),
        e: Y {
            a: (1, (1.0, 1)),
            b: X { a: 1 },
        },
    };
    println!("{:?}", example);
}
