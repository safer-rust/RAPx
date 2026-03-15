pub struct Item(u32);

pub fn foo() -> Item {
    Item(0)
}

pub fn bar(_item: Item) -> Vec<u32> {
    vec![0]
}

pub fn vec_arg(_vec: Vec<i32>) -> String {
    "hi".to_string()
}