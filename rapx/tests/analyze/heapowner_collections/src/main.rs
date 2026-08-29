#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]

fn main() {
    mod sequences {
        use std::collections::{LinkedList, VecDeque};
        fn t() {
            let v: Vec<i32> = Vec::new();
            let s: String = String::from("test");
            let vd: VecDeque<i32> = VecDeque::new();
            let link: LinkedList<i32> = LinkedList::new();
            println!("{:?}", (v, s, vd, link));
        }
    }

    mod maps {
        use std::collections::{BTreeMap, HashMap};
        fn t() {
            let hash: HashMap<i32, i32> = HashMap::new();
            let btree: BTreeMap<i32, i32> = BTreeMap::new();
            println!("{:?}", (hash, btree));
        }
    }

    mod sets {
        use std::collections::{BTreeSet, HashSet};
        fn t() {
            let hash: HashSet<i32> = HashSet::new();
            let btree: BTreeSet<i32> = BTreeSet::new();
            println!("{:?}", (hash, btree));
        }
    }

    mod misc {
        use std::collections::BinaryHeap;
        fn t() {
            let heap: BinaryHeap<i32> = BinaryHeap::new();
            println!("{:?}", heap);
        }
    }
}
