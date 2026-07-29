#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

#[rapx::invariant(any(Null(next), (Align(next, Entry), ValidPtr(next, Entry, 1), Allocated(next, Entry, 1), Typed(next, Entry), Owning(next))))]
struct Entry {
    key: i32,
    value: i32,
    next: *mut Entry,
}

#[rapx::invariant(Align(buckets.iter(), Entry))]
#[rapx::invariant(Allocated(buckets.iter(), Entry, 1))]
#[rapx::invariant(Typed(buckets.iter(), Entry))]
#[rapx::invariant(Owning(buckets.iter()))]
struct HashMap {
    buckets: Box<[*mut Entry]>,
    cap: usize,
    len: usize,
}

impl HashMap {
    #[rapx::verify]
    pub fn new(cap: usize) -> Self {
        let mut data: Vec<*mut Entry> = Vec::with_capacity(cap);
        for _ in 0..cap {
            data.push(std::ptr::null_mut());
        }
        HashMap { buckets: data.into_boxed_slice(), cap, len: 0 }
    }

    #[rapx::verify]
    pub fn len(&self) -> usize { self.len }

    #[rapx::verify]
    pub fn is_empty(&self) -> bool { self.len == 0 }

    pub fn capacity(&self) -> usize { self.cap }

    fn hash(key: i32, cap: usize) -> usize { (key as usize) % cap.max(1) }

    #[rapx::verify]
    pub fn insert(&mut self, key: i32, value: i32) {
        let idx = Self::hash(key, self.cap);
        let head = self.buckets[idx];
        let entry = Box::into_raw(Box::new(Entry { key, value, next: head }));
        self.buckets[idx] = entry;
        self.len += 1;
    }

    #[rapx::verify]
    pub fn contains_key(&self, key: i32) -> bool {
        let idx = Self::hash(key, self.cap);
        let mut current = self.buckets[idx];
        let mut found = false;
        unsafe {
            while !current.is_null() {
                if (*current).key == key { found = true; break; }
                current = (*current).next;
            }
        }
        found
    }

    pub fn get(&self, key: i32) -> Option<i32> {
        let idx = Self::hash(key, self.cap);
        let mut current = self.buckets[idx];
        unsafe {
            while !current.is_null() {
                if (*current).key == key { return Some((*current).value); }
                current = (*current).next;
            }
        }
        None
    }

    pub fn remove(&mut self, key: i32) -> Option<i32> {
        let idx = Self::hash(key, self.cap);
        let mut current = self.buckets[idx];
        let mut prev: *mut Entry = std::ptr::null_mut();
        unsafe {
            while !current.is_null() {
                if (*current).key == key {
                    let value = (*current).value;
                    let next = (*current).next;
                    self.buckets[idx] = next;
                    if !prev.is_null() { (*prev).next = next; }
                    drop(Box::from_raw(current));
                    self.len -= 1;
                    return Some(value);
                }
                prev = current;
                current = (*current).next;
            }
        }
        None
    }

    #[rapx::verify]
    pub fn clear(&mut self) {
        for i in 0..self.cap {
            let mut current = self.buckets[i];
            unsafe {
                while !current.is_null() {
                    let next = (*current).next;
                    drop(Box::from_raw(current));
                    current = next;
                }
            }
            self.buckets[i] = std::ptr::null_mut();
        }
        self.len = 0;
    }
}

impl Drop for HashMap {
    fn drop(&mut self) {
        for i in 0..self.cap {
            let mut current = self.buckets[i];
            unsafe {
                while !current.is_null() {
                    let next = (*current).next;
                    drop(Box::from_raw(current));
                    current = next;
                }
            }
        }
    }
}
