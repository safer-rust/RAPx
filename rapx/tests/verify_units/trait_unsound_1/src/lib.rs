#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

unsafe trait Buffer {
    #[rapx::ensures(NonNull(return))]
    fn as_bytes(&self) -> &[u8];

    #[rapx::requires(InBound(index, u8, 1))]
    unsafe fn get_unchecked(&self, index: usize) -> u8;
}

pub struct VecBuf {
    data: Vec<u8>,
}

#[rapx::verify]
unsafe impl Buffer for VecBuf {
    fn as_bytes(&self) -> &[u8] {
        &self.data
    }

    unsafe fn get_unchecked(&self, index: usize) -> u8 {
        self.data[index]
    }
}
