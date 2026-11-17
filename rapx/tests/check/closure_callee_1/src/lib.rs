pub fn total(items: &[u32]) -> u32 {
    items.iter().map(|x| x + 1).sum()
}
