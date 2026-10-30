// The body of an async closure has no HIR node of its own: reporting on it must not panic.
pub async fn total(items: Vec<String>) -> usize {
    let mut total = 0;
    let mut add = async |item: String| total += item.len();
    for item in items {
        add(item).await;
    }
    total
}
