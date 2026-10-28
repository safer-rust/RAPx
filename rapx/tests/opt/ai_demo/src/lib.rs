/// FIFO consumption using the existing Vec front-removal opt rule.
/// Select a manually authored equivalent with the `optimized` feature.
pub fn join(mut parts: Vec<String>) -> String {
    let mut output = String::new();
    #[cfg(not(feature = "optimized"))]
    while !parts.is_empty() {
        output.push_str(&parts.remove(0));
    }
    #[cfg(feature = "optimized")]
    {
        let mut queue = std::collections::VecDeque::from(std::mem::take(&mut parts));
        while let Some(part) = queue.pop_front() {
            output.push_str(&part);
        }
    }
    output
}

/// A second existing-rule candidate for request-budget tests only.
#[cfg(feature = "two-findings")]
pub fn remove_first(mut items: Vec<u32>) -> Option<u32> {
    if items.is_empty() {
        None
    } else {
        Some(items.remove(0))
    }
}

#[cfg(test)]
mod tests {
    use super::join;

    #[test]
    fn matches_reference_for_empty_unicode_and_growth() {
        let fragments = ["", "a", "é", "中文", "🦀", "\0", "ab"];
        for a in fragments {
            for b in fragments {
                for c in fragments {
                    assert_eq!(
                        join([a, b, c].map(str::to_owned).to_vec()),
                        [a, b, c].concat()
                    );
                }
            }
        }
        assert_eq!(join(vec![]), "");
        let large = vec!["rust🦀"; 1000];
        assert_eq!(
            join(large.iter().map(|s| (*s).to_owned()).collect()),
            large.concat()
        );
    }
}
