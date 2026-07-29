
#[test]
fn opt_bounds_len() {
    let output = run_with_args("opt/bounds_len", &["opt"]);
    assert_not_contain(&output, "RAPx|ERROR|");
    assert_contain(&output, "Potential optimizations detected");
    assert_contain(&output, "Bounds Checking: 2");
}

#[test]
fn opt_encoding_check() {
    let output = run_with_args("opt/encoding_check", &["opt"]);
    assert_not_contain(&output, "RAPx|ERROR|");
    assert_contain(&output, "Potential optimizations detected");
    assert_contain(&output, "Encoding Checking: 2");
}

#[test]
fn opt_hash_key_cloning() {
    let output = run_with_args("opt/hash_key_cloning", &["opt"]);
    assert_not_contain(&output, "RAPx|ERROR|");
    assert_contain(&output, "Potential optimizations detected");
    assert_contain(&output, "Cloning: 1");
}
