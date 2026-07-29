
// ==================== Dangling Pointer Detection Tests ====================
#[test]
fn uaf_cases() {
    let output = run_with_args("check/uaf_1", CMD_CHECK_UAF);
    assert_contain(
        &output,
        "Dangling pointer detected in function \"create_vec\"",
    );

    let output = run_with_args("check/uaf_2", CMD_CHECK_UAF);
    assert_contain(&output, "Double free detected in function \"main\"");

    let output = run_with_args("check/uaf_3", CMD_CHECK_UAF);
    assert_contain(&output, "Double free detected");

    let output = run_with_args("check/uaf_4", CMD_CHECK_UAF);
    assert_contain(&output, "Dangling pointer detected in function \"call\"");

    let output = run_with_args("check/uaf_5", CMD_CHECK_UAF);
    assert_contain(&output, "Use-after-free detected in function \"main\"");

    let output = run_with_args("check/uaf_6", CMD_CHECK_UAF);
    assert_contain(&output, "Use-after-free detected in function \"main\"");

    let output = run_with_args("check/uaf_7", CMD_CHECK_UAF);
    assert_contain(&output, "Double free detected in function \"main\"");

    let output = run_with_args("check/uaf_8", CMD_CHECK_UAF);
    assert_contain(&output, "Use-after-free detected in function \"main\"");

    let output = run_with_args("check/uaf_9", CMD_CHECK_UAF);
    assert_contain(&output, "Use-after-free detected in function \"main\"");

    let output = run_with_args("check/uaf_10", CMD_CHECK_UAF);
    assert_contain(&output, "Double free detected in function \"evil_test\"");
}

#[test]
fn uaf_false_cases() {
    let output = run_with_args("check/uaf_false_1", CMD_CHECK_UAF);
    assert_not_contain(&output, "detected");

    let output = run_with_args("check/uaf_false_2", CMD_CHECK_UAF);
    assert_not_contain(&output, "detected");

    let output = run_with_args("check/uaf_false_3", CMD_CHECK_UAF);
    assert_not_contain(&output, "detected");

    let output = run_with_args("check/uaf_false_4", CMD_CHECK_UAF);
    assert_not_contain(&output, "detected");

    let output = run_with_args("check/uaf_false_5", CMD_CHECK_UAF);
    assert_not_contain(&output, "detected");

    let output = run_with_args("check/uaf_false_6", CMD_CHECK_UAF);
    assert_not_contain(&output, "detected");

    let output = run_with_args("check/uaf_false_7", CMD_CHECK_UAF);
    assert_not_contain(&output, "detected");

    let output = run_with_args("check/uaf_false_8", CMD_CHECK_UAF);
    assert_not_contain(&output, "detected");

    let output = run_with_args("check/uaf_false_9", CMD_CHECK_UAF);
    assert_not_contain(&output, "detected");

    let output = run_with_args("check/uaf_false_10", CMD_CHECK_UAF);
    assert_not_contain(&output, "detected");

    let output = run_with_args("check/uaf_false_11", CMD_CHECK_UAF);
    assert_not_contain(&output, "detected");
}

#[test]
fn leak_cases() {
    let output = run_with_args("check/memleak_1", CMD_CHECK_MEMLEAK);
    assert_not_contain(&output, "Memory Leak detected in function main");

    let output = run_with_args("check/memleak_2", CMD_CHECK_MEMLEAK);
    assert_contain(&output, "Memory Leak detected in function main");

    let output = run_with_args("check/memleak_3", CMD_CHECK_MEMLEAK);
    assert_contain(&output, "Memory Leak detected in function main");
}
