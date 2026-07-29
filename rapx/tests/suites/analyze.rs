
fn run_alias_cases(cmd: &[&str], alias_2_pattern: &str) {
    let output = run_with_args("analyze/alias_1", cmd);
    assert_contain(&output, "foo\": (0.0,1)");

    let output = run_with_args("analyze/alias_2", cmd);
    assert_contain(&output, alias_2_pattern);

    let output = run_with_args("analyze/alias_3", cmd);
    assert_contain(&output, "foo\": null");

    let output = run_with_args("analyze/alias_4", cmd);
    let has_either = output.contains("\"foo\": (0,1.1), (0,1.0)")
        || output.contains("\"foo\": (0,1.0), (0,1.1)");
    assert!(
        has_either,
        "Missing alias field variations\nFull output:\n{}",
        output
    );

    let output = run_with_args("analyze/alias_5", cmd);
    assert_contain(&output, "new\": (0.0,1.0)");

    let output = run_with_args("analyze/alias_6", cmd);
    assert_contain(&output, "foo\": (0,1)");

    let output = run_with_args("analyze/alias_7", cmd);
    assert_contain(&output, "foo\": (0,1)");

    let output = run_with_args("analyze/alias_8", cmd);
    assert_contain(&output, "foo\": (0,1), (0,2)");

    let output = run_with_args("analyze/alias_9", cmd);
    assert_contain(&output, "foo\": (0,1)");

    let output = run_with_args("analyze/alias_10", cmd);
    assert_contain(&output, "new\": (0.0,1.0)");

    let output = run_with_args("analyze/alias_11", cmd);
    assert_contain(&output, "iter_prop\": (0.0,1.0)");
}

// ===============Alias(MOP) Analysis Test==============
#[test]
fn alias_cases() {
    run_alias_cases(CMD_ANALYZE_ALIAS, "foo\": (0,1)");
}

// ===============Alias(MFP) Analysis Test==============
#[test]
fn alias_mfp_cases() {
    run_alias_cases(CMD_ANALYZE_ALIAS_MFP, "foo\": (0.0,1)");
}

#[test]
fn heap_cases() {
    let output = run_with_args("analyze/ownedheap_cell", CMD_ANALYZE_OWNEDHEAP);
    for pattern in [
        "Cell\": False, <1>",
        "RefCell\": False, <1>",
        "UnsafeCell\": False, <1>",
        "Rc\": True, <1,1>",
        "Arc\": True, <1,1>",
        "UniqueRc\": True, <1,1>",
    ] {
        assert_contain(&output, pattern);
    }

    let output = run_with_args("analyze/ownedheap_collections", CMD_ANALYZE_OWNEDHEAP);
    for pattern in [
        "Unique\": True, <0>",
        "Box\": True, <0,1>",
        "Vec\": True, <0,1>",
        "String\": True, <>",
        "LinkedList\": True, <1,1>",
    ] {
        assert_contain(&output, pattern);
    }
    #[cfg(rapx_rustc_ge_196)]
    {
        assert_contain(&output, "HashMap\": True, <0,0,1,1>");
        assert_contain(&output, "HashSet\": True, <0,1,1>");
        assert_contain(&output, "BTreeMap\": True, <0,0,1>");
        assert_contain(&output, "BTreeSet\": True, <0,1>");
    }
    #[cfg(not(rapx_rustc_ge_196))]
    {
        assert_contain(&output, "HashMap\": True, <0,0,1>");
        assert_contain(&output, "HashSet\": True, <0,1>");
        assert_contain(&output, "BTreeMap\": True, <0,0,1>");
        assert_contain(&output, "BTreeSet\": True, <0,1>");
    }

    let output = run_with_args("analyze/ownedheap_nested", CMD_ANALYZE_OWNEDHEAP);
    for pattern in [
        "X\": False, <1>",
        "Y\": False, <1>",
        "Example\": True, <1,1,0,1>",
    ] {
        assert_contain(&output, pattern);
    }

    let output = run_with_args("analyze/ownedheap_proxy", CMD_ANALYZE_OWNEDHEAP);
    for pattern in [
        "Proxy1\": False, <0>",
        "Proxy2\": True, <0>",
        "Proxy3\": False, <0,0>",
        "Proxy4\": False, <1>",
        "Proxy5\": True, <0>",
    ] {
        assert_contain(&output, pattern);
    }
}

#[test]
fn path_cases() {
    let output = run_with_args("analyze/path_1", CMD_ANALYZE_PATHS);
    assert_contain(&output, "Function: \"example\":");
    assert_contain(&output, "Path [0, 3, 4, 6, 7, 9]");
    assert_contain(&output, "Path [0, 2, 4, 5, 8, 9]");
    assert_eq!(path_count_for(&output, "example"), 2);

    let output = run_with_args("analyze/path_2", CMD_ANALYZE_PATHS);
    assert_contain(&output, "Function: \"read2\":");
    assert_contain(&output, "Path [0, 1, 2, 3, 10, 11]");
    assert_contain(&output, "Path [0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11]");
    assert_contain(&output, "Path [0, 1, 2, 4, 5, 6, 12*]");
    assert_eq!(path_count_for(&output, "read2"), 3);

    let output = run_with_args("analyze/path_3", CMD_ANALYZE_PATHS);
    assert_contain(&output, "Function: \"retry_once\":");
    assert_contain(&output, "Path [0, 1, 2, 1, 3]");
    assert_eq!(path_count_for(&output, "retry_once"), 1);

    let output = run_with_args("analyze/path_4", CMD_ANALYZE_PATHS);
    assert_contain(&output, "Function: \"read1\":");
    assert_contain(&output, "Path [0, 1, 2, 6]");
    assert_contain(&output, "Path [0, 1, 3, 4, 1, 3, 5, 6]");
    assert_eq!(path_count_for(&output, "read1"), 2);

    let output = run_with_args("analyze/path_5", CMD_ANALYZE_PATHS);
    assert_contain(&output, "Function: \"read2\":");
    assert_contain(&output, "Path [0, 1, 2, 3, 9]");
    assert_eq!(path_count_for(&output, "read2"), 2);

    let output = run_with_args("analyze/path_false_1", CMD_ANALYZE_PATHS);
    assert_contain(&output, "Function: \"classify\":");
    assert_contain(&output, "Path [0, 1, 2]");
    assert_contain(&output, "Path [0, 1, 3, 4, 5, 6, 7, 10, 1, 2]");
    assert_contain(&output, "Path [0, 1, 3, 4, 5, 8, 9, 10, 1, 2]");
    assert_eq!(path_count_for(&output, "classify"), 9);

    let output = run_with_args("analyze/path_6", CMD_ANALYZE_PATHS);
    assert_contain(&output, "Function: \"early_exit\":");
    assert_contain(&output, "Path [0, 1, 2]");
    assert_contain(&output, "Path [0, 1, 3, 4, 1, 2]");
    assert_eq!(path_count_for(&output, "early_exit"), 2);

    let output = run_with_args("analyze/path_7", CMD_ANALYZE_PATHS);
    assert_contain(&output, "Function: \"walk\":");
    assert_contain(&output, "Path [0, 1, 2]");
    assert_contain(&output, "Path [0, 1, 3, 4, 5, 9, 1, 2]");
    assert_contain(&output, "Path [0, 1, 3, 4, 6, 7, 8, 4, 5, 9, 1, 2]");
    assert_contain(
        &output,
        "Path [0, 1, 3, 4, 6, 7, 8, 4, 5, 9, 1, 3, 4, 5, 9, 1, 2]",
    );
    assert_eq!(path_count_for(&output, "walk"), 4);

    let output = run_with_args("analyze/path_false_1", CMD_ANALYZE_PATHS_REPEAT_1);
    assert_eq!(path_count_for(&output, "classify"), 39);
    assert_contain(&output, "Path [0, 1, 2]");

    let output = run_with_args("analyze/path_false_1", CMD_ANALYZE_PATHS_REPEAT_2);
    assert_eq!(path_count_for(&output, "classify"), 128);
    assert_contain(&output, "Path [0, 1, 2]");
}

#[test]
fn range_analysis() {
    let output = run_with_args("analyze/range_1", CMD_ANALYZE_RANGE);

    let expected_ranges = vec![
        "_1 => Regular [0, 0]",
        "_2 => Regular [Min, Max]",
        "_4 => Regular [0, 100]",
        "_6 => Regular [0, 99]",
        "_11 => Regular [1, 99]",
        "_12 => Regular [0, 98]",
        "_34 => Regular [1, 100]",
    ];

    for expected in expected_ranges {
        assert!(
            output.contains(expected),
            "Missing expected range: '{}'\nFull output:\n{}",
            expected,
            output
        );
    }
}

#[test]

fn interprocedural_range_analysis() {
    let output = run_with_args("analyze/range_2", CMD_ANALYZE_RANGE);

    let expected_ranges = vec![
        "_1 => Regular [42, 42]",
        "_2 => Regular [Min, Max]",
        "_4 => Regular [52, 52]",
        "_5 => Regular [100, 100]",
    ];

    for expected in expected_ranges {
        assert!(
            output.contains(expected),
            "Missing expected range: '{}'\nFull output:\n{}",
            expected,
            output
        );
    }
}

#[test]
fn callgraph_dynamic_dispatch() {
    let output = run_with_args("analyze/callgraph_dynamic", CMD_ANALYZE_CALLGRAPH);

    let expected_calls = vec!["-> <Dog as Animal>::speak", "-> <Cat as Animal>::speak"];

    for expected in expected_calls {
        assert!(
            output.contains(expected),
            "Missing dynamic call '{}'\nFull output:\n{}",
            expected,
            output
        );
    }
}

#[test]
fn symbolic_interval() {
    let output = run_with_args("analyze/range_symbolic", CMD_ANALYZE_RANGE);

    let expected_ranges = vec![
        "Var: (_5.0: i32). [ Binary(AddWithOverflow, Place(_1), Constant(Val(Scalar(0x00000001), i32))) , Binary(AddWithOverflow, Place(_1), Constant(Val(Scalar(0x00000001), i32))) ]",
        "Var: _6. [ Place(_1) , Place(_1) ]",
        "Var: _8. [ Constant(Val(Scalar(0x00000001), i32)) , Constant(Val(Scalar(0x00000001), i32)) ]",
    ];

    for expected in expected_ranges {
        assert!(
            output.contains(expected),
            "Missing expected symbolic interval: '{}'\nFull output:\n{}",
            expected,
            output
        );
    }
}

#[test]
fn adg_bug_regression() {
    // This test pass if don't panic (e.g., stack overflow) during ADG construction and resolution.
    let _ = run_with_args("analyze/adg_bug_regression", CMD_ANALYZE_ADG);
}

#[test]
fn adg_simple_graph() {
    let _ = run_with_args("analyze/adg_simple_graph", CMD_ANALYZE_ADG);
    let graph_str =
        std::fs::read_to_string(project_path("analyze/adg_simple_graph").join("api_graph.yml"))
            .expect("read api_graph.yml fail");
    assert_contain(&graph_str, "path: foo");
    assert_contain(&graph_str, "path: bar");
    assert_contain(&graph_str, "path: vec_arg");
    assert_contain(&graph_str, "path: std::vec::Vec::<i32, std::alloc::Global>");
    assert_contain(&graph_str, "path: Item");
    assert_contain(&graph_str, "type: Api");
    assert_contain(&graph_str, "type: Ty");
    assert_contain(&graph_str, "type: Ret");
    assert_contain(&graph_str, "type: Arg");
    assert_contain(&graph_str, "from: 0");
    assert_contain(&graph_str, "to: 1");
    assert_contain(&graph_str, "from: 1");
    assert_contain(&graph_str, "to: 2");
    assert_contain(&graph_str, "from: 3");
    assert_contain(&graph_str, "to: 4");
}

#[test]
fn ssa_transform() {
    let output = run_with_args("analyze/ssa_transform", CMD_ANALYZE_SSA);
    assert_contain(&output, "ssa lvalue check true");
}

#[test]
fn safetyflow_safe_caller() {
    let output = run_with_args("analyze/safetyflow_safe_caller", CMD_ANALYZE_SAFETYFLOW);
    assert_contain(&output, "from_raw_parts");
}

#[test]
fn safetyflow_raw_ptr() {
    let output = run_with_args("analyze/safetyflow_raw_ptr", CMD_ANALYZE_SAFETYFLOW);
    assert_contain(&output, "*raw* ptr deref");
}

#[test]
fn safetyflow_static_mut() {
    let output = run_with_args("analyze/safetyflow_static_mut", CMD_ANALYZE_SAFETYFLOW);
    assert_contain(&output, "COUNTER");
}

#[test]
fn scan_raw_ptr_deref() {
    let output = run_with_args("analyze/safetyflow_raw_ptr", CMD_VERIFY_SCAN);
    assert_contain(&output, "[rapx::verify] function: main");
    assert_contain(&output, "ValidPtr | Proved");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn scan_static_mut() {
    let output = run_with_args("analyze/safetyflow_static_mut", CMD_VERIFY_SCAN);
    assert_contain(&output, "[rapx::verify] function: main");
    assert_contain(&output, "Unknown");
    assert_contain(&output, "UNSOUND");
}
