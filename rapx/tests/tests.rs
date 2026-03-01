#![allow(clippy::bool_assert_comparison)]
use std::path::Path;
use std::process::Command;

/// Checks if any bug message in the output has confidence > 50
pub fn detected_high_confidence(output: &str) -> bool {
    // Regex to find confidence, e.g., `confidence 50%`
    let re = regex::Regex::new(r"confidence (\d+)%").unwrap();
    output.lines().any(|line| {
        if let Some(cap) = re.captures(line) {
            if let Some(conf_str) = cap.get(1) {
                if let Ok(conf) = conf_str.as_str().parse::<u32>() {
                    return conf > 10;
                }
            }
        }
        false
    })
}

#[inline(always)]
fn run_with_args(dir: &str, args: &[&str]) -> String {
    let raw_path = "./tests/".to_owned() + dir;
    let project_path = Path::new(&raw_path);

    let output = Command::new("cargo")
        .arg("rapx")
        .args(args)
        .current_dir(project_path)
        .output()
        .expect("Failed to execute cargo rapx");

    String::from_utf8_lossy(&output.stderr).into_owned()
}

const CHECK_UAF_CMD: &[&str] = &["check", "-f"];
const CHECK_MLEAK_CMD: &[&str] = &["check", "-m"];
const ANALYZE_ALIAS_CMD: &[&str] = &["analyze", "alias"];
const ANALYZE_ALIAS_MFP_CMD: &[&str] = &["analyze", "alias", "--strategy", "mfp"];
const ANALYZE_OWNED_HEAP_CMD: &[&str] = &["analyze", "owned-heap"];
const ANALYZE_UPG_CMD: &[&str] = &["analyze", "upg"];
const ANALYZE_SSA_CMD: &[&str] = &["analyze", "ssa"];
const ANALYZE_RANGE_CMD: &[&str] = &["analyze", "range"];
const ANALYZE_CALLGRAPH_CMD: &[&str] = &["analyze", "callgraph"];

// ================Dangling Pointer Detection Test=====================
#[test]
fn test_dangling_min() {
    let output = run_with_args("uaf/dangling_min", CHECK_UAF_CMD);
    assert_eq!(
        output.contains("Dangling pointer detected in function \"create_vec\""),
        true
    );
}

#[test]
fn test_df_min() {
    let output = run_with_args("uaf/df_min", CHECK_UAF_CMD);
    assert_eq!(
        output.contains("Double free detected in function \"main\""),
        true
    );
}

#[test]
fn test_df_unwinding() {
    let output = run_with_args("uaf/df_unwinding", CHECK_UAF_CMD);
    assert_eq!(output.contains("Double free detected"), true);
}

#[test]
fn test_dp_lengthy() {
    let output = run_with_args("uaf/dp_lengthy", CHECK_UAF_CMD);
    assert_eq!(
        output.contains("Dangling pointer detected in function \"call\""),
        true
    );
}

#[test]
fn test_uaf_drop() {
    let output = run_with_args("uaf/uaf_drop", CHECK_UAF_CMD);
    assert_eq!(
        output.contains("Use-after-free detected in function \"main\""),
        true
    );
}

#[test]
fn test_uaf_drop2() {
    let output = run_with_args("uaf/uaf_drop2", CHECK_UAF_CMD);
    assert_eq!(
        output.contains("Use-after-free detected in function \"main\""),
        true
    );
}

#[test]
fn test_uaf_drop_in_place() {
    let output = run_with_args("uaf/uaf_drop_in_place", CHECK_UAF_CMD);
    assert_eq!(
        output.contains("Use-after-free detected in function \"main\""),
        true
    );
}

#[test]
fn test_uaf_lifetime() {
    let output = run_with_args("uaf/uaf_lifetime", CHECK_UAF_CMD);
    assert_eq!(
        output.contains("Use-after-free detected in function \"main\""),
        true
    );
}

#[test]
fn test_uaf_small() {
    let output = run_with_args("uaf/uaf_small", CHECK_UAF_CMD);
    assert_eq!(
        output.contains("Use-after-free detected in function \"main\""),
        true
    );
}

#[test]
fn test_uaf_swithint() {
    let output = run_with_args("uaf/uaf_swithint", CHECK_UAF_CMD);
    assert_eq!(
        output.contains("Use-after-free detected in function \"evil_test\""),
        true
    );
}

#[test]
fn test_false_wrapper() {
    let output = run_with_args("uaf/false_wrapper", CHECK_UAF_CMD);
    assert_eq!(detected_high_confidence(&output), false);
}

#[test]
fn test_false_scc1() {
    let output = run_with_args("uaf/false_scc1", CHECK_UAF_CMD);
    assert_eq!(output.contains("detected"), false);
}

#[test]
fn test_false_tuple_transitive() {
    let output = run_with_args("uaf/false_tuple_transitive", CHECK_UAF_CMD);
    assert_eq!(detected_high_confidence(&output), false);
}

#[test]
fn test_false_arc() {
    let output = run_with_args("uaf/false_arc", CHECK_UAF_CMD);
    assert_eq!(output.contains("detected"), false);
}

#[test]
fn test_false_clone1() {
    #[allow(unused)]
    let output = run_with_args("uaf/false_clone1", CHECK_UAF_CMD);
    assert_eq!(output.contains("detected"), false);
}

#[test]
fn test_false_field_clone() {
    #[allow(unused)]
    let output = run_with_args("uaf/false_field_clone", CHECK_UAF_CMD);
    assert_eq!(detected_high_confidence(&output), false);
}

#[test]
fn test_false_mutate() {
    #[allow(unused)]
    let output = run_with_args("uaf/false_mutate", CHECK_UAF_CMD);
    assert_eq!(output.contains("detected"), false);
}

#[test]
fn test_false_loop_drop() {
    #[allow(unused)]
    let output = run_with_args("uaf/false_loop_drop", CHECK_UAF_CMD);
    assert_eq!(output.contains("detected"), false);
}

#[test]
fn test_false_memtake() {
    #[allow(unused)]
    let output = run_with_args("uaf/false_memtake", CHECK_UAF_CMD);
    assert_eq!(output.contains("detected"), false);
}

#[test]
fn test_reference() {
    #[allow(unused)]
    let output = run_with_args("uaf/false_reference", CHECK_UAF_CMD);
    assert_eq!(output.contains("detected"), false);
}

// ===============Alias(MOP) Analysis Test==============
#[test]
fn test_alias_from_raw_parts_in() {
    let output = run_with_args("alias/alias_from_raw_parts_in", ANALYZE_ALIAS_CMD);
    assert_eq!(output.contains("foo\": (0.0,1)"), true);
}

#[test]
fn test_alias_from_raw_parts() {
    let output = run_with_args("alias/alias_from_raw_parts", ANALYZE_ALIAS_CMD);
    assert_eq!(output.contains("foo\": (0,1)"), true);
}

#[test]
fn test_alias_not_alias_iter() {
    let output = run_with_args("alias/not_alias_iter", ANALYZE_ALIAS_CMD);
    assert_eq!(output.contains("foo\": null"), true);
}

#[test]
fn test_alias_field() {
    let output = run_with_args("alias/alias_field", ANALYZE_ALIAS_CMD);
    assert_eq!(
        output.contains("\"foo\": (0,1.1), (0,1.0)")
            || output.contains("\"foo\": (0,1.0), (0,1.1)"),
        true
    );
}

#[test]
fn test_alias_lib_no_caller() {
    let output = run_with_args("alias/alias_lib_no_caller", ANALYZE_ALIAS_CMD);
    assert_eq!(output.contains("new\": (0.0,1.0)"), true);
}

#[test]
fn test_alias_scc() {
    let output = run_with_args("alias/alias_scc", ANALYZE_ALIAS_CMD);
    assert_eq!(output.contains("foo\": (0,1)"), true);
}

#[test]
fn test_alias_sub_scc1() {
    let output = run_with_args("alias/alias_sub_scc1", ANALYZE_ALIAS_CMD);
    assert_eq!(output.contains("foo\": (0,1)"), true);
}

#[test]
fn test_alias_sub_scc2() {
    let output = run_with_args("alias/alias_sub_scc2", ANALYZE_ALIAS_CMD);
    assert_eq!(output.contains("foo\": (0,1), (0,2)"), true);
}

#[test]
fn test_alias_switch() {
    let output = run_with_args("alias/alias_switch", ANALYZE_ALIAS_CMD);
    assert_eq!(output.contains("foo\": (0,1)"), true);
}

#[test]
fn test_alias_copy_on_deref() {
    let output = run_with_args("alias/alias_copy_for_deref", ANALYZE_ALIAS_CMD);
    assert_eq!(output.contains("new\": (0.0,1.0)"), true);
}

#[test]
fn test_alias_indirect() {
    let output = run_with_args("alias/alias_indirect", ANALYZE_ALIAS_CMD);
    assert_eq!(output.contains("iter_prop\": (0.0,1.0)"), true);
}

// ===============Alias(MFP) Analysis Test==============
#[test]
fn test_alias_mfp_from_raw_parts_in() {
    let output = run_with_args("alias/alias_from_raw_parts_in", ANALYZE_ALIAS_MFP_CMD);
    assert_eq!(output.contains("foo\": (0.0,1)"), true);
}

#[test]
fn test_alias_mfp_from_raw_parts() {
    let output = run_with_args("alias/alias_from_raw_parts", ANALYZE_ALIAS_MFP_CMD);
    // assert_eq!(output.contains("foo\": (0,1)"), true);
    assert_eq!(output.contains("foo\": (0.0,1)"), true); // This is slightly different from MOP
}

#[test]
fn test_alias_mfp_not_alias_iter() {
    let output = run_with_args("alias/not_alias_iter", ANALYZE_ALIAS_MFP_CMD);
    assert_eq!(output.contains("foo\": null"), true);
}

#[test]
fn test_alias_mfp_field() {
    let output = run_with_args("alias/alias_field", ANALYZE_ALIAS_MFP_CMD);
    assert_eq!(
        output.contains("\"foo\": (0,1.1), (0,1.0)")
            || output.contains("\"foo\": (0,1.0), (0,1.1)"),
        true
    );
}

#[test]
fn test_alias_mfp_lib_no_caller() {
    let output = run_with_args("alias/alias_lib_no_caller", ANALYZE_ALIAS_MFP_CMD);
    assert_eq!(output.contains("new\": (0.0,1.0)"), true);
}

#[test]
fn test_alias_mfp_scc() {
    let output = run_with_args("alias/alias_scc", ANALYZE_ALIAS_MFP_CMD);
    assert_eq!(output.contains("foo\": (0,1)"), true);
}

#[test]
fn test_alias_mfp_sub_scc1() {
    let output = run_with_args("alias/alias_sub_scc1", ANALYZE_ALIAS_MFP_CMD);
    assert_eq!(output.contains("foo\": (0,1)"), true);
}

#[test]
fn test_alias_mfp_sub_scc2() {
    let output = run_with_args("alias/alias_sub_scc2", ANALYZE_ALIAS_MFP_CMD);
    assert_eq!(output.contains("foo\": (0,1), (0,2)"), true);
}

#[test]
fn test_alias_mfp_switch() {
    let output = run_with_args("alias/alias_switch", ANALYZE_ALIAS_MFP_CMD);
    assert_eq!(output.contains("foo\": (0,1)"), true);
}

#[test]
fn test_alias_mfp_copy_on_deref() {
    let output = run_with_args("alias/alias_copy_for_deref", ANALYZE_ALIAS_MFP_CMD);
    assert_eq!(output.contains("new\": (0.0,1.0)"), true);
}

#[test]
fn test_alias_mfp_indirect() {
    let output = run_with_args("alias/alias_indirect", ANALYZE_ALIAS_MFP_CMD);
    assert_eq!(output.contains("iter_prop\": (0.0,1.0)"), true);
}

#[test]
fn test_leak_ctor() {
    let output = run_with_args("leak/leak_ctor", CHECK_MLEAK_CMD);
    assert_eq!(
        output.contains("Memory Leak detected in function main"),
        false
    );
}

#[test]
fn test_leak_orphan() {
    let output = run_with_args("leak/leak_orphan", CHECK_MLEAK_CMD);
    assert_eq!(
        output.contains("Memory Leak detected in function main"),
        true
    );
}

#[test]
fn test_leak_orphan_timeout() {
    let mut args = Vec::from(["--timeout", "0"]);
    args.extend(CHECK_MLEAK_CMD);
    let output = run_with_args("leak/leak_orphan", &args);
    assert!(output.contains("Process killed due to timeout"));
}

#[test]
fn test_leak_proxy() {
    let output = run_with_args("leak/leak_proxy", CHECK_MLEAK_CMD);
    assert_eq!(
        output.contains("Memory Leak detected in function main"),
        true
    );
}

#[test]
fn test_heap_cell() {
    let output = run_with_args("ownedheap/heap_cell", ANALYZE_OWNED_HEAP_CMD);
    assert_eq!(
        output.contains("Cell\": False, <1>")
            && output.contains("RefCell\": False, <1>")
            && output.contains("UnsafeCell\": False, <1>")
            && output.contains("Rc\": True, <1,1>")
            && output.contains("Arc\": True, <1,1>")
            && output.contains("UniqueRc\": True, <1,1>"),
        true
    );
}

#[test]
fn test_heap_collections() {
    let output = run_with_args("ownedheap/heap_collections", ANALYZE_OWNED_HEAP_CMD);
    assert_eq!(
        output.contains("Unique\": True, <0>")
            && output.contains("Box\": True, <0,1>")
            && output.contains("Vec\": True, <0,1>")
            && output.contains("String\": True, <>")
            && output.contains("LinkedList\": True, <1,1>")
            && output.contains("HashMap\": True, <0,0,1>")
            && output.contains("BTreeMap\": True, <0,0,1>")
            && output.contains("HashSet\": True, <0,1>")
            && output.contains("BTreeSet\": True, <0,1>"),
        true
    );
}

#[test]
fn test_heap_nested() {
    let output: String = run_with_args("ownedheap/heap_nested", ANALYZE_OWNED_HEAP_CMD);
    assert_eq!(
        output.contains("X\": False, <1>")
            && output.contains("Y\": False, <1>")
            && output.contains("Example\": True, <1,1,0,1>"),
        true
    );
}

#[test]
fn test_heap_proxy() {
    let output = run_with_args("ownedheap/heap_proxy", ANALYZE_OWNED_HEAP_CMD);
    assert_eq!(
        output.contains("Proxy1\": False, <0>")
            && output.contains("Proxy2\": True, <0>")
            && output.contains("Proxy3\": False, <0,0>")
            && output.contains("Proxy4\": False, <1>")
            && output.contains("Proxy5\": True, <0>"),
        true
    );
}

#[test]
fn test_upg_safe_caller() {
    let output = run_with_args("upg/safe_caller", ANALYZE_UPG_CMD);
    assert_eq!(output.contains("from_raw_parts"), true);
}

#[test]
fn test_upg_raw_ptr() {
    let output = run_with_args("upg/raw_ptr", ANALYZE_UPG_CMD);
    assert_eq!(output.contains("raw_ptr_deref_dummy"), true);
}

#[test]
fn test_upg_static_mut() {
    let output = run_with_args("upg/static_mut", ANALYZE_UPG_CMD);
    assert_eq!(output.contains("::COUNTER"), true);
}

#[test]
fn test_ssa_transform() {
    let output = run_with_args("ssa/ssa_transform", ANALYZE_SSA_CMD);
    assert_eq!(output.contains("ssa lvalue check true"), true);
}
#[test]
fn test_range_analysis() {
    let output = run_with_args("range/range_1", ANALYZE_RANGE_CMD);

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

fn test_interprocedual_range_analysis() {
    let output = run_with_args("range/range_2", ANALYZE_RANGE_CMD);

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
fn test_callgraph_dynamic_dispatch() {
    let output = run_with_args("callgraph/dynamic", ANALYZE_CALLGRAPH_CMD);

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
fn test_symbolic_interval() {
    let output = run_with_args("range/range_symbolic", ANALYZE_RANGE_CMD);

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
