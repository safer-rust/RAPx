#![allow(clippy::bool_assert_comparison)]
use fs4::fs_std::FileExt;
use std::ffi::OsString;
use std::fs::File;
use std::path::{Path, PathBuf};
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

fn project_path(dir: &str) -> PathBuf {
    Path::new("tests").join(dir)
}

/// Count `  Path [` lines inside a function's output block.
fn path_count_for(output: &str, fn_name: &str) -> usize {
    let header = format!("Function: \"{}\":", fn_name);
    let mut in_block = false;
    let mut count = 0;
    for line in output.lines() {
        if line.contains(&header) {
            in_block = true;
            continue;
        }
        if in_block {
            if line.contains("Function:") {
                break;
            }
            if line.trim().starts_with("Path [") {
                count += 1;
            }
        }
    }
    count
}

#[inline(always)]
fn run_with_args(dir: &str, args: &[&str]) -> String {
    // let raw_path = "./tests/".to_owned() + dir;
    // let project_path = Path::new(&raw_path);
    let project_path = project_path(dir);

    let lock_path = project_path.join(".rapx-test.lock");
    let lock_file = File::create(&lock_path).expect("Failed to create lock file");
    lock_file.lock_exclusive().expect("Failed to acquire lock");

    let mut command = cargo_rapx_command();
    let output = command
        .args(args)
        .current_dir(project_path)
        .output()
        .expect("Failed to execute cargo rapx");

    lock_file.unlock().expect("Failed to release lock");

    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn cargo_rapx_command() -> Command {
    if let Some(path) = option_env!("CARGO_BIN_EXE_cargo-rapx") {
        let path = PathBuf::from(path);
        let mut command = Command::new(&path);
        command.arg("rapx");
        prepend_local_bin_to_path(&mut command, path.parent());
        return command;
    }

    let mut command = Command::new("cargo");
    command.arg("rapx");
    command
}

fn prepend_local_bin_to_path(command: &mut Command, cargo_rapx_dir: Option<&Path>) {
    let local_rapx_dir = option_env!("CARGO_BIN_EXE_rapx")
        .and_then(|path| PathBuf::from(path).parent().map(Path::to_path_buf))
        .or_else(|| cargo_rapx_dir.map(Path::to_path_buf));
    let Some(local_rapx_dir) = local_rapx_dir else {
        return;
    };

    let mut paths = vec![local_rapx_dir];
    if let Some(path) = std::env::var_os("PATH") {
        paths.extend(std::env::split_paths(&path));
    }
    if let Ok(path) = std::env::join_paths(paths) {
        command.env("PATH", OsString::from(path));
    }
}

fn assert_contain(output: &str, pattern: &str) {
    assert!(
        output.contains(pattern),
        "Missing pattern:\n{}\nFull output:\n{}",
        pattern,
        output
    );
}

fn assert_not_contain(output: &str, pattern: &str) {
    assert!(
        !output.contains(pattern),
        "Unexpected pattern:\n{}\nFull output:\n{}",
        pattern,
        output
    );
}

fn assert_unproved_exclusive(output: &str, function: &str, allowed: &[&str]) {
    assert_contain(output, &format!("function: {function}"));
    let block = extract_block_after(output, &format!("function: {function}"));

    // At least the primary (first) property must appear as Failed/Unknown.
    if let Some(primary) = allowed.first() {
        assert!(
            block.contains(&format!("{primary} | Failed"))
                || block.contains(&format!("{primary} | Unknown")),
            "Expected {primary} | Failed/Unknown for {function}\nBlock:\n{block}"
        );
    }

    // No property outside the allowed set may appear as Failed/Unknown.
    let mut actual: Vec<&str> = Vec::new();
    for line in block.lines() {
        for sfx in ["| Failed", "| Unknown"] {
            let Some(idx) = line.find(sfx) else { continue };
            let prop = line[..idx].trim_end().rsplit(' ').next().unwrap_or("");
            if !prop.is_empty() && prop != "Unknown" {
                actual.push(prop);
            }
        }
    }
    actual.sort();
    actual.dedup();
    let unexpected: Vec<_> = actual.iter().filter(|p| !allowed.contains(p)).collect();
    assert!(
        unexpected.is_empty(),
        "Unexpected Failed/Unknown for {function}: {unexpected:?}\nAllowed: {allowed:?}\nBlock:\n{block}"
    );
    assert_contain(output, "result: UNSOUND");
}

fn extract_block_after<'a>(text: &'a str, marker: &str) -> &'a str {
    let Some(pos) = text.find(marker) else {
        return "";
    };
    let rest = &text[pos + marker.len()..];
    match rest.find("function: ") {
        Some(end) => &rest[..end],
        None => rest,
    }
}

const CHECK_UAF_CMD: &[&str] = &["check", "-f"];
const CHECK_MLEAK_CMD: &[&str] = &["check", "-m"];
const ANALYZE_ALIAS_CMD: &[&str] = &["analyze", "alias"];
const ANALYZE_ALIAS_MFP_CMD: &[&str] = &["analyze", "alias", "--strategy", "mfp"];
const ANALYZE_OWNED_HEAP_CMD: &[&str] = &["analyze", "ownedheap"];
const ANALYZE_PATHS_CMD: &[&str] = &["analyze", "paths"];
const ANALYZE_PATHS_REPEAT1_CMD: &[&str] = &["analyze", "paths", "--postfix-repeat", "1"];
const ANALYZE_PATHS_REPEAT2_CMD: &[&str] = &["analyze", "paths", "--postfix-repeat", "2"];
const ANALYZE_SAFETYFLOW_CMD: &[&str] = &["analyze", "safetyflow"];
const ANALYZE_SSA_CMD: &[&str] = &["analyze", "ssa"];
const ANALYZE_RANGE_CMD: &[&str] = &["analyze", "range"];
const ANALYZE_CALLGRAPH_CMD: &[&str] = &["analyze", "callgraph"];
const ANALYZE_ADG_CMD: &[&str] = &["analyze", "adg", "--dump", "api_graph.yml"];
const VERIFY_CMD: &[&str] = &["verify"];
const VERIFY_TARGETED_CMD: &[&str] = &["verify", "--mode", "targeted"];
const VERIFY_PREPARE_CMD: &[&str] = &["verify", "--prepare-targets"];
const VERIFY_ALLOW_REPEAT_CMD: &[&str] = &["verify", "--postfix-repeat", "1"];
const VERIFY_ALLOW_REPEAT2_CMD: &[&str] = &["verify", "--postfix-repeat", "2"];
const VERIFY_SCAN_CMD: &[&str] = &["verify", "--mode", "scan"];
const VERIFY_INVLESS_CMD: &[&str] = &["verify", "--mode", "invless"];

// ================Dangling Pointer Detection Test=====================
#[test]
fn uaf_cases() {
    let output = run_with_args("check/uaf_1", CHECK_UAF_CMD);
    assert_contain(
        &output,
        "Dangling pointer detected in function \"create_vec\"",
    );

    let output = run_with_args("check/uaf_2", CHECK_UAF_CMD);
    assert_contain(&output, "Double free detected in function \"main\"");

    let output = run_with_args("check/uaf_3", CHECK_UAF_CMD);
    assert_contain(&output, "Double free detected");

    let output = run_with_args("check/uaf_4", CHECK_UAF_CMD);
    assert_contain(&output, "Dangling pointer detected in function \"call\"");

    let output = run_with_args("check/uaf_5", CHECK_UAF_CMD);
    assert_contain(&output, "Use-after-free detected in function \"main\"");

    let output = run_with_args("check/uaf_6", CHECK_UAF_CMD);
    assert_contain(&output, "Use-after-free detected in function \"main\"");

    let output = run_with_args("check/uaf_7", CHECK_UAF_CMD);
    assert_contain(&output, "Double free detected in function \"main\"");

    let output = run_with_args("check/uaf_8", CHECK_UAF_CMD);
    assert_contain(&output, "Use-after-free detected in function \"main\"");

    let output = run_with_args("check/uaf_9", CHECK_UAF_CMD);
    assert_contain(&output, "Use-after-free detected in function \"main\"");

    let output = run_with_args("check/uaf_10", CHECK_UAF_CMD);
    assert_contain(&output, "Double free detected in function \"evil_test\"");
}

#[test]
fn uaf_false_cases() {
    let output = run_with_args("check/uaf_false_1", CHECK_UAF_CMD);
    assert!(
        !detected_high_confidence(&output),
        "Unexpected high-confidence bug in output:\n{}",
        output
    );

    let output = run_with_args("check/uaf_false_2", CHECK_UAF_CMD);
    assert_not_contain(&output, "detected");

    let output = run_with_args("check/uaf_false_3", CHECK_UAF_CMD);
    assert!(
        !detected_high_confidence(&output),
        "Unexpected high-confidence bug in output:\n{}",
        output
    );

    let output = run_with_args("check/uaf_false_4", CHECK_UAF_CMD);
    assert_not_contain(&output, "detected");

    #[allow(unused)]
    let output = run_with_args("check/uaf_false_5", CHECK_UAF_CMD);
    assert_not_contain(&output, "detected");

    #[allow(unused)]
    let output = run_with_args("check/uaf_false_6", CHECK_UAF_CMD);
    assert!(
        !detected_high_confidence(&output),
        "Unexpected high-confidence bug in output:\n{}",
        output
    );

    #[allow(unused)]
    let output = run_with_args("check/uaf_false_8", CHECK_UAF_CMD);
    assert_not_contain(&output, "detected");

    #[allow(unused)]
    let output = run_with_args("check/uaf_false_9", CHECK_UAF_CMD);
    assert_not_contain(&output, "detected");

    #[allow(unused)]
    let output = run_with_args("check/uaf_false_10", CHECK_UAF_CMD);
    assert_not_contain(&output, "detected");

    #[allow(unused)]
    let output = run_with_args("check/uaf_false_11", CHECK_UAF_CMD);
    assert_not_contain(&output, "detected");
}

// ===============Alias(MOP) Analysis Test==============
#[test]
fn alias_cases() {
    let output = run_with_args("analyze/alias_1", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "foo\": (0.0,1)");

    let output = run_with_args("analyze/alias_2", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "foo\": (0,1)");

    let output = run_with_args("analyze/alias_3", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "foo\": null");

    let output = run_with_args("analyze/alias_4", ANALYZE_ALIAS_CMD);
    let has_either = output.contains("\"foo\": (0,1.1), (0,1.0)")
        || output.contains("\"foo\": (0,1.0), (0,1.1)");
    assert!(
        has_either,
        "Missing alias field variations\nFull output:\n{}",
        output
    );

    let output = run_with_args("analyze/alias_5", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "new\": (0.0,1.0)");

    let output = run_with_args("analyze/alias_6", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "foo\": (0,1)");

    let output = run_with_args("analyze/alias_7", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "foo\": (0,1)");

    let output = run_with_args("analyze/alias_8", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "foo\": (0,1), (0,2)");

    let output = run_with_args("analyze/alias_9", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "foo\": (0,1)");

    let output = run_with_args("analyze/alias_10", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "new\": (0.0,1.0)");

    let output = run_with_args("analyze/alias_11", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "iter_prop\": (0.0,1.0)");
}

// ===============Alias(MFP) Analysis Test==============
#[test]
fn alias_mfp_cases() {
    let output = run_with_args("analyze/alias_1", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "foo\": (0.0,1)");

    let output = run_with_args("analyze/alias_2", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "foo\": (0.0,1)");

    let output = run_with_args("analyze/alias_3", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "foo\": null");

    let output = run_with_args("analyze/alias_4", ANALYZE_ALIAS_MFP_CMD);
    let has_either = output.contains("\"foo\": (0,1.1), (0,1.0)")
        || output.contains("\"foo\": (0,1.0), (0,1.1)");
    assert!(
        has_either,
        "Missing alias field variations\nFull output:\n{}",
        output
    );

    let output = run_with_args("analyze/alias_5", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "new\": (0.0,1.0)");

    let output = run_with_args("analyze/alias_6", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "foo\": (0,1)");

    let output = run_with_args("analyze/alias_7", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "foo\": (0,1)");

    let output = run_with_args("analyze/alias_8", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "foo\": (0,1), (0,2)");

    let output = run_with_args("analyze/alias_9", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "foo\": (0,1)");

    let output = run_with_args("analyze/alias_10", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "new\": (0.0,1.0)");

    let output = run_with_args("analyze/alias_11", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "iter_prop\": (0.0,1.0)");
}

#[test]
fn leak_cases() {
    let output = run_with_args("check/memleak_1", CHECK_MLEAK_CMD);
    assert_not_contain(&output, "Memory Leak detected in function main");

    let output = run_with_args("check/memleak_2", CHECK_MLEAK_CMD);
    assert_contain(&output, "Memory Leak detected in function main");

    let output = run_with_args("check/memleak_3", CHECK_MLEAK_CMD);
    assert_contain(&output, "Memory Leak detected in function main");
}

#[test]
fn heap_cases() {
    let output = run_with_args("analyze/ownedheap_cell", ANALYZE_OWNED_HEAP_CMD);
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

    let output = run_with_args("analyze/ownedheap_collections", ANALYZE_OWNED_HEAP_CMD);
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

    let output = run_with_args("analyze/ownedheap_nested", ANALYZE_OWNED_HEAP_CMD);
    for pattern in [
        "X\": False, <1>",
        "Y\": False, <1>",
        "Example\": True, <1,1,0,1>",
    ] {
        assert_contain(&output, pattern);
    }

    let output = run_with_args("analyze/ownedheap_proxy", ANALYZE_OWNED_HEAP_CMD);
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
    let output = run_with_args("analyze/path_1", ANALYZE_PATHS_CMD);
    assert_contain(&output, "Function: \"example\":");
    assert_contain(&output, "Path [0, 3, 4, 6, 7, 9]");
    assert_contain(&output, "Path [0, 2, 4, 5, 8, 9]");
    assert_eq!(path_count_for(&output, "example"), 2);

    let output = run_with_args("analyze/path_2", ANALYZE_PATHS_CMD);
    assert_contain(&output, "Function: \"read2\":");
    assert_contain(&output, "Path [0, 1, 2, 3, 10, 11]");
    assert_contain(&output, "Path [0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11]");
    assert_contain(&output, "Path [0, 1, 2, 4, 5, 6, 12*]");
    assert_eq!(path_count_for(&output, "read2"), 3);

    let output = run_with_args("analyze/path_3", ANALYZE_PATHS_CMD);
    assert_contain(&output, "Function: \"retry_once\":");
    assert_contain(&output, "Path [0, 1, 2, 1, 3]");
    assert_eq!(path_count_for(&output, "retry_once"), 1);

    let output = run_with_args("analyze/path_4", ANALYZE_PATHS_CMD);
    assert_contain(&output, "Function: \"read1\":");
    assert_contain(&output, "Path [0, 1, 2, 6]");
    assert_contain(&output, "Path [0, 1, 3, 4, 1, 3, 5, 6]");
    assert_eq!(path_count_for(&output, "read1"), 2);

    let output = run_with_args("analyze/path_5", ANALYZE_PATHS_CMD);
    assert_contain(&output, "Function: \"read2\":");
    assert_contain(&output, "Path [0, 1, 2, 3, 9]");
    assert_eq!(path_count_for(&output, "read2"), 2);

    let output = run_with_args("analyze/path_false_1", ANALYZE_PATHS_CMD);
    assert_contain(&output, "Function: \"classify\":");
    assert_contain(&output, "Path [0, 1, 2]");
    assert_contain(&output, "Path [0, 1, 3, 4, 5, 6, 7, 10, 1, 2]");
    assert_contain(&output, "Path [0, 1, 3, 4, 5, 8, 9, 10, 1, 2]");
    assert_eq!(path_count_for(&output, "classify"), 9);

    let output = run_with_args("analyze/path_6", ANALYZE_PATHS_CMD);
    assert_contain(&output, "Function: \"early_exit\":");
    assert_contain(&output, "Path [0, 1, 2]");
    assert_contain(&output, "Path [0, 1, 3, 4, 1, 2]");
    assert_eq!(path_count_for(&output, "early_exit"), 2);

    let output = run_with_args("analyze/path_7", ANALYZE_PATHS_CMD);
    assert_contain(&output, "Function: \"walk\":");
    assert_contain(&output, "Path [0, 1, 2]");
    assert_contain(&output, "Path [0, 1, 3, 4, 5, 9, 1, 2]");
    assert_contain(&output, "Path [0, 1, 3, 4, 6, 7, 8, 4, 5, 9, 1, 2]");
    assert_contain(
        &output,
        "Path [0, 1, 3, 4, 6, 7, 8, 4, 5, 9, 1, 3, 4, 5, 9, 1, 2]",
    );
    assert_eq!(path_count_for(&output, "walk"), 4);

    let output = run_with_args("analyze/path_false_1", ANALYZE_PATHS_REPEAT1_CMD);
    assert_eq!(path_count_for(&output, "classify"), 39);
    assert_contain(&output, "Path [0, 1, 2]");

    let output = run_with_args("analyze/path_false_1", ANALYZE_PATHS_REPEAT2_CMD);
    assert_eq!(path_count_for(&output, "classify"), 128);
    assert_contain(&output, "Path [0, 1, 2]");
}

// ================ Align Unsound Cases =============
#[test]
fn align_unsound_cases() {
    let output = run_with_args("verify_units/align_unsound_1", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_enum_paths_inside_scc", &["Align"]);

    let output = run_with_args("verify_units/align_unsound_2", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_scc_selects_mixed_source", &["Align"]);

    let output = run_with_args("verify_units/align_unsound_3", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_scc_computes_misaligned_offset",
        &["Align"],
    );

    let output = run_with_args("verify_units/align_unsound_4", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_nested_scc_controller", &["Align"]);

    let output = run_with_args("verify_units/align_unsound_5", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_iteration_count_can_leave_unaligned",
        &["Align"],
    );

    let output = run_with_args("verify_units/align_unsound_6", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_pre_scc_guard_overwritten_by_scc",
        &["Align"],
    );

    let output = run_with_args("verify_units/align_unsound_7", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_scc_guard_only_on_one_branch", &["Align"]);

    let output = run_with_args("verify_units/align_unsound_8", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_helper_with_disjunctive_guard", &["Align"]);

    let output = run_with_args("verify_units/align_unsound_9", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_helper_return_path_selects_bad_ptr",
        &["Align"],
    );

    let output = run_with_args("verify_units/align_unsound_10", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_multi_hop_missing_offset_guard",
        &["Align"],
    );

    let output = run_with_args("verify_units/align_unsound_11", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_sub_missing_guard", &["Align"]);

    let output = run_with_args("verify_units/align_unsound_12", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_byte_offset_one", &["Align"]);

    let output = run_with_args("verify_units/align_unsound_13", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_usize_add_missing_offset_guard",
        &["Align"],
    );

    let output = run_with_args("verify_units/align_unsound_14", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_repr_packed_field", &["Align"]);

    let output = run_with_args("verify_units/align_unsound_15", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_four_phase_scc_alignment", &["Align"]);

    let output = run_with_args("verify_units/align_unsound_16", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_trait_bound_cross_cast", &["Align"]);

    let output = run_with_args("verify_units/align_unsound_17", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_contract_type_param_binds_generic",
        &["Align"],
    );

    let output = run_with_args(
        "verify_units/align_repeat_threshold",
        VERIFY_ALLOW_REPEAT2_CMD,
    );
    assert_unproved_exclusive(&output, "repeat2_reveals_delayed_unaligned", &["Align"]);
}

// ================ Align Sound Cases =============
#[test]
fn align_sound_cases() {
    let output = run_with_args("verify_units/align_sound_1", VERIFY_CMD);
    assert_contain(&output, "function: sound_named_contract_binds_callsite_arg");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_2", VERIFY_CMD);
    assert_contain(&output, "function: sound_enum_paths_inside_scc");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_3", VERIFY_CMD);
    assert_contain(&output, "function: sound_scc_selects_aligned_source");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_4", VERIFY_CMD);
    assert_contain(&output, "function: sound_scc_computes_aligned_offset");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_5", VERIFY_CMD);
    assert_contain(&output, "function: sound_nested_scc_controller");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_6", VERIFY_CMD);
    assert_contain(
        &output,
        "function: sound_iteration_count_switches_aligned_offsets",
    );
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_7", VERIFY_CMD);
    assert_contain(
        &output,
        "function: sound_unrelated_scc_does_not_pollute_align",
    );
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_8", VERIFY_CMD);
    assert_contain(
        &output,
        "function: sound_unrelated_nested_scc_with_bad_scratch",
    );
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_9", VERIFY_CMD);
    assert_contain(&output, "function: sound_pre_scc_guard_with_scc_offsets");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_10", VERIFY_CMD);
    assert_contain(&output, "function: sound_scc_internal_noise_ignored");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_11", VERIFY_CMD);
    assert_contain(&output, "function: sound_helper_with_conjunctive_guard");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_12", VERIFY_CMD);
    assert_contain(&output, "function: sound_nested_if_before_helper");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_13", VERIFY_CMD);
    assert_contain(&output, "function: sound_helper_return_paths_all_aligned");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_14", VERIFY_CMD);
    assert_contain(&output, "function: sound_multi_hop_helper");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_15", VERIFY_CMD);
    assert_contain(&output, "function: sound_unrelated_condition_ignored");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_16", VERIFY_CMD);
    assert_contain(&output, "function: sound_add_sub_chain");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_17", VERIFY_CMD);
    assert_contain(&output, "function: sound_offset_zero_preserves_align");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_18", VERIFY_CMD);
    assert_contain(&output, "function: sound_usize_round_trip");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_19", VERIFY_CMD);
    assert_contain(&output, "function: sound_usize_add_guarded");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_20", VERIFY_CMD);
    assert_contain(&output, "function: sound_usize_mul_div_offset");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_21", VERIFY_CMD);
    assert_contain(&output, "function: sound_repr_c_field");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_22", VERIFY_CMD);
    assert_contain(&output, "function: sound_repr_align_object");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_23", VERIFY_CMD);
    assert_contain(&output, "function: sound_zst_trivial_alignment");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_24", VERIFY_CMD);
    assert_contain(&output, "function: sound_trait_bound_cross_cast");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_25", VERIFY_CMD);
    assert_contain(
        &output,
        "function: sound_contract_type_param_binds_concrete",
    );
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/align_sound_26", VERIFY_CMD);
    assert_contain(&output, "function: sound_contract_type_param_binds_generic");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args(
        "verify_units/align_repeat_threshold",
        VERIFY_ALLOW_REPEAT_CMD,
    );
    assert_contain(&output, "function: repeat2_reveals_delayed_unaligned");
    assert_contain(&output, "result: SOUND");
}

// ================ NonNull Sound Cases =============
#[test]
fn nonnull_sound_cases() {
    let output = run_with_args("verify_units/nonnull_sound_7", VERIFY_CMD);
    assert_contain(&output, "function: sound_ref_cast_copy_chain");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/nonnull_sound_2", VERIFY_CMD);
    assert_contain(&output, "function: sound_slice_as_ptr_branch");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/nonnull_sound_3", VERIFY_CMD);
    assert_contain(&output, "function: sound_intra_helper_from_ref");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/nonnull_sound_4", VERIFY_CMD);
    assert_contain(&output, "function: sound_scc_unrelated_state");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/nonnull_sound_5", VERIFY_CMD);
    assert_contain(&output, "function: sound_raw_arg_guarded");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/nonnull_sound_6", VERIFY_CMD);
    assert_contain(&output, "function: sound_nonnull_wrapper_from_ref");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/nonnull_sound_1", VERIFY_CMD);
    assert_contain(&output, "function: caller_with_contract");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_chained_propagation");
    assert_contain(&output, "result: SOUND");
}

// ================ NonNull Unsound Cases =============
#[test]
fn nonnull_unsound_cases() {
    let output = run_with_args("verify_units/nonnull_unsound_1", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_explicit_null_constant", &["NonNull"]);

    let output = run_with_args("verify_units/nonnull_unsound_2", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_raw_pointer_argument", &["NonNull"]);

    let output = run_with_args("verify_units/nonnull_unsound_3", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_branch_selects_null", &["NonNull"]);

    let output = run_with_args("verify_units/nonnull_unsound_4", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_scc_overwrites_with_null", &["NonNull"]);

    let output = run_with_args("verify_units/nonnull_unsound_5", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_unrelated_guard", &["NonNull"]);

    let output = run_with_args("verify_units/nonnull_unsound_6", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_nonnull_wrapper_from_null", &["NonNull"]);
}

// ================ Allocated Sound Cases =============
#[test]
fn allocated_sound_cases() {
    let output = run_with_args("verify_units/allocated_sound_1", VERIFY_CMD);
    assert_contain(&output, "function: sound_stack_local_allocated");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/allocated_sound_2", VERIFY_CMD);
    assert_contain(&output, "function: sound_slice_prefix_allocated");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/allocated_sound_3", VERIFY_CMD);
    assert_contain(&output, "function: sound_live_vec_allocated");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/allocated_sound_4", VERIFY_CMD);
    assert_contain(&output, "function: sound_live_box_allocated");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/allocated_sound_5", VERIFY_CMD);
    assert_contain(&output, "function: sound_branch_selects_live_local");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/allocated_sound_6", VERIFY_CMD);
    assert_contain(&output, "function: sound_loop_slice_element_allocated");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/allocated_sound_7", VERIFY_CMD);
    assert_contain(&output, "function: sound_scc_selects_live_array");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/allocated_sound_8", VERIFY_CMD);
    assert_contain(&output, "function: sound_intra_returns_slice_pointer");
    assert_contain(&output, "result: SOUND");
}

// ================ Allocated Unsound Cases =============
#[test]
fn allocated_unsound_cases() {
    let output = run_with_args("verify_units/allocated_unsound_1", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_null_not_allocated", &["Allocated"]);

    let output = run_with_args("verify_units/allocated_unsound_2", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_stack_scope_ended", &["Allocated"]);

    let output = run_with_args("verify_units/allocated_unsound_3", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_vec_dropped_before_use", &["Allocated"]);

    let output = run_with_args("verify_units/allocated_unsound_4", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_empty_slice_needs_one_element",
        &["Allocated"],
    );

    let output = run_with_args("verify_units/allocated_unsound_5", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_branch_may_select_null", &["Allocated"]);

    let output = run_with_args("verify_units/allocated_unsound_6", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_scc_overwrites_with_null", &["Allocated"]);

    let output = run_with_args("verify_units/allocated_unsound_7", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_vec_reallocates_old_pointer",
        &["Allocated"],
    );

    let output = run_with_args("verify_units/allocated_unsound_8", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_slice_too_short_for_requested_len",
        &["Allocated"],
    );

    let output = run_with_args("verify_units/allocated_unsound_9", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_intra_returns_dangling_pointer",
        &["Allocated"],
    );

    let output = run_with_args("verify_units/allocated_unsound_10", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_scc_selects_dead_temporary",
        &["Allocated"],
    );

    let output = run_with_args("verify_units/allocated_unsound_11", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_adjacent_stack_objects_do_not_merge",
        &["Allocated"],
    );
}

// ================ InBound Sound Cases =============
#[test]
fn inbound_sound_cases() {
    let output = run_with_args("verify_units/inbound_sound_1", VERIFY_CMD);
    assert_contain(&output, "function: sound_ptr_add_guarded");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/inbound_sound_2", VERIFY_CMD);
    assert_contain(&output, "function: sound_from_raw_parts_prefix_two");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/inbound_sound_3", VERIFY_CMD);
    assert_contain(&output, "function: sound_get_unchecked_generic");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/inbound_sound_4", VERIFY_CMD);
    assert_contain(&output, "function: sound_copy_nonoverlapping_one");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/inbound_sound_5", VERIFY_CMD);
    assert_contain(&output, "function: sound_intra_slice_add_guarded");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/inbound_sound_6", VERIFY_CMD);
    assert_contain(&output, "function: sound_scc_loop_index_guard");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/inbound_std_sound_1", VERIFY_CMD);
    assert_contain(&output, "function: sound_std_get_unchecked");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/inbound_std_sound_2", VERIFY_CMD);
    assert_contain(&output, "function: sound_std_copy_nonoverlapping");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/sliceindex_sound_01", VERIFY_CMD);
    assert_contain(&output, "function: sound_scalar_index_guard");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/sliceindex_sound_02", VERIFY_CMD);
    assert_contain(&output, "function: sound_range_index_guard");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/sliceindex_sound_03", VERIFY_CMD);
    assert_contain(&output, "function: sound_std_get_unchecked_sliceindex");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/sliceindex_sound_04", VERIFY_CMD);
    assert_contain(&output, "function: sound_std_range_get_unchecked");
    assert_contain(&output, "result: SOUND");
}

// ================ InBound Unsound Cases =============
#[test]
fn inbound_unsound_cases() {
    let output = run_with_args("verify_units/inbound_unsound_1", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_ptr_add_without_guard", &["InBound"]);

    let output = run_with_args("verify_units/inbound_unsound_2", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_from_raw_parts_two_only_nonempty",
        &["InBound"],
    );

    let output = run_with_args("verify_units/inbound_unsound_3", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_get_unchecked_wrong_guard", &["InBound"]);

    let output = run_with_args("verify_units/inbound_unsound_4", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_copy_nonoverlapping_dst_unguarded",
        &["InBound"],
    );

    let output = run_with_args("verify_units/inbound_unsound_5", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_branch_selects_unguarded_index",
        &["InBound"],
    );

    let output = run_with_args("verify_units/inbound_unsound_6", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_scc_off_by_one", &["InBound"]);

    let output = run_with_args("verify_units/inbound_unsound_7", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_len_guard_off_by_one", &["InBound"]);

    let output = run_with_args("verify_units/inbound_unsound_8", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_inclusive_range_off_by_one", &["InBound"]);

    let output = run_with_args("verify_units/inbound_unsound_9", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_ptr_add_off_by_one", &["InBound"]);

    let output = run_with_args("verify_units/inbound_std_unsound_1", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_std_get_unchecked_wrong_guard",
        &["InBound"],
    );

    let output = run_with_args("verify_units/inbound_std_unsound_2", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_std_copy_nonoverlapping_dst_unguarded",
        &["ValidPtr", "NonOverlap", "ValidNum"],
    );

    let output = run_with_args("verify_units/sliceindex_unsound_01", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_scalar_index_wrong_guard", &["InBound"]);

    let output = run_with_args("verify_units/sliceindex_unsound_02", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_range_index_missing_end_guard",
        &["InBound"],
    );

    let output = run_with_args("verify_units/sliceindex_unsound_03", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_std_range_missing_end_guard", &["InBound"]);
}

#[test]
fn init_std_sound_cases() {
    let output = run_with_args("verify_units/init_std_sound_1", VERIFY_CMD);
    assert_contain(&output, "function: sound_assume_init_read_after_write");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/init_std_sound_2", VERIFY_CMD);
    assert_contain(&output, "function: sound_assume_init_after_write");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/init_std_sound_3", VERIFY_CMD);
    assert_contain(&output, "function: sound_branch_local_init");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/init_std_sound_4", VERIFY_CMD);
    assert_contain(&output, "function: sound_intra_helper_initializes");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/init_std_sound_5", VERIFY_CMD);
    assert_contain(&output, "function: sound_loop_initializes_slice");
    assert_contain(&output, "Init | Proved");

    let output = run_with_args("verify_units/init_std_sound_6", VERIFY_CMD);
    assert_contain(&output, "function: sound_len_bound_loop_initializes_slice");
    assert_contain(&output, "Init | Proved");
}

// ================ Init Std Unsound Cases =============
#[test]
fn init_std_unsound_cases() {
    let output = run_with_args("verify_units/init_std_unsound_1", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_assume_init_read_without_write", &["Init"]);

    let output = run_with_args("verify_units/init_std_unsound_2", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_assume_init_without_write", &["Init"]);

    let output = run_with_args("verify_units/init_std_unsound_3", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_conditional_write_then_assume", &["Init"]);

    let output = run_with_args("verify_units/init_std_unsound_4", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_write_different_slot", &["Init"]);

    let output = run_with_args("verify_units/init_std_unsound_5", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_intra_helper_maybe_initializes", &["Init"]);

    let output = run_with_args("verify_units/init_std_unsound_6", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_from_raw_parts_uninitialized", &["Init"]);

    let output = run_with_args("verify_units/init_std_unsound_7", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_from_raw_parts_wrong_element_type",
        &["Init"],
    );

    let output = run_with_args("verify_units/init_std_unsound_8", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_len_bound_loop_skips_even_indices",
        &["Init"],
    );
}

// ================ ValidNum Sound Cases =============
#[test]
fn validnum_sound_cases() {
    let output = run_with_args("verify_units/validnum_sound_1", VERIFY_CMD);
    assert_contain(&output, "function: sound_guarded_less_than");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validnum_sound_2", VERIFY_CMD);
    assert_contain(&output, "function: sound_guarded_nonzero");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validnum_sound_3", VERIFY_CMD);
    assert_contain(&output, "function: sound_constant_sum_below_cap");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validnum_sound_4", VERIFY_CMD);
    assert_contain(&output, "function: sound_trait_bound_size_limit");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validnum_sound_5", VERIFY_CMD);
    assert_contain(&output, "function: sound_scc_validnum_index_guard");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validnum_sound_6", VERIFY_CMD);
    assert_contain(&output, "function: sound_guarded_variable_sum");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validnum_sound_7", VERIFY_CMD);
    assert_contain(&output, "function: sound_interval_guard");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validnum_sound_8", VERIFY_CMD);
    assert_contain(&output, "function: sound_trait_bound_align_order");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validnum_std_sound_1", VERIFY_CMD);
    assert_contain(&output, "function: sound_std_from_raw_parts_validnum");
    assert_contain(&output, "ValidNum | Proved");

    let output = run_with_args("verify_units/validnum_std_sound_2", VERIFY_CMD);
    assert_contain(&output, "function: sound_std_copy_nonoverlapping_validnum");
    assert_contain(&output, "ValidNum | Proved");

    let output = run_with_args("verify_units/as_chunks_sound_01", VERIFY_CMD);
    assert_contain(&output, "function: sound_as_chunks_unchecked_exact_div");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_exact_div_guard");
    assert_contain(&output, "result: SOUND");
}

// ================ ValidNum Unsound Cases =============
#[test]
fn validnum_unsound_cases() {
    let output = run_with_args("verify_units/validnum_unsound_1", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_missing_less_than_guard", &["ValidNum"]);

    let output = run_with_args("verify_units/validnum_unsound_2", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_missing_nonzero_guard", &["ValidNum"]);

    let output = run_with_args("verify_units/validnum_unsound_3", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_partial_sum_guard", &["ValidNum"]);

    let output = run_with_args("verify_units/validnum_unsound_4", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_trait_bound_missing_size_limit",
        &["ValidNum"],
    );

    let output = run_with_args("verify_units/validnum_unsound_5", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_interval_inclusive_guard", &["ValidNum"]);

    let output = run_with_args("verify_units/validnum_std_unsound_1", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_std_from_raw_parts_validnum_overflow",
        &["ValidNum", "ValidPtr", "Init"],
    );

    let output = run_with_args("verify_units/validnum_std_unsound_2", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_std_copy_nonoverlapping_validnum",
        &["ValidNum", "ValidPtr", "NonOverlap"],
    );

    let output = run_with_args("verify_units/as_chunks_unsound_01", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_as_chunks_unchecked_missing_exact_div",
        &["ValidNum"],
    );
    assert_unproved_exclusive(&output, "unsound_exact_div_missing_guard", &["ValidNum"]);
}

#[test]
fn validptr_sound_cases() {
    let output = run_with_args("verify_units/validptr_sound_1", VERIFY_CMD);
    assert_contain(&output, "function: sound_zst_dangling_valid_for_any_len");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validptr_sound_2", VERIFY_CMD);
    assert_contain(&output, "function: sound_stack_array_full_range");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validptr_sound_3", VERIFY_CMD);
    assert_contain(&output, "function: sound_slice_suffix_guarded");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validptr_sound_5", VERIFY_CMD);
    assert_contain(&output, "function: sound_signed_suffix_guarded");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validptr_sound_4", VERIFY_CMD);
    assert_contain(&output, "function: sound_scc_each_slice_element");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/deref_sound_1", VERIFY_CMD);
    assert_contain(&output, "function: sound_deref_slice_prefix");
    assert_contain(&output, "Deref | Proved");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn validptr_unsound_cases() {
    let output = run_with_args("verify_units/validptr_unsound_1", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_non_zst_dangling_not_allocated",
        &["ValidPtr"],
    );

    let output = run_with_args("verify_units/validptr_unsound_2", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_one_past_requires_one_element",
        &["ValidPtr"],
    );

    let output = run_with_args("verify_units/validptr_unsound_3", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_stack_array_len_too_large", &["ValidPtr"]);

    let output = run_with_args("verify_units/validptr_unsound_4", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_scc_branch_uses_one_past", &["ValidPtr"]);

    let output = run_with_args("verify_units/validptr_unsound_5", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "unsound_signed_suffix_missing_lower_bound",
        &["InBound"],
    );

    let output = run_with_args("verify_units/deref_unsound_1", VERIFY_CMD);
    assert_unproved_exclusive(&output, "unsound_deref_one_past", &["Deref"]);
}

#[test]
fn typed_provenance_cases() {
    let output = run_with_args("verify_units/typed_cases", VERIFY_CMD);

    assert_contain(&output, "function: sound_reference_source");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_slice_element_source");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_repr_c_field_source");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_generic_reference_source");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_branch_all_sources_typed");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_scc_preserves_typed_source");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_maybeuninit_after_write");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_align_to_same_type");
    assert_contain(&output, "result: SOUND");

    assert_unproved_exclusive(&output, "unsound_u8_bytes_as_u32", &["Typed"]);
    assert_unproved_exclusive(&output, "unsound_u16_slice_as_u32", &["Typed"]);
    assert_unproved_exclusive(&output, "unsound_uninit_memory_as_u32", &["Typed"]);
    assert_unproved_exclusive(&output, "unsound_invalid_bool_bits", &["Typed"]);
    assert_unproved_exclusive(&output, "unsound_invalid_char_bits", &["Typed"]);
    assert_unproved_exclusive(&output, "unsound_invalid_enum_discriminant", &["Typed"]);
    assert_unproved_exclusive(&output, "unsound_branch_selects_untyped_source", &["Typed"]);
    assert_unproved_exclusive(
        &output,
        "unsound_scc_overwrites_with_untyped_source",
        &["Typed"],
    );
}

#[test]
fn alive_sound_cases() {
    let output = run_with_args("verify_units/alive_sound_01", VERIFY_CMD);
    assert_contain(&output, "function: SliceHost::<'a, T>::get");
    assert_contain(&output, "Alive | Proved");

    let output = run_with_args("verify_units/alive_sound_02", VERIFY_CMD);
    assert_contain(&output, "function: MutSliceHost::<'a, T>::get_mut");
    assert_contain(&output, "Alive | Proved");

    let output = run_with_args("verify_units/alive_sound_03", VERIFY_CMD);
    assert_contain(&output, "function: slice_from_host");
    assert_contain(&output, "Alive | Proved");
}

#[test]
fn alive_unsound_cases() {
    let output = run_with_args("verify_units/alive_unsound_01", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "DangerousAliaser::<'a, T>::get_mut",
        &["Alive", "NonNull", "ValidPtr"],
    );

    let output = run_with_args("verify_units/alive_unsound_02", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "slice_tied_to_unrelated_host",
        &["Alias", "Alive", "Init", "NonNull", "ValidPtr"],
    );

    let output = run_with_args("verify_units/alive_unsound_03", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "static_slice_from_local_vec",
        &["Alias", "Align", "Alive", "Init", "NonNull", "ValidPtr"],
    );
}

#[test]
fn struct_invariant() {
    let output = run_with_args("verify_units/struct_invariant_1", VERIFY_CMD);
    // unsound_new: constructor with requires, all struct invariants proved
    assert_contain(&output, "function: Wrapper::<T>::unsound_new");
    assert_contain(&output, "Align | Proved");
    assert_contain(&output, "InBound | Proved");
    assert_contain(&output, "Init | Proved");
    // unsound_set_len: mutator with requires, struct invariants proved via self
    assert_contain(&output, "function: Wrapper::<T>::unsound_set_len");
    // sound_read: alignment proved via guard, but raw-ptr deref still unproved
    assert_contain(&output, "function: Wrapper::<T>::sound_read");
    // unsound_read: raw-ptr deref unproved, struct invariants hold via precond
    assert_contain(&output, "function: Wrapper::<T>::unsound_read");
}

#[test]
fn linked_list_nonnull() {
    let output = run_with_args("verify_cases/linked_list_nonnull", VERIFY_CMD);
    // from_vec: linked list with Option<NonNull<Node>>, invariants via unwrap_some
    assert_contain(&output, "function: LinkedList::from_vec");
    // struct invariants section present (Align via unwrap_some)
    assert_contain(&output, "struct invariants");
}

#[test]
fn linked_list_rawptr() {
    let output = run_with_args("verify_cases/linked_list_rawptr", VERIFY_CMD);
    // from_vec: linked list with *mut Node, invariants directly on raw pointers
    assert_contain(&output, "function: LinkedList::from_vec");
    // struct invariants present, NonNull and Align checked
    assert_contain(&output, "struct invariants");
    assert_contain(&output, "NonNull");
    assert_contain(&output, "Align");
}

#[test]
fn invless_skips_struct_invariant() {
    let output = run_with_args("verify_units/struct_invariant_1", VERIFY_INVLESS_CMD);
    // 4 sequences: 2 read methods × 2 options (direct, through set_len)
    assert_contain(&output, "sequence: unsound_new -> sound_read");
    assert_contain(
        &output,
        "sequence: unsound_new -> unsound_set_len -> sound_read",
    );
    assert_contain(&output, "sequence: unsound_new -> unsound_read");
    assert_contain(
        &output,
        "sequence: unsound_new -> unsound_set_len -> unsound_read",
    );
    // All UNSOUND: ValidPtr/Typed unimplemented
    assert_contain(&output, "result: UNSOUND");
    assert_not_contain(&output, "result: SOUND");
    // sound_read Align proved via guard; unsound_read Align Unknown
    assert_contain(&output, "Align | Proved");
    assert_contain(&output, "Align | Unknown");
    assert_not_contain(&output, "function: Wrapper::<T>::unsound_new");
    assert_not_contain(&output, "function: Wrapper::<T>::unsound_set_len");
    assert_not_contain(&output, "struct-invariant");
}

#[test]
fn invless_no_annotations() {
    let output = run_with_args("verify_units/invless_1", VERIFY_INVLESS_CMD);
    // 4 sequences generated
    assert_contain(&output, "sequence: unsound_new -> sound_read");
    assert_contain(
        &output,
        "sequence: unsound_new -> unsound_set_len -> sound_read",
    );
    assert_contain(&output, "sequence: unsound_new -> unsound_read");
    assert_contain(
        &output,
        "sequence: unsound_new -> unsound_set_len -> unsound_read",
    );
    // sound_read: Align Proved (internal guard), ValidPtr/Typed Unknown → UNSOUND(2)
    // set_len→sound_read: same
    // unsound_read: Align Unknown (no contracts), ValidPtr/Typed Unknown → UNSOUND(3)
    // set_len→unsound_read: same
    assert_contain(&output, "result: UNSOUND");
    assert_not_contain(&output, "result: SOUND");
    assert_contain(&output, "Align | Proved");
    assert_contain(&output, "Align | Unknown");
    assert_not_contain(&output, "struct-invariant");
}

#[test]
fn invless_with_contracts() {
    let output = run_with_args("verify_units/invless_2", VERIFY_INVLESS_CMD);
    // 4 sequences generated
    assert_contain(&output, "sequence: unsound_new -> sound_read");
    assert_contain(
        &output,
        "sequence: unsound_new -> unsound_set_len -> sound_read",
    );
    assert_contain(&output, "sequence: unsound_new -> unsound_read");
    assert_contain(
        &output,
        "sequence: unsound_new -> unsound_set_len -> unsound_read",
    );
    // sound_read: Align Proved (guard), ValidPtr/Typed Unknown → UNSOUND(2)
    // set_len→sound_read: Align Proved (guard; set_len mutates len but Align depends only on ptr)
    // unsound_read: Align Unknown (contract Align(self.ptr, u32) not connected to casted ptr via SMT)
    // set_len→unsound_read: Align Unknown (same; set_len mutates len, Align not invalidated)
    assert_contain(&output, "result: UNSOUND");
    assert_not_contain(&output, "result: SOUND");
    assert_contain(&output, "Align | Proved");
    assert_contain(&output, "Align | Unknown");
    assert_contain(&output, "ValidPtr | Unknown");
    assert_contain(&output, "Typed | Unknown");
    assert_not_contain(&output, "struct-invariant");
}

#[test]
fn invless_sound_callee() {
    let output = run_with_args("verify_units/align_sound_1", VERIFY_INVLESS_CMD);
    assert_contain(&output, "function: sound_named_contract_binds_callsite_arg");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn safetyflow_safe_caller() {
    let output = run_with_args("analyze/safetyflow_safe_caller", ANALYZE_SAFETYFLOW_CMD);
    assert_contain(&output, "from_raw_parts");
}

#[test]
fn safetyflow_raw_ptr() {
    let output = run_with_args("analyze/safetyflow_raw_ptr", ANALYZE_SAFETYFLOW_CMD);
    assert_contain(&output, "*raw* ptr deref");
}

#[test]
fn safetyflow_static_mut() {
    let output = run_with_args("analyze/safetyflow_static_mut", ANALYZE_SAFETYFLOW_CMD);
    assert_contain(&output, "COUNTER");
}

#[test]
fn scan_raw_ptr_deref() {
    let output = run_with_args("analyze/safetyflow_raw_ptr", VERIFY_SCAN_CMD);
    assert_contain(&output, "[rapx::verify] function: main");
    assert_contain(&output, "ValidPtr | Proved");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn scan_static_mut() {
    let output = run_with_args("analyze/safetyflow_static_mut", VERIFY_SCAN_CMD);
    assert_contain(&output, "[rapx::verify] function: main");
    assert_contain(&output, "Unknown");
    assert_contain(&output, "UNSOUND");
}

#[test]
fn std_challenge_17() {
    let output = run_with_args("verify_cases/std-challenge-17", VERIFY_TARGETED_CMD);

    let functions = [
        "<[T] as SliceExt<T>>::get_unchecked_ext",
        "<[T] as SliceExt<T>>::get_unchecked_mut_ext",
        "<[T] as SliceExt<T>>::split_at_unchecked_ext",
        "<[T] as SliceExt<T>>::split_at_mut_unchecked_ext",
        "<[T] as SliceExt<T>>::swap_unchecked_ext",
        "<[T] as SliceExt<T>>::as_chunks_unchecked_ext",
        "<[T] as SliceExt<T>>::as_chunks_unchecked_mut_ext",
        "<[T] as SliceExt<T>>::align_to_ext",
        "<[T] as SliceExt<T>>::align_to_mut_ext",
        "<[T] as SliceExt<T>>::get_disjoint_unchecked_mut_ext",
        "<[T] as SliceSafeExt<T>>::first_chunk_ext",
        "<[T] as SliceSafeExt<T>>::first_chunk_mut_ext",
        "<[T] as SliceSafeExt<T>>::split_first_chunk_ext",
        "<[T] as SliceSafeExt<T>>::split_first_chunk_mut_ext",
        "<[T] as SliceSafeExt<T>>::split_last_chunk_ext",
        "<[T] as SliceSafeExt<T>>::split_last_chunk_mut_ext",
        "<[T] as SliceSafeExt<T>>::last_chunk_ext",
        "<[T] as SliceSafeExt<T>>::last_chunk_mut_ext",
        "<[T] as SliceSafeExt<T>>::as_chunks_ext",
        "<[T] as SliceSafeExt<T>>::as_chunks_mut_ext",
        "<[T] as SliceSafeExt<T>>::as_rchunks_ext",
        "<[T] as SliceSafeExt<T>>::split_at_checked_ext",
        "<[T] as SliceSafeExt<T>>::split_at_mut_checked_ext",
        "<[T] as SliceSafeExt<T>>::reverse_ext",
        "<[T] as SliceSafeExt<T>>::rotate_left_ext",
        "<[T] as SliceSafeExt<T>>::rotate_right_ext",
        "<[T] as SliceSafeExt<T>>::copy_from_slice_ext",
        "<[T] as SliceSafeExt<T>>::copy_within_ext",
        "<[T] as SliceSafeExt<T>>::swap_with_slice_ext",
        "<[T] as SliceSafeExt<T>>::binary_search_by_ext",
        "<[T] as SliceSafeExt<T>>::partition_dedup_by_ext",
        "<[T] as SliceSafeExt<T>>::get_disjoint_mut_ext",
        "<[T] as SliceSimdExt<T>>::as_simd_ext",
        "<[T] as SliceSimdExt<T>>::as_simd_mut_ext",
        "<[[T; N]] as SliceArrayExt<T, N>>::as_flattened_ext",
        "<[[T; N]] as SliceArrayExt<T, N>>::as_flattened_mut_ext",
        "get_disjoint_check_valid_ext",
    ];

    for fn_name in &functions {
        assert_contain(&output, fn_name);
    }

    assert_eq!(
        output.matches("result: SOUND").count(),
        37,
        "expected 37 SOUND results"
    );
}

#[test]
fn transmute_align_unsound() {
    let output = run_with_args("verify_units/transmute_without_align_unsound", VERIFY_CMD);
    assert_unproved_exclusive(
        &output,
        "align_without_contract_generic",
        &["TransmuteWithoutAlign"],
    );
    assert_unproved_exclusive(
        &output,
        "unsound_align_to_bool_from_bytes",
        &["TransmuteWithoutAlign"],
    );
    assert_contain(&output, "function: align_without_contract_u32");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: align_without_contract_u16");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: align_without_contract_u8");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn transmute_align_nonzero() {
    let output = run_with_args("verify_units/transmute_without_align_nonzero", VERIFY_CMD);
    assert_contain(&output, "function: align_to_nonzero_u16");
    assert_contain(&output, "result: UNSOUND");
    assert_contain(&output, "function: align_to_nonzero_u32");
    assert_contain(&output, "result: UNSOUND");
    assert_contain(&output, "function: align_to_nonzero_u8");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn transmute_align_sound() {
    let output = run_with_args("verify_units/transmute_without_align_sound", VERIFY_CMD);
    assert_contain(&output, "function: align_to_u8_sound");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn trait_unsound_prepare() {
    let output = run_with_args("verify_units/trait_unsound_1", VERIFY_PREPARE_CMD);
    assert_contain(&output, "prepare targets for unsafe trait: Buffer");
    assert_contain(&output, "impl for: VecBuf");
    assert_contain(&output, "ensures");
    assert_contain(&output, "ValidSlice");
}

#[test]
fn trait_unsound_verify() {
    let output = run_with_args("verify_units/trait_unsound_1", VERIFY_CMD);
    assert_contain(&output, "unsafe trait impl: Buffer");
    assert_contain(&output, "impl for: VecBuf");
    assert_contain(&output, "ensures");
    assert_contain(&output, "ValidSlice");
    assert_contain(&output, "verification: deferred");
}

#[test]
fn ssa_transform() {
    let output = run_with_args("analyze/ssa_transform", ANALYZE_SSA_CMD);
    assert_contain(&output, "ssa lvalue check true");
}
#[test]
fn range_analysis() {
    let output = run_with_args("analyze/range_1", ANALYZE_RANGE_CMD);

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
    let output = run_with_args("analyze/range_2", ANALYZE_RANGE_CMD);

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
    let output = run_with_args("analyze/callgraph_dynamic", ANALYZE_CALLGRAPH_CMD);

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
    let output = run_with_args("analyze/range_symbolic", ANALYZE_RANGE_CMD);

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
    let _ = run_with_args("analyze/adg_bug_regression", ANALYZE_ADG_CMD);
}

#[test]
fn adg_simple_graph() {
    let _ = run_with_args("analyze/adg_simple_graph", ANALYZE_ADG_CMD);
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

// ================ Alias Verify Sound Cases =============
#[test]
fn alias_verify_sound() {
    let output = run_with_args("verify_units/alias_sound_13", VERIFY_CMD);
    assert_contain(&output, "function: as_bytes_mut_sound");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/alias_sound_14", VERIFY_CMD);
    assert_contain(&output, "function: as_bytes_sound");
    assert_contain(&output, "result: SOUND");
}

// ================ Alias Verify Unsound Cases =============
#[test]
fn alias_verify_unsound() {
    let output = run_with_args("verify_units/alias_unsound_18", VERIFY_CMD);
    assert_unproved_exclusive(&output, "as_bytes_mut_unsound", &["Alias"]);

    let output = run_with_args("verify_units/alias_unsound_19", VERIFY_CMD);
    assert_unproved_exclusive(&output, "as_bytes_mut_ptr_missing_alias", &["Alias"]);

    let output = run_with_args("verify_units/alias_unsound_20", VERIFY_CMD);
    assert_unproved_exclusive(&output, "as_bytes_mut_ptr_len_missing_alias", &["Alias"]);
}

#[test]
fn filter_by_module() {
    let output = run_with_args(
        "verify_units/module_filter",
        &["verify", "--mode", "targeted", "--module", "a"],
    );
    assert_contain(&output, "function: a::f");
    assert_not_contain(&output, "function: b::g");
    assert_not_contain(&output, "function: c::h");

    let output = run_with_args(
        "verify_units/module_filter",
        &["verify", "--mode", "scan", "--module", "b"],
    );
    assert_contain(&output, "function: b::g");
    assert_not_contain(&output, "function: a::f");
    assert_not_contain(&output, "function: c::h");
}

#[test]
fn filter_by_crate() {
    let output = run_with_args(
        "verify_units/module_filter",
        &[
            "verify",
            "--mode",
            "targeted",
            "--crate",
            "verify_module_filter",
        ],
    );
    assert_contain(&output, "function: a::f");
    assert_contain(&output, "function: b::g");
    assert_contain(&output, "function: c::h");

    let output = run_with_args(
        "verify_units/module_filter",
        &[
            "verify",
            "--mode",
            "targeted",
            "--crate",
            "verify_module_filter",
            "--module",
            "a",
        ],
    );
    assert_contain(&output, "function: a::f");
    assert_not_contain(&output, "function: b::g");
    assert_not_contain(&output, "function: c::h");

    let output = run_with_args(
        "verify_units/module_filter",
        &[
            "verify",
            "--mode",
            "targeted",
            "--crate",
            "nonexistent_crate",
        ],
    );
    assert_contain(&output, "--crate \"nonexistent_crate\" matched no targets");
}

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
