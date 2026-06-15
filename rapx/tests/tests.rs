#![allow(clippy::bool_assert_comparison)]
use fs4::fs_std::FileExt;
use insta::assert_snapshot;
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

#[inline(always)]
fn project_path(dir: &str) -> PathBuf {
    Path::new("tests").join(dir)
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

const CHECK_UAF_CMD: &[&str] = &["check", "-f"];
const CHECK_MLEAK_CMD: &[&str] = &["check", "-m"];
const ANALYZE_ALIAS_CMD: &[&str] = &["analyze", "alias"];
const ANALYZE_ALIAS_MFP_CMD: &[&str] = &["analyze", "alias", "--strategy", "mfp"];
const ANALYZE_OWNED_HEAP_CMD: &[&str] = &["analyze", "owned-heap"];
const ANALYZE_PATHS_CMD: &[&str] = &["analyze", "paths"];
const ANALYZE_UPG_CMD: &[&str] = &["analyze", "upg"];
const ANALYZE_SSA_CMD: &[&str] = &["analyze", "ssa"];
const ANALYZE_RANGE_CMD: &[&str] = &["analyze", "range"];
const ANALYZE_CALLGRAPH_CMD: &[&str] = &["analyze", "callgraph"];
const ANALYZE_ADG_CMD: &[&str] = &["analyze", "adg", "--dump", "api_graph.yml"];
const VERIFY_CMD: &[&str] = &["verify"];
const VERIFY_ALLOW_REPEAT_CMD: &[&str] = &["verify", "--allow-pathseg-repeat", "1"];
const VERIFY_ALLOW_REPEAT2_CMD: &[&str] = &["verify", "--allow-pathseg-repeat", "2"];

// ================Dangling Pointer Detection Test=====================
#[test]
fn uaf_01() {
    let output = run_with_args("uaf/uaf_01", CHECK_UAF_CMD);
    assert_contain(
        &output,
        "Dangling pointer detected in function \"create_vec\"",
    );
}

#[test]
fn uaf_02() {
    let output = run_with_args("uaf/uaf_02", CHECK_UAF_CMD);
    assert_contain(&output, "Double free detected in function \"main\"");
}

#[test]
fn uaf_03() {
    let output = run_with_args("uaf/uaf_03", CHECK_UAF_CMD);
    assert_contain(&output, "Double free detected");
}

/*
#[test]
fn uaf_04() {
    let output = run_with_args("uaf/uaf_04", CHECK_UAF_CMD);
    assert_contain(&output, "Dangling pointer detected in function \"call\"");
}
*/

#[test]
fn uaf_05() {
    let output = run_with_args("uaf/uaf_05", CHECK_UAF_CMD);
    assert_contain(&output, "Use-after-free detected in function \"main\"");
}

#[test]
fn uaf_06() {
    let output = run_with_args("uaf/uaf_06", CHECK_UAF_CMD);
    assert_contain(&output, "Use-after-free detected in function \"main\"");
}

#[test]
fn uaf_07() {
    let output = run_with_args("uaf/uaf_07", CHECK_UAF_CMD);
    assert_contain(&output, "Double free detected in function \"main\"");
}

#[test]
fn uaf_08() {
    let output = run_with_args("uaf/uaf_08", CHECK_UAF_CMD);
    assert_contain(&output, "Use-after-free detected in function \"main\"");
}

#[test]
fn uaf_09() {
    let output = run_with_args("uaf/uaf_09", CHECK_UAF_CMD);
    assert_contain(&output, "Use-after-free detected in function \"main\"");
}

#[test]
fn uaf_10() {
    let output = run_with_args("uaf/uaf_10", CHECK_UAF_CMD);
    assert_contain(&output, "Double free detected in function \"evil_test\"");
}

#[test]
fn uaf_false_01() {
    let output = run_with_args("uaf/uaf_false_01", CHECK_UAF_CMD);
    assert!(
        !detected_high_confidence(&output),
        "Unexpected high-confidence bug in output:\n{}",
        output
    );
}

#[test]
fn uaf_false_02() {
    let output = run_with_args("uaf/uaf_false_02", CHECK_UAF_CMD);
    assert_not_contain(&output, "detected");
}

#[test]
fn uaf_false_03() {
    let output = run_with_args("uaf/uaf_false_03", CHECK_UAF_CMD);
    assert!(
        !detected_high_confidence(&output),
        "Unexpected high-confidence bug in output:\n{}",
        output
    );
}

#[test]
fn uaf_false_04() {
    let output = run_with_args("uaf/uaf_false_04", CHECK_UAF_CMD);
    assert_not_contain(&output, "detected");
}

#[test]
fn uaf_false_05() {
    #[allow(unused)]
    let output = run_with_args("uaf/uaf_false_05", CHECK_UAF_CMD);
    assert_not_contain(&output, "detected");
}

#[test]
fn uaf_false_06() {
    #[allow(unused)]
    let output = run_with_args("uaf/uaf_false_06", CHECK_UAF_CMD);
    assert!(
        !detected_high_confidence(&output),
        "Unexpected high-confidence bug in output:\n{}",
        output
    );
}

#[test]
fn uaf_false_08() {
    #[allow(unused)]
    let output = run_with_args("uaf/uaf_false_08", CHECK_UAF_CMD);
    assert_not_contain(&output, "detected");
}

#[test]
fn uaf_false_09() {
    #[allow(unused)]
    let output = run_with_args("uaf/uaf_false_09", CHECK_UAF_CMD);
    assert_not_contain(&output, "detected");
}

#[test]
fn uaf_false_10() {
    #[allow(unused)]
    let output = run_with_args("uaf/uaf_false_10", CHECK_UAF_CMD);
    assert_not_contain(&output, "detected");
}

#[test]
fn uaf_false_11() {
    #[allow(unused)]
    let output = run_with_args("uaf/uaf_false_11", CHECK_UAF_CMD);
    assert_not_contain(&output, "detected");
}

// ===============Alias(MOP) Analysis Test==============
#[test]
fn alias_01() {
    let output = run_with_args("alias/alias_01", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "foo\": (0.0,1)");
}

#[test]
fn alias_02() {
    let output = run_with_args("alias/alias_02", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "foo\": (0,1)");
}

#[test]
fn alias_03() {
    let output = run_with_args("alias/alias_03", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "foo\": null");
}

#[test]
fn alias_04() {
    let output = run_with_args("alias/alias_04", ANALYZE_ALIAS_CMD);
    let has_either = output.contains("\"foo\": (0,1.1), (0,1.0)")
        || output.contains("\"foo\": (0,1.0), (0,1.1)");
    assert!(
        has_either,
        "Missing alias field variations\nFull output:\n{}",
        output
    );
}

#[test]
fn alias_05() {
    let output = run_with_args("alias/alias_05", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "new\": (0.0,1.0)");
}

#[test]
fn alias_06() {
    let output = run_with_args("alias/alias_06", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "foo\": (0,1)");
}

#[test]
fn alias_07() {
    let output = run_with_args("alias/alias_07", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "foo\": (0,1)");
}

#[test]
fn alias_08() {
    let output = run_with_args("alias/alias_08", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "foo\": (0,1), (0,2)");
}

#[test]
fn alias_09() {
    let output = run_with_args("alias/alias_09", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "foo\": (0,1)");
}

#[test]
fn alias_10() {
    let output = run_with_args("alias/alias_10", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "new\": (0.0,1.0)");
}

#[test]
fn alias_11() {
    let output = run_with_args("alias/alias_11", ANALYZE_ALIAS_CMD);
    assert_contain(&output, "iter_prop\": (0.0,1.0)");
}

// ===============Alias(MFP) Analysis Test==============
#[test]
fn alias_01_mfp() {
    let output = run_with_args("alias/alias_01", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "foo\": (0.0,1)");
}

#[test]
fn alias_02_mfp() {
    let output = run_with_args("alias/alias_02", ANALYZE_ALIAS_MFP_CMD);
    // MOP expects "foo": (0,1) but MFP reports a slightly different format.
    assert_contain(&output, "foo\": (0.0,1)"); // This is slightly different from MOP
}

#[test]
fn alias_03_mfp() {
    let output = run_with_args("alias/alias_03", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "foo\": null");
}

#[test]
fn alias_04_mfp() {
    let output = run_with_args("alias/alias_04", ANALYZE_ALIAS_MFP_CMD);
    let has_either = output.contains("\"foo\": (0,1.1), (0,1.0)")
        || output.contains("\"foo\": (0,1.0), (0,1.1)");
    assert!(
        has_either,
        "Missing alias field variations\nFull output:\n{}",
        output
    );
}

#[test]
fn alias_05_mfp() {
    let output = run_with_args("alias/alias_05", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "new\": (0.0,1.0)");
}

#[test]
fn alias_06_mfp() {
    let output = run_with_args("alias/alias_06", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "foo\": (0,1)");
}

#[test]
fn alias_07_mfp() {
    let output = run_with_args("alias/alias_07", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "foo\": (0,1)");
}

#[test]
fn alias_08_mfp() {
    let output = run_with_args("alias/alias_08", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "foo\": (0,1), (0,2)");
}

#[test]
fn alias_09_mfp() {
    let output = run_with_args("alias/alias_09", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "foo\": (0,1)");
}

#[test]
fn alias_10_mfp() {
    let output = run_with_args("alias/alias_10", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "new\": (0.0,1.0)");
}

#[test]
fn alias_11_mfp() {
    let output = run_with_args("alias/alias_11", ANALYZE_ALIAS_MFP_CMD);
    assert_contain(&output, "iter_prop\": (0.0,1.0)");
}

#[test]
fn leak_01() {
    let output = run_with_args("leak/leak_01", CHECK_MLEAK_CMD);
    assert_not_contain(&output, "Memory Leak detected in function main");
}

#[test]
fn leak_02() {
    let output = run_with_args("leak/leak_02", CHECK_MLEAK_CMD);
    assert_contain(&output, "Memory Leak detected in function main");
}

#[test]
fn leak_02_timeout() {
    let mut args = Vec::from(["--timeout", "0"]);
    args.extend(CHECK_MLEAK_CMD);
    let output = run_with_args("leak/leak_02", &args);
    assert!(output.contains("Process killed due to timeout"));
}

#[test]
fn leak_03() {
    let output = run_with_args("leak/leak_03", CHECK_MLEAK_CMD);
    assert_contain(&output, "Memory Leak detected in function main");
}

#[test]
fn heap_cell() {
    let output = run_with_args("ownedheap/heap_cell", ANALYZE_OWNED_HEAP_CMD);
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
}

#[test]
fn heap_collections() {
    let output = run_with_args("ownedheap/heap_collections", ANALYZE_OWNED_HEAP_CMD);
    for pattern in [
        "Unique\": True, <0>",
        "Box\": True, <0,1>",
        "Vec\": True, <0,1>",
        "String\": True, <>",
        "LinkedList\": True, <1,1>",
        "HashMap\": True, <0,0,1>",
        "BTreeMap\": True, <0,0,1>",
        "HashSet\": True, <0,1>",
        "BTreeSet\": True, <0,1>",
    ] {
        assert_contain(&output, pattern);
    }
}

#[test]
fn heap_nested() {
    let output: String = run_with_args("ownedheap/heap_nested", ANALYZE_OWNED_HEAP_CMD);
    for pattern in [
        "X\": False, <1>",
        "Y\": False, <1>",
        "Example\": True, <1,1,0,1>",
    ] {
        assert_contain(&output, pattern);
    }
}

#[test]
fn heap_proxy() {
    let output = run_with_args("ownedheap/heap_proxy", ANALYZE_OWNED_HEAP_CMD);
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
fn if_else() {
    let output = run_with_args("verify/path/if-else", ANALYZE_PATHS_CMD);
    assert_contain(&output, "Function: \"read1\":");
    assert_contain(&output, "Function: \"read2\":");
    assert_contain(&output, "Path [");
}

#[test]
fn align_sound_01() {
    let output = run_with_args("verify/align_sound_01", VERIFY_CMD);
    assert_contain(&output, "function: sound_named_contract_binds_callsite_arg");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_sound_02() {
    let output = run_with_args("verify/align_sound_02", VERIFY_CMD);
    assert_contain(&output, "function: sound_enum_paths_inside_scc");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_unsound_01() {
    let output = run_with_args("verify/align_unsound_01", VERIFY_CMD);
    assert_contain(&output, "function: unsound_enum_paths_inside_scc");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_sound_03() {
    let output = run_with_args("verify/align_sound_03", VERIFY_CMD);
    assert_contain(&output, "function: sound_scc_selects_aligned_source");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_unsound_02() {
    let output = run_with_args("verify/align_unsound_02", VERIFY_CMD);
    assert_contain(&output, "function: unsound_scc_selects_mixed_source");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_sound_04() {
    let output = run_with_args("verify/align_sound_04", VERIFY_CMD);
    assert_contain(&output, "function: sound_scc_computes_aligned_offset");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_unsound_03() {
    let output = run_with_args("verify/align_unsound_03", VERIFY_CMD);
    assert_contain(&output, "function: unsound_scc_computes_misaligned_offset");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_sound_05() {
    let output = run_with_args("verify/align_sound_05", VERIFY_CMD);
    assert_contain(&output, "function: sound_nested_scc_controller");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_unsound_04() {
    let output = run_with_args("verify/align_unsound_04", VERIFY_ALLOW_REPEAT_CMD);
    assert_contain(&output, "function: unsound_nested_scc_controller");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_sound_06() {
    let output = run_with_args("verify/align_sound_06", VERIFY_CMD);
    assert_contain(
        &output,
        "function: sound_iteration_count_switches_aligned_offsets",
    );
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_unsound_05() {
    let output = run_with_args("verify/align_unsound_05", VERIFY_CMD);
    assert_contain(
        &output,
        "function: unsound_iteration_count_can_leave_unaligned",
    );
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_sound_07() {
    let output = run_with_args("verify/align_sound_07", VERIFY_CMD);
    assert_contain(
        &output,
        "function: sound_unrelated_scc_does_not_pollute_align",
    );
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_sound_08() {
    let output = run_with_args("verify/align_sound_08", VERIFY_CMD);
    assert_contain(
        &output,
        "function: sound_unrelated_nested_scc_with_bad_scratch",
    );
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_sound_09() {
    let output = run_with_args("verify/align_sound_09", VERIFY_CMD);
    assert_contain(&output, "function: sound_pre_scc_guard_with_scc_offsets");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_unsound_06() {
    let output = run_with_args("verify/align_unsound_06", VERIFY_CMD);
    assert_contain(
        &output,
        "function: unsound_pre_scc_guard_overwritten_by_scc",
    );
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_sound_10() {
    let output = run_with_args("verify/align_sound_10", VERIFY_CMD);
    assert_contain(&output, "function: sound_scc_internal_noise_ignored");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_unsound_07() {
    let output = run_with_args("verify/align_unsound_07", VERIFY_CMD);
    assert_contain(&output, "function: unsound_scc_guard_only_on_one_branch");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_sound_11() {
    let output = run_with_args("verify/align_sound_11", VERIFY_CMD);
    assert_contain(&output, "function: sound_helper_with_conjunctive_guard");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_unsound_08() {
    let output = run_with_args("verify/align_unsound_08", VERIFY_CMD);
    assert_contain(&output, "function: unsound_helper_with_disjunctive_guard");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_sound_12() {
    let output = run_with_args("verify/align_sound_12", VERIFY_CMD);
    assert_contain(&output, "function: sound_nested_if_before_helper");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_unsound_09() {
    let output = run_with_args("verify/align_unsound_09", VERIFY_CMD);
    assert_contain(
        &output,
        "function: unsound_helper_return_path_selects_bad_ptr",
    );
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_sound_13() {
    let output = run_with_args("verify/align_sound_13", VERIFY_CMD);
    assert_contain(&output, "function: sound_helper_return_paths_all_aligned");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_sound_14() {
    let output = run_with_args("verify/align_sound_14", VERIFY_CMD);
    assert_contain(&output, "function: sound_multi_hop_helper");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_unsound_10() {
    let output = run_with_args("verify/align_unsound_10", VERIFY_CMD);
    assert_contain(&output, "function: unsound_multi_hop_missing_offset_guard");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_sound_15() {
    let output = run_with_args("verify/align_sound_15", VERIFY_CMD);
    assert_contain(&output, "function: sound_unrelated_condition_ignored");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_sound_16() {
    let output = run_with_args("verify/align_sound_16", VERIFY_CMD);
    assert_contain(&output, "function: sound_add_sub_chain");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_unsound_11() {
    let output = run_with_args("verify/align_unsound_11", VERIFY_CMD);
    assert_contain(&output, "function: unsound_sub_missing_guard");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_sound_17() {
    let output = run_with_args("verify/align_sound_17", VERIFY_CMD);
    assert_contain(&output, "function: sound_offset_zero_preserves_align");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_unsound_12() {
    let output = run_with_args("verify/align_unsound_12", VERIFY_CMD);
    assert_contain(&output, "function: unsound_byte_offset_one");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_sound_18() {
    let output = run_with_args("verify/align_sound_18", VERIFY_CMD);
    assert_contain(&output, "function: sound_usize_round_trip");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_sound_19() {
    let output = run_with_args("verify/align_sound_19", VERIFY_CMD);
    assert_contain(&output, "function: sound_usize_add_guarded");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_unsound_13() {
    let output = run_with_args("verify/align_unsound_13", VERIFY_CMD);
    assert_contain(&output, "function: unsound_usize_add_missing_offset_guard");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_sound_20() {
    let output = run_with_args("verify/align_sound_20", VERIFY_CMD);
    assert_contain(&output, "function: sound_usize_mul_div_offset");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_sound_21() {
    let output = run_with_args("verify/align_sound_21", VERIFY_CMD);
    assert_contain(&output, "function: sound_repr_c_field");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_sound_22() {
    let output = run_with_args("verify/align_sound_22", VERIFY_CMD);
    assert_contain(&output, "function: sound_repr_align_object");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_unsound_14() {
    let output = run_with_args("verify/align_unsound_14", VERIFY_CMD);
    assert_contain(&output, "function: unsound_repr_packed_field");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_sound_23() {
    let output = run_with_args("verify/align_sound_23", VERIFY_CMD);
    assert_contain(&output, "function: sound_zst_trivial_alignment");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_unsound_15() {
    let output = run_with_args("verify/align_unsound_15", VERIFY_CMD);
    assert_contain(&output, "function: unsound_four_phase_scc_alignment");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_unsound_16() {
    let output = run_with_args("verify/align_unsound_16", VERIFY_CMD);
    assert_contain(&output, "function: unsound_trait_bound_cross_cast");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_sound_24() {
    let output = run_with_args("verify/align_sound_24", VERIFY_CMD);
    assert_contain(&output, "function: sound_trait_bound_cross_cast");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_sound_25() {
    let output = run_with_args("verify/align_sound_25", VERIFY_CMD);
    assert_contain(
        &output,
        "function: sound_contract_type_param_binds_concrete",
    );
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_sound_26() {
    let output = run_with_args("verify/align_sound_26", VERIFY_CMD);
    assert_contain(&output, "function: sound_contract_type_param_binds_generic");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_unsound_17() {
    let output = run_with_args("verify/align_unsound_17", VERIFY_CMD);
    assert_contain(
        &output,
        "function: unsound_contract_type_param_binds_generic",
    );
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn align_repeat_threshold_repeat1_sound() {
    let output = run_with_args("verify/align_repeat_threshold", VERIFY_ALLOW_REPEAT_CMD);
    assert_contain(&output, "function: repeat2_reveals_delayed_unaligned");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn align_repeat_threshold_repeat2_unsound() {
    let output = run_with_args("verify/align_repeat_threshold", VERIFY_ALLOW_REPEAT2_CMD);
    assert_contain(&output, "function: repeat2_reveals_delayed_unaligned");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn struct_invariant_1() {
    let output = run_with_args("verify/struct_invariant_1", VERIFY_CMD);
    assert_contain(&output, "function: Wrapper::<T>::unsound_new");
    assert_contain(&output, "result: UNSOUND");
    assert_contain(&output, "function: Wrapper::<T>::unsound_set_len");
    assert_contain(&output, "function: Wrapper::<T>::sound_read");
    assert_contain(&output, "function: Wrapper::<T>::unsound_read");
    // Alignment is proved in sound_read via the guard
    assert_contain(&output, "Align | Proved");
}

#[test]
fn upg_safe_caller() {
    let output = run_with_args("upg/safe_caller", ANALYZE_UPG_CMD);
    assert_contain(&output, "from_raw_parts");
}

#[test]
fn upg_raw_ptr() {
    let output = run_with_args("upg/raw_ptr", ANALYZE_UPG_CMD);
    assert_contain(&output, "raw_ptr_deref_dummy");
}

#[test]
fn upg_static_mut() {
    let output = run_with_args("upg/static_mut", ANALYZE_UPG_CMD);
    assert_contain(&output, "COUNTER");
}

#[test]
fn ssa_transform() {
    let output = run_with_args("ssa/ssa_transform", ANALYZE_SSA_CMD);
    assert_contain(&output, "ssa lvalue check true");
}
#[test]
fn range_analysis() {
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

fn interprocedual_range_analysis() {
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
fn callgraph_dynamic_dispatch() {
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
fn symbolic_interval() {
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

#[test]
fn adg_bug() {
    // This test pass if don't panic (e.g., stack overflow) during ADG construction and resolution.
    let _ = run_with_args("adg/bug-regression", ANALYZE_ADG_CMD);
}

#[test]
fn adg_simple_graph() {
    let _ = run_with_args("adg/simple-graph", ANALYZE_ADG_CMD);
    let graph_str = std::fs::read_to_string(project_path("adg/simple-graph").join("api_graph.yml"))
        .expect("read api_graph.yml fail");
    assert_snapshot!(graph_str);
}
