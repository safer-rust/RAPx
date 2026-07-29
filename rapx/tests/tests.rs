#![allow(clippy::bool_assert_comparison)]
use fs4::fs_std::FileExt;
use std::ffi::OsString;
use std::fs::File;
use std::path::{Path, PathBuf};
use std::process::Command;

fn project_path(dir: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join(dir)
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

struct LockGuard {
    file: std::fs::File,
    path: PathBuf,
}

impl LockGuard {
    fn new(path: PathBuf) -> Self {
        let file = File::create(&path).expect("Failed to create lock file");
        file.lock_exclusive().expect("Failed to acquire lock");
        Self { file, path }
    }
}

impl Drop for LockGuard {
    fn drop(&mut self) {
        let _ = self.file.unlock();
        let _ = std::fs::remove_file(&self.path);
    }
}

#[inline(always)]
fn run_with_args(dir: &str, args: &[&str]) -> String {
    let project_path = project_path(dir);
    let _lock = LockGuard::new(project_path.join(".rapx-test.lock"));

    let mut command = cargo_rapx_command();
    let output = command
        .args(args)
        .current_dir(&project_path)
        .output()
        .expect("Failed to execute cargo rapx");

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
    assert_unproved_exclusive_with_result(output, function, allowed, "UNSOUND");
}

fn assert_function_result(output: &str, function: &str, result_pat: &str) {
    assert_contain(output, &format!("function: {function}"));
    let block = extract_block_after(output, &format!("function: {function}"));
    assert!(
        block.contains(&format!("result: {result_pat}")),
        "Expected result: {result_pat} for {function}\nBlock:\n{block}"
    );
}

/// Like assert_unproved_exclusive but expects a different result string (e.g. "HAZARD").
fn assert_unproved_exclusive_with_result(
    output: &str,
    function: &str,
    allowed: &[&str],
    result_pat: &str,
) {
    assert_contain(output, &format!("function: {function}"));
    let block = extract_block_after(output, &format!("function: {function}"));

    // At least the primary (first) property must appear as Failed/Unknown.
    // Hazard properties are printed with a [hazard] prefix; match either form.
    if let Some(primary) = allowed.first() {
        let matches_plain = block.contains(&format!("{primary} | Failed"))
            || block.contains(&format!("{primary} | Unknown"));
        let matches_hazard = block.contains(&format!("[hazard] {primary} | Failed"))
            || block.contains(&format!("[hazard] {primary} | Unknown"));
        let matches_option = block.contains(&format!("[option] {primary} | Failed"))
            || block.contains(&format!("[option] {primary} | Unknown"));
        assert!(
            matches_plain || matches_hazard || matches_option,
            "Expected {primary} | Failed/Unknown for {function}\nBlock:\n{block}"
        );
    }

    // No property outside the allowed set may appear as Failed/Unknown.
    let mut actual: Vec<&str> = Vec::new();
    for line in block.lines() {
        for sfx in ["| Failed", "| Unknown"] {
            let Some(idx) = line.find(sfx) else { continue };
            // Skip [option] and [hazard] lines — they don't count as unproved preconditions.
            let prefix = line[..idx].trim_end();
            if prefix.contains("[hazard]") || prefix.contains("[option]") {
                continue;
            }
            let prop = prefix.rsplit(' ').next().unwrap_or("");
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
    assert_contain(output, &format!("result: {result_pat}"));
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

const CMD_CHECK_UAF: &[&str] = &["check", "-f"];
const CMD_CHECK_MEMLEAK: &[&str] = &["check", "-m"];
const CMD_ANALYZE_ALIAS: &[&str] = &["analyze", "alias"];
const CMD_ANALYZE_ALIAS_MFP: &[&str] = &["analyze", "alias", "--strategy", "mfp"];
const CMD_ANALYZE_OWNEDHEAP: &[&str] = &["analyze", "ownedheap"];
const CMD_ANALYZE_PATHS: &[&str] = &["analyze", "paths"];
const CMD_ANALYZE_PATHS_REPEAT_1: &[&str] = &["analyze", "paths", "--postfix-repeat", "1"];
const CMD_ANALYZE_PATHS_REPEAT_2: &[&str] = &["analyze", "paths", "--postfix-repeat", "2"];
const CMD_ANALYZE_SAFETYFLOW: &[&str] = &["analyze", "safetyflow"];
const CMD_ANALYZE_SSA: &[&str] = &["analyze", "ssa"];
const CMD_ANALYZE_RANGE: &[&str] = &["analyze", "range"];
const CMD_ANALYZE_CALLGRAPH: &[&str] = &["analyze", "callgraph"];
const CMD_ANALYZE_ADG: &[&str] = &["analyze", "adg", "--dump", "api_graph.yml"];
const CMD_VERIFY: &[&str] = &["verify"];
const CMD_VERIFY_TARGETED: &[&str] = &["verify", "--mode", "targeted"];
const CMD_VERIFY_PREPARE: &[&str] = &["verify", "--prepare-targets"];
const CMD_VERIFY_REPEAT_1: &[&str] = &["verify", "--postfix-repeat", "1"];
const CMD_VERIFY_REPEAT_2: &[&str] = &["verify", "--postfix-repeat", "2"];
const CMD_VERIFY_SCAN: &[&str] = &["verify", "--mode", "scan"];
const CMD_VERIFY_SKIP_INVARIANT: &[&str] = &["verify", "--skip-invariant"];

macro_rules! verify_sound {
    ($dir:literal, $func:literal) => {{
        let output = $crate::run_with_args($dir, CMD_VERIFY);
        $crate::assert_contain(&output, concat!("function: ", $func));
        $crate::assert_contain(&output, "result: SOUND");
    }};
}

macro_rules! verify_unsound {
    ($dir:literal, $func:literal, $prop:literal) => {{
        let output = $crate::run_with_args($dir, CMD_VERIFY);
        $crate::assert_unproved_exclusive(&output, $func, &[$prop]);
    }};
}

macro_rules! verify_hazard {
    ($dir:literal, $func:literal, $prop:literal) => {{
        let output = $crate::run_with_args($dir, CMD_VERIFY);
        $crate::assert_unproved_exclusive_with_result(&output, $func, &[$prop], "HAZARD");
    }};
}

include!("suites/check.rs");
include!("suites/analyze.rs");
include!("suites/verify_units.rs");
include!("suites/verify_cases.rs");
include!("suites/opt.rs");

#[test]
fn all_fixture_dirs_tested() {
    let all_sources = [
        include_str!("suites/check.rs"),
        include_str!("suites/analyze.rs"),
        include_str!("suites/verify_units.rs"),
        include_str!("suites/verify_cases.rs"),
        include_str!("suites/opt.rs"),
    ]
    .concat();

    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let categories: &[&str] = &["check", "analyze", "verify_units", "verify_cases", "opt"];

    let mut missing = Vec::new();
    for cat in categories {
        let cat_dir = root.join(cat);
        if !cat_dir.is_dir() {
            continue;
        }
        for entry in std::fs::read_dir(&cat_dir).expect("read dir failed") {
            let entry = entry.expect("read entry failed");
            let name = entry.file_name();
            let dir_path = format!("{}/{}", cat, name.to_str().unwrap());
            if !entry.file_type().expect("file_type failed").is_dir() {
                continue;
            }
            if !all_sources.contains(&dir_path) {
                missing.push(dir_path);
            }
        }
    }
    assert!(
        missing.is_empty(),
        "Fixture directories not referenced in any test:\n  {}",
        missing.join("\n  ")
    );
}

#[test]
fn std_contracts_valid() {
    let json = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("src/verify/source/assets/std-public-contracts.json"),
    )
    .expect("failed to read contracts JSON");
    let db: std::collections::HashMap<String, Vec<serde_json::Value>> =
        serde_json::from_str(&json).expect("failed to parse contracts JSON");

    for (key, entries) in &db {
        for entry in entries {
            assert!(entry["tag"].is_string(), "{key}: missing or invalid tag");
            assert!(entry["args"].is_array(), "{key}: missing or invalid args");
        }
    }
    assert!(!db.is_empty(), "contract database is empty");
}
