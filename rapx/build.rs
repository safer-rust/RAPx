fn main() {
    emit_check_cfg("rapx_intrinsic_enum");
    emit_check_cfg("rapx_error_output_in_output");
    emit_check_cfg("rapx_post_analysis_no_rigid_aliases");
    emit_check_cfg("rapx_mir_terminator_required");

    emit_cfg(
        "rapx_intrinsic_enum",
        rustc_src_contains_path(
            "compiler/rustc_middle/src/ty/intrinsic.rs",
            "pub enum Intrinsic {",
        ),
    );
    emit_cfg(
        "rapx_error_output_in_output",
        rustc_src_contains_path(
            "compiler/rustc_session/src/output.rs",
            "pub enum ErrorOutputType",
        ),
    );
    emit_cfg(
        "rapx_post_analysis_no_rigid_aliases",
        rustc_src_contains_path(
            "compiler/rustc_middle/src/ty/mod.rs",
            "pub fn post_analysis_no_rigid_aliases(",
        ),
    );
    emit_cfg(
        "rapx_mir_terminator_required",
        rustc_src_contains_path(
            "compiler/rustc_middle/src/mir/mod.rs",
            "pub terminator: Terminator<'tcx>",
        ),
    );
}

fn emit_check_cfg(name: &str) {
    println!("cargo::rustc-check-cfg=cfg({name})");
}

fn emit_cfg(name: &str, condition: bool) {
    if condition {
        println!("cargo::rustc-cfg={name}");
    }
}

/// Check whether a specific file in the rustc source tree contains a string.
fn rustc_src_contains_path(relative_path: &str, needle: &str) -> bool {
    let sysroot = get_sysroot();
    let path = format!("{}/lib/rustlib/rustc-src/rust/{}", sysroot, relative_path);
    println!("cargo::rerun-if-changed={path}");
    std::fs::read_to_string(path)
        .map(|s| s.contains(needle))
        .unwrap_or(false)
}

fn get_sysroot() -> String {
    use std::process::Command;
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    Command::new(&rustc)
        .arg("--print")
        .arg("sysroot")
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_default()
}
