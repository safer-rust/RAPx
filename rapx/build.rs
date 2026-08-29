use std::process::Command;

fn main() {
    let (_major, minor, _patch) = detect_rustc_version();

    emit_check_cfg("rapx_ge_99");
    emit_check_cfg("rapx_ge_100");
    emit_check_cfg("rapx_has_attr_item_kind");
    emit_check_cfg("rapx_has_fielddef_extras");
    emit_check_cfg("rapx_has_skip_norm_wip");
    emit_check_cfg("rapx_rvalue_use_with_retag");
    emit_check_cfg("rapx_rvalue_has_reborrow");
    emit_check_cfg("rapx_scalar_to_pointer_interp_result");
    emit_check_cfg("rapx_has_fnptr_asptr");
    emit_check_cfg("rapx_rvalue_has_nullary_op");

    emit_cfg("rapx_ge_99", minor >= 99);
    emit_cfg("rapx_ge_100", minor >= 100);
    emit_cfg(
        "rapx_has_attr_item_kind",
        rustc_src_contains("pub enum AttrItemKind"),
    );
    emit_cfg(
        "rapx_has_fielddef_extras",
        rustc_src_contains("pub struct FieldDefExtras"),
    );
    emit_cfg(
        "rapx_has_skip_norm_wip",
        rustc_src_contains_path("compiler/rustc_type_ir/src/unnormalized.rs", "fn skip_norm_wip"),
    );
    emit_cfg(
        "rapx_rvalue_use_with_retag",
        rustc_src_contains_path("compiler/rustc_middle/src/mir/syntax.rs", "WithRetag"),
    );
    emit_cfg(
        "rapx_rvalue_has_reborrow",
        rustc_src_contains_path("compiler/rustc_middle/src/mir/syntax.rs", "Reborrow("),
    );
    emit_cfg(
        "rapx_scalar_to_pointer_interp_result",
        rustc_src_contains_path(
            "compiler/rustc_middle/src/mir/interpret/value.rs",
            "to_pointer(self, cx: &impl HasDataLayout) -> InterpResult",
        ),
    );
    emit_cfg(
        "rapx_has_fnptr_asptr",
        rustc_src_contains_path(
            "compiler/rustc_middle/src/ty/instance.rs",
            "FnPtrAsPtr",
        ),
    );
    emit_cfg(
        "rapx_rvalue_has_nullary_op",
        rustc_src_contains_path("compiler/rustc_middle/src/mir/syntax.rs", "NullaryOp(NullOp)"),
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

fn detect_rustc_version() -> (u32, u32, u32) {
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let output = Command::new(&rustc)
        .arg("--version")
        .output()
        .unwrap_or_else(|_| panic!("failed to run `{} --version`", rustc));

    let version = String::from_utf8_lossy(&output.stdout);
    let parts: Vec<&str> = version
        .split(|c: char| !c.is_ascii_digit())
        .filter(|s| !s.is_empty())
        .collect();

    let major = parts.first().and_then(|s| s.parse().ok()).unwrap_or(0);
    let minor = parts.get(1).and_then(|s| s.parse().ok()).unwrap_or(0);
    let patch = parts.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
    (major, minor, patch)
}

/// Check whether the rustc source tree contains a specific string (requires
/// the `rust-src` component to be installed).
fn rustc_src_contains(needle: &str) -> bool {
    let sysroot = get_sysroot();
    let ast = format!(
        "{}/lib/rustlib/rustc-src/rust/compiler/rustc_ast/src/ast.rs",
        sysroot
    );
    std::fs::read_to_string(ast)
        .map(|s| s.contains(needle))
        .unwrap_or(false)
}

/// Check whether a specific file in the rustc source tree contains a string.
fn rustc_src_contains_path(relative_path: &str, needle: &str) -> bool {
    let sysroot = get_sysroot();
    let path = format!(
        "{}/lib/rustlib/rustc-src/rust/{}",
        sysroot, relative_path
    );
    std::fs::read_to_string(path)
        .map(|s| s.contains(needle))
        .unwrap_or(false)
}

fn get_sysroot() -> String {
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
