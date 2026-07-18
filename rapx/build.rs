use std::process::Command;

fn main() {
    let (_major, minor, _patch) = detect_rustc_version();

    emit_check_cfg("rustc_spanned_at_root");
    emit_check_cfg("rapx_rustc_ge_193");
    emit_check_cfg("rapx_rustc_ge_196");
    emit_check_cfg("rapx_rustc_ge_198");
    emit_check_cfg("rapx_rustc_ge_199");
    emit_check_cfg("rapx_rustc_ge_100");

    emit_cfg("rustc_spanned_at_root", minor >= 96);
    emit_cfg("rapx_rustc_ge_193", minor >= 93);
    emit_cfg("rapx_rustc_ge_196", minor >= 96);
    emit_cfg("rapx_rustc_ge_198", minor >= 98);
    emit_cfg("rapx_rustc_ge_199", minor >= 99);
    emit_cfg("rapx_rustc_ge_100", minor >= 100);
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
