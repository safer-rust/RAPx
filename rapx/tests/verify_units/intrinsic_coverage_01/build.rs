use std::process::Command;

fn main() {
    println!("cargo:rustc-check-cfg=cfg(rapx_generic_float_minmax)");

    let rustc = std::env::var("RUSTC").expect("RUSTC is set by Cargo");
    let sysroot = Command::new(rustc)
        .args(["--print", "sysroot"])
        .output()
        .expect("rustc --print sysroot succeeds");
    let sysroot = String::from_utf8(sysroot.stdout).expect("sysroot is UTF-8");
    let source = std::path::Path::new(sysroot.trim())
        .join("lib/rustlib/src/rust/library/core/src/intrinsics/mod.rs");
    if let Ok(source) = std::fs::read_to_string(source) {
        if source.contains("pub const fn minimum<T:") {
            println!("cargo:rustc-cfg=rapx_generic_float_minmax");
        }
    }
}
