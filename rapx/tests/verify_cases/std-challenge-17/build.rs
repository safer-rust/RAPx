fn main() {
    println!("cargo::rustc-check-cfg=cfg(rapx_rustc_ge_199)");
    println!("cargo::rustc-check-cfg=cfg(rapx_rustc_ge_196)");

    let version = rustc_version::version().unwrap();
    let minor = version.minor;

    if minor >= 99 {
        println!("cargo:rustc-cfg=rapx_rustc_ge_199");
    }
    if minor >= 96 {
        println!("cargo:rustc-cfg=rapx_rustc_ge_196");
    }
}
