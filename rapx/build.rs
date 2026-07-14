use std::process::Command;

fn main() {
    let (_major, minor, _patch) = detect_rustc_version();

    // Register all cfg flags with Cargo for expected warnings suppression.
    emit_check_cfg("rustc_spanned_at_root");
    emit_check_cfg("rapx_rustc_ge_193");
    emit_check_cfg("rapx_rustc_ge_196");
    emit_check_cfg("rapx_rustc_ge_198");
    emit_check_cfg("rapx_rustc_ge_199");
    emit_check_cfg("rapx_rustc_ge_200");

    // ─── Version-gated compatibility flags ───────────────────────────────
    //
    // Add new entries here when compiler APIs change.  Each entry records
    // the minimum rustc minor version that requires the new code path.
    //
    // Flag name                     | since | Description
    // ------------------------------|-------|-------------------------------
    // rustc_spanned_at_root         | 1.96  | Spanned: source_map::Spanned
    //                               |       | became private; only
    //                               |       | rustc_span::Spanned is public
    // rapx_rustc_ge_193            | 1.93  | Analysis trait: &mut self→&self
    //                               |       | NullaryOp: 1→2 fields
    //                               |       | Option<EarlyBinder<T>> blanket
    //                               |       |   methods (skip_binder, etc.)
    //                               |       | impl_trait_id, impl_opt_trait_ref
    //                               |       |   added to TyCtxt
    //                               |       | is_doc_comment: bool→Option<bool>
    // rapx_rustc_ge_196            | 1.96  | Rvalue::NullaryOp removed
    //                               |       | Rvalue::ShallowInitBox removed
    //                               |       | Spanned: re-export→re-export of
    //                               |       |   private type
    //                               |       | Operand::RuntimeChecks added
    //                               |       | Fn::eii_impls added
    //                               |       | DefKind::Const/AssocConst
    //                               |       |   unit→struct variants
    //                               |       | Query key ref changes
    // rapx_rustc_ge_198            | 1.98  | Ty/TraitRef/Clause/FnSig
    //                               |       |   wrapped in Unnormalized
    //                               |       | StatementKind::Retag removed
    //                               |       | TerminatorKind::Drop
    //                               |       |   async_fut field removed
    //                               |       | ItemKind::Trait struct variant
    //                               |       | FieldDef::mut_restriction added
    //                               |       | Various tuple variant field
    //                               |       |   count changes
    // rapx_rustc_ge_199            | 1.99  | AST `tokens` field removed from
    //                               |       |   Block/Visibility/Ty/Item/
    //                               |       |   MutRestriction node structs
    // rapx_rustc_ge_200            | 1.100 | GenericArg::as_type() removed;
    //                               |       | use GenericArgKind::Type
    //                               |       | GenericArgsRef wrapped in Binder
    //                               |       |   at FnDef destructuring sites
    emit_cfg("rustc_spanned_at_root", minor >= 96);
    emit_cfg("rapx_rustc_ge_193", minor >= 93);
    emit_cfg("rapx_rustc_ge_196", minor >= 96);
    emit_cfg("rapx_rustc_ge_198", minor >= 98);
    emit_cfg("rapx_rustc_ge_199", minor >= 99);
    emit_cfg("rapx_rustc_ge_200", minor >= 100);
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
