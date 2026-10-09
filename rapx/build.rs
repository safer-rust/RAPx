use std::process::Command;

fn main() {
    let (_major, minor, _patch) = detect_rustc_version();

    emit_check_cfg("rapx_ge_95");
    emit_check_cfg("rapx_ge_99");
    emit_check_cfg("rapx_ge_100");
    emit_check_cfg("rapx_const_ext");
    emit_check_cfg("rapx_box_deref_transmute");
    emit_check_cfg("rapx_has_public_adts");
    emit_check_cfg("rapx_has_attr_item_kind");
    emit_check_cfg("rapx_has_fielddef_extras");
    emit_check_cfg("rapx_has_skip_norm_wip");
    emit_check_cfg("rapx_rvalue_use_with_retag");
    emit_check_cfg("rapx_rvalue_has_reborrow");
    emit_check_cfg("rapx_scalar_to_pointer_interp_result");
    emit_check_cfg("rapx_has_fnptr_asptr");
    emit_check_cfg("rapx_has_maybe_dangling_lang_item");
    emit_check_cfg("rapx_has_attr_ir");
    emit_check_cfg("rapx_rvalue_has_nullary_op");
    emit_check_cfg("rapx_constkind_alias");
    emit_check_cfg("rapx_alias_const_inherent_self");
    emit_check_cfg("rapx_alias_ty_structured_kind");
    emit_check_cfg("rapx_has_deeply_resolve_ignoring_regions");
    emit_check_cfg("rapx_has_compiler_entrypoint");
    emit_check_cfg("rapx_defkind_const_struct");

    emit_cfg("rapx_ge_95", minor >= 95);
    emit_cfg("rapx_ge_99", minor >= 99);
    emit_cfg("rapx_ge_100", minor >= 100);
    // `DefKind::Const`/`AssocConst` were struct variants (with `is_type_const`)
    // between 1.96 and 1.99 inclusive; unit variants before and after.
    emit_cfg(
        "rapx_defkind_const_struct",
        rustc_src_contains_path("compiler/rustc_hir/src/def.rs", "is_type_const"),
    );
    emit_cfg(
        "rapx_has_public_adts",
        rustc_src_contains_path("compiler/rustc_public/src/lib.rs", "pub fn adts"),
    );
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
        rustc_src_contains_path(
            "compiler/rustc_type_ir/src/unnormalized.rs",
            "fn skip_norm_wip",
        ),
    );
    emit_cfg(
        "rapx_rvalue_use_with_retag",
        rustc_src_contains_path("compiler/rustc_middle/src/mir/syntax.rs", "WithRetag"),
    );
    // `CastKind::BoxDerefTransmute` is the compiler's dedicated marker for the
    // safe `*box` deref; present only on recent nightlies.
    emit_cfg(
        "rapx_box_deref_transmute",
        rustc_src_contains_path("compiler/rustc_middle/src/mir/syntax.rs", "BoxDerefTransmute"),
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
        rustc_src_contains_path("compiler/rustc_middle/src/ty/instance.rs", "FnPtrAsPtr"),
    );
    emit_cfg(
        "rapx_has_maybe_dangling_lang_item",
        rustc_src_contains_path("compiler/rustc_hir/src/lang_items.rs", "MaybeDangling")
            || rustc_src_contains_path("compiler/rustc_attr_ir/src/lang_items.rs", "MaybeDangling"),
    );
    // `LangItem` / `Attribute` / `AttributeKind` / `find_attr!` moved from
    // `rustc_hir` into the new `rustc_attr_ir` crate around 2026-09 (nightly
    // 1.101).  Detect the move by the presence of `LangItem` in
    // `rustc_attr_ir`.
    emit_cfg(
        "rapx_has_attr_ir",
        rustc_src_contains_path("compiler/rustc_attr_ir/src/lang_items.rs", "pub enum LangItem"),
    );
    emit_cfg(
        "rapx_rvalue_has_nullary_op",
        rustc_src_contains_path(
            "compiler/rustc_middle/src/mir/syntax.rs",
            "NullaryOp(NullOp)",
        ),
    );
    // `ty::ConstKind` renamed its unevaluated-const variant from `Unevaluated`
    // to `Alias` (with `IsRigid` + `AliasConst`) around 2026-07.
    emit_cfg(
        "rapx_constkind_alias",
        rustc_src_contains_path(
            "compiler/rustc_type_ir/src/const_kind.rs",
            "Alias(ty::IsRigid",
        ),
    );
    // `AliasConstKind::Inherent` split into `InherentSelf` + `InherentImpl` and
    // `opt_def_id` was dropped (extract the def_id by matching) around 2026-09.
    emit_cfg(
        "rapx_alias_const_inherent_self",
        rustc_src_contains_path("compiler/rustc_type_ir/src/const_kind.rs", "InherentSelf"),
    );
    // `InferCtxt::resolve_vars_if_possible` was renamed to
    // `deeply_resolve_ignoring_regions` in nightly 2026-09-11.
    emit_cfg(
        "rapx_has_deeply_resolve_ignoring_regions",
        rustc_src_contains_path(
            "compiler/rustc_infer/src/infer/mod.rs",
            "deeply_resolve_ignoring_regions",
        ),
    );
    // `Const::{try_to_value,try_to_target_usize}` moved from an inherent impl
    // onto the `ConstExt` trait (which must be in scope) in a recent nightly.
    emit_cfg(
        "rapx_const_ext",
        rustc_src_contains_path(
            "compiler/rustc_middle/src/ty/consts.rs",
            "pub trait ConstExt",
        ),
    );
    // `AliasTyKind` variants gained named fields (`Projection { def_id }`) and
    // `AliasTy::kind` changed from a method to a field around 2026-07.
    emit_cfg(
        "rapx_alias_ty_structured_kind",
        rustc_src_contains_path(
            "compiler/rustc_type_ir/src/ty_kind.rs",
            "Projection { def_id",
        ),
    );
    // `rustc_driver::run_compiler` was renamed to `compiler_entrypoint` (with a
    // `&mut (dyn Callbacks + Send)` callback) in nightly 1.101.
    emit_cfg(
        "rapx_has_compiler_entrypoint",
        rustc_src_contains_path(
            "compiler/rustc_driver_impl/src/lib.rs",
            "pub fn compiler_entrypoint",
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
    let path = format!("{}/lib/rustlib/rustc-src/rust/{}", sysroot, relative_path);
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
