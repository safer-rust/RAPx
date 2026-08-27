//! Centralized contract query service.
//!
//! Provides a unified API for querying safety contracts from all sources:
//!
//! 1. **Inline `#[rapx::requires(...)]` annotations** — highest priority, parsed
//!    from HIR attributes.
//! 2. **`#[rapx::ensures(...)]` on trait methods** — inherited by implementors
//!    that lack their own annotations.
//! 3. **Bundled JSON contracts** — embedded backup for standard-library unsafe
//!    APIs without inline annotations.
//! 4. **Chain resolution** — follows the call chain to find inherited contracts.
//!
//! Contract resolution priority (per `VerifyTargetCollector::get_fn_contracts`):
//! a. Inline `#[rapx::requires]` on the callee.
//! b. Trait method `#[rapx::requires]` (if the callee is a trait impl without its
//!    own annotations).
//! c. Bundled JSON contracts (for std callees).
//! d. Recursive chain resolution (`resolve_chain_contracts`) — follows the call
//!    chain to find inherited contracts.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use syn::Expr;

use super::assets::{AnyItem, PropertyEntry, get_std_contracts_from_assets};

use super::types::{Property, PropertyKind};

/// Convert a single [`PropertyEntry`] from JSON into the properties it denotes.
///
/// Resolves named parameter references (e.g. `"src"` → `"Arg_0"`), normalizes
/// explicit JSON tokens (`arg:`, `const:`, `ty:`), and delegates to
/// [`Property::parse_list`] for tag-based parsing.  A single entry may expand to
/// several properties (via a compound `def` or `any`), hence the `Vec` return.
pub fn entry_to_property<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    entry: &PropertyEntry,
    param_names: &[String],
    has_names: bool,
) -> Vec<Property<'tcx>> {
    if entry.tag == "any" {
        if let Some(disjuncts) = &entry.any {
            if disjuncts.len() >= 2 {
                let mut prop = any_entry_to_property(tcx, def_id, disjuncts, param_names, has_names);
                prop.apply_kind(entry.kind.as_deref());
                return vec![prop];
            }
            rap_error!(
                "JSON any entry requires at least 2 disjuncts, got {}",
                disjuncts.len()
            );
            return Vec::new();
        }
        rap_error!("JSON any entry missing 'any' field");
        return Vec::new();
    }

    let exprs = resolve_json_args(&entry.args, param_names, has_names, &entry.tag);
    if exprs.len() != entry.args.len() {
        rap_error!(
            "Parse JSON API args error: Failed to parse arg '{:?}' for tag {}",
            entry.args, entry.tag
        );
        return Vec::new();
    }

    let properties = Property::parse_list(tcx, def_id, entry.tag.as_str(), &exprs);
    let mut result = Vec::new();
    for mut property in properties {
        property.apply_kind(entry.kind.as_deref());
        if matches!(property.kind(), Some(PropertyKind::Unknown)) {
            rap_debug!(
                "skip unsupported std safety contract tag '{}' for callee {:?}",
                entry.tag, def_id
            );
            continue;
        }
        result.push(property);
    }
    result
}

/// Parse an `any` disjunction entry from JSON into a `Property::Or` property.
///
/// Each element of `disjuncts` is an [`AnyItem`]:
/// - `Single(entry)` → one-property disjunct
/// - `And(entries)` → conjunction group (all entries must hold for this disjunct)
fn any_entry_to_property<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    disjuncts: &[AnyItem],
    param_names: &[String],
    has_names: bool,
) -> Property<'tcx> {
    let mut or_disjuncts: Vec<Property<'tcx>> = Vec::new();
    for item in disjuncts {
        match item {
            AnyItem::Single(entry) => {
                if entry.tag == "any" {
                    rap_error!("Nested 'any' inside 'any' is not supported in JSON contracts");
                    continue;
                }
                let exprs =
                    resolve_json_args(&entry.args, param_names, has_names, &entry.tag);
                if exprs.len() != entry.args.len() {
                    rap_error!(
                        "Parse any entry arg error: Failed to parse arg '{:?}' for tag {}",
                        entry.args, entry.tag
                    );
                    continue;
                }
                let props = Property::parse_list(tcx, def_id, entry.tag.as_str(), &exprs);
                let mut group: Vec<Property<'tcx>> = Vec::new();
                for mut prop in props {
                    prop.apply_kind(entry.kind.as_deref());
                    group.push(prop);
                }
                if !group.is_empty() {
                    or_disjuncts.push(Property::conjunction(group));
                }
            }
            AnyItem::And(entries) => {
                let mut group: Vec<Property<'tcx>> = Vec::new();
                for entry in entries {
                    if entry.tag == "any" {
                        rap_error!("Nested 'any' inside 'any' group is not supported");
                        continue;
                    }
                    let exprs =
                        resolve_json_args(&entry.args, param_names, has_names, &entry.tag);
                    if exprs.len() != entry.args.len() {
                        rap_error!(
                            "Parse any group entry arg error: failed to parse '{:?}' for tag {}",
                            entry.args, entry.tag
                        );
                        continue;
                    }
                    let props =
                        Property::parse_list(tcx, def_id, entry.tag.as_str(), &exprs);
                    for mut prop in props {
                        prop.apply_kind(entry.kind.as_deref());
                        group.push(prop);
                    }
                }
                if !group.is_empty() {
                    or_disjuncts.push(Property::conjunction(group));
                }
            }
        }
    }
    Property::new_or(or_disjuncts)
}

/// Resolve JSON contract argument strings to parsed [`syn::Expr`] values.
///
/// Handles:
/// - Named parameter resolution (e.g. `"src"` → `"arg:0"`)
/// - Explicit token normalization (`arg:`, `const:`, `ty:` prefixes)
/// - Lifetime stripping (`'a` → `a`)
pub fn resolve_json_args(
    args: &[String],
    param_names: &[String],
    has_names: bool,
    tag: &str,
) -> Vec<Expr> {
    let mut exprs: Vec<Expr> = Vec::new();
    for arg_str in args {
        let resolved = if has_names {
            resolve_json_param_name(arg_str, param_names)
        } else {
            arg_str.clone()
        };
        let normalized_arg = normalize_json_contract_arg(&resolved);
        match syn::parse_str::<Expr>(&normalized_arg) {
            Ok(expr) => exprs.push(expr),
            Err(_) => {
                if let Some(lifetime) = normalized_arg.strip_prefix('\'') {
                    if lifetime.chars().all(|c| c.is_alphabetic() || c == '_') {
                        match syn::parse_str::<Expr>(lifetime) {
                            Ok(expr) => exprs.push(expr),
                            Err(_) => {
                                rap_error!(
                                    "JSON Contract Error: Failed to parse lifetime \
                                     '{}' as Rust Expr for tag {}",
                                    arg_str, tag
                                );
                            }
                        }
                    } else {
                        rap_error!(
                            "JSON Contract Error: Failed to parse arg '{}' as Rust Expr for tag {}",
                            arg_str, tag
                        );
                    }
                } else {
                    rap_error!(
                        "JSON Contract Error: Failed to parse arg '{}' as Rust Expr for tag {}",
                        arg_str, tag
                    );
                }
            }
        }
    }
    exprs
}

/// Resolve a simple parameter-name reference in a JSON contract arg string to
/// the `arg:N` positional form.  Complex expressions (containing function
/// calls, field access, etc.) are left unchanged — they are handled later by
/// the expression parser which already knows how to resolve named parameters.
pub fn resolve_json_param_name(arg: &str, param_names: &[String]) -> String {
    if arg.starts_with("arg:")
        || arg.starts_with("const:")
        || arg.starts_with("ty:")
        || arg.contains('(')
        || arg.contains('.')
        || arg.contains("::")
        || arg.contains(' ')
        || arg.starts_with('\'')
    {
        return arg.to_string();
    }
    if let Some(pos) = param_names.iter().position(|n| n == arg) {
        format!("arg:{pos}")
    } else {
        arg.to_string()
    }
}

/// Convert explicit JSON contract tokens into the expression syntax accepted by
/// the existing property parser.
///
/// Supported explicit tokens:
/// - `arg:N` names callee argument `N` and becomes internal `Arg_N`.
/// - `const:N` names an integer constant and becomes `N`.
/// - `ty:T` names a type parameter/type identifier and becomes `T`.
///
/// Unprefixed strings are kept unchanged for compatibility with older entries
/// such as `"0"`, `"T"`, and `"1"`.
pub fn normalize_json_contract_arg(arg: &str) -> String {
    let bytes = arg.as_bytes();
    let mut out = String::with_capacity(arg.len());
    let mut i = 0;

    while i < bytes.len() {
        if arg[i..].starts_with("arg:") {
            let start = i + "arg:".len();
            let end = scan_while(arg, start, |ch| ch.is_ascii_digit());
            if end > start {
                out.push_str("Arg_");
                out.push_str(&arg[start..end]);
                i = end;
                continue;
            }
        }

        if arg[i..].starts_with("const:") {
            let start = i + "const:".len();
            let end = scan_while(arg, start, is_contract_token_char);
            if end > start {
                out.push_str(&arg[start..end]);
                i = end;
                continue;
            }
        }

        if arg[i..].starts_with("ty:") {
            let start = i + "ty:".len();
            let end = scan_while(arg, start, is_contract_token_char);
            if end > start {
                out.push_str(&arg[start..end]);
                i = end;
                continue;
            }
        }

        let ch = arg[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }

    out
}

fn scan_while(arg: &str, mut index: usize, predicate: impl Fn(char) -> bool) -> usize {
    while index < arg.len() {
        let ch = arg[index..].chars().next().unwrap();
        if !predicate(ch) {
            break;
        }
        index += ch.len_utf8();
    }
    index
}

fn is_contract_token_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_' || ch == ':'
}

/// Query contracts for a function from the bundled JSON backup database.
///
/// Uses [`get_std_contracts_from_assets`] for lookup with wildcard fallback,
/// then parses each entry into a [`Property`] via [`entry_to_property`].
pub fn query_json_contracts<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<Property<'tcx>> {
    let entries = get_std_contracts_from_assets(tcx, def_id);
    if entries.is_empty() {
        return Vec::new();
    }
    let (param_names, _) = crate::helpers::name::parse_signature(tcx, def_id);
    let has_names =
        !param_names.is_empty() && !param_names[0].chars().all(|c| c.is_ascii_digit());

    let mut results = Vec::new();
    for entry in entries {
        results.extend(entry_to_property(tcx, def_id, entry, &param_names, has_names));
    }
    results
}
