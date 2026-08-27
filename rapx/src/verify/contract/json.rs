//! The bundled JSON contract front-end: loading, lookup, and conversion.
//!
//! Two embedded JSON assets provide out-of-the-box contracts: std function
//! contracts (`std-public-contracts.json`) and std type invariants
//! (`std-type-invariants.json`). Lookup uses exact, path-stripped, and wildcard
//! fallback so trait-method impls and re-exported paths resolve correctly.
//! Entries are then converted into [`Property`] values via [`entry_to_property`].

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::OnceLock;
use syn::Expr;

use crate::helpers::name::get_cleaned_def_path_name;

use super::types::{Property, PropertyKind};

/// Structure of JSON entries.
///
/// When `tag == "any"` and `any` is present, the entry represents a
/// disjunction (logical OR) of property groups.  Each element in `any`
/// is either a single [`JsonProperty`] (one disjunct) or an array of
/// entries (a conjunction group — all must hold).
///
/// JSON format for `any` (flat OR):
/// ```json
/// {
///   "tag": "any",
///   "any": [
///     {"tag": "Trait", "args": ["T", "Copy"]},
///     {"tag": "Alias", "args": ["T", "return"]}
///   ]
/// }
/// ```
///
/// JSON format for `any` with conjunction group (null-guard):
/// ```json
/// {
///   "tag": "any",
///   "any": [
///     {"tag": "Null", "args": ["head"]},
///     [
///       {"tag": "Align", "args": ["head", "Node"]},
///       {"tag": "ValidPtr", "args": ["head", "Node", "1"]}
///     ]
///   ]
/// }
/// ```
#[derive(Debug, Serialize, Deserialize, Clone)]
pub(crate) struct JsonProperty {
    pub tag: String,
    #[serde(default)]
    pub args: Vec<String>,
    #[serde(default)]
    pub kind: Option<String>,
    /// When `tag == "any"`, the list of disjuncts (OR alternatives).
    /// Each element is either a single entry or a conjunction group.
    #[serde(default)]
    pub any: Option<Vec<AnyItem>>,
}

/// One disjunct inside a JSON `any` entry.
///
/// `Single` is one property; `And` is a conjunction of properties
/// (all must hold together, forming one OR alternative).
#[derive(Debug, Serialize, Deserialize, Clone)]
#[serde(untagged)]
pub(crate) enum AnyItem {
    Single(JsonProperty),
    And(Vec<JsonProperty>),
}

/// Looks up backup contracts for a standard-library function by its normalized path.
/// For trait-method impls, resolves to the trait method's path first so that
/// all impls share the same contracts.
///
/// After exact-path lookup, first strips impl-block type segments, then falls
/// back to wildcard patterns by progressively replacing the tail segment with
/// `*`.  For example, for `core::slice::<impl [T]>::as_chunks`, the fallback
/// chain is:
///
/// 1. `core::slice::<impl [T]>::as_chunks`  (exact)
/// 2. `core::slice::as_chunks`              (impl segments stripped)
/// 3. `core::slice::<impl [T]>::*`          (all methods of `[T]`)
/// 4. `core::slice::*`                      (all functions in slice module)
/// 5. `core::*`                             (anything in core crate)
pub(crate) fn get_std_contracts_from_json(tcx: TyCtxt<'_>, def_id: DefId) -> &'static [JsonProperty] {
    let lookup_def_id = resolve_trait_method(tcx, def_id);
    let cleaned_path_name = get_cleaned_def_path_name(tcx, lookup_def_id);
    let db = load_std_contracts_json();

    // Exact match first.
    if let Some(entries) = db.get(&cleaned_path_name) {
        return entries.as_slice();
    }

    // Strip intra-path type segments that appear in impl blocks.
    // E.g. `core::slice::[T]::as_chunks_unchecked` → `core::slice::as_chunks_unchecked`.
    {
        let stripped: Vec<&str> = cleaned_path_name
            .split("::")
            .filter(|s| !s.starts_with('[') && !s.starts_with('<'))
            .collect();
        if stripped.len() != cleaned_path_name.matches("::").count() + 1 {
            let stripped_path = stripped.join("::");
            if let Some(entries) = db.get(&stripped_path) {
                return entries.as_slice();
            }
        }
    }

    // Wildcard fallback: progressively replace tail segments with `*`.
    let mut segments: Vec<&str> = cleaned_path_name.split("::").collect();
    for i in (1..segments.len()).rev() {
        segments.truncate(i + 1);
        segments[i] = "*";
        let pattern = segments.join("::");
        if let Some(entries) = db.get(&pattern) {
            return entries.as_slice();
        }
    }

    // Try bare `*` for any function.
    if let Some(entries) = db.get("*") {
        return entries.as_slice();
    }

    &[]
}

/// If `def_id` is a trait-method implementation, returns the corresponding
/// trait method's [`DefId`]; otherwise returns `def_id` unchanged.
fn resolve_trait_method(tcx: TyCtxt<'_>, def_id: DefId) -> DefId {
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        if let Some(trait_def_id) = assoc_item.trait_item_def_id() {
            return trait_def_id;
        }
    }
    def_id
}

/// Lazily loads the backup contract database for standard-library APIs.
fn load_std_contracts_json() -> &'static HashMap<String, Vec<JsonProperty>> {
    static STD_CONTRACTS: OnceLock<HashMap<String, Vec<JsonProperty>>> = OnceLock::new();
    STD_CONTRACTS.get_or_init(|| {
        serde_json::from_str(include_str!("assets/std-public-contracts.json"))
            .expect("failed to parse verify std contracts backup")
    })
}

/// Serialisation-friendly struct for the type-invariants JSON.
#[derive(Debug, Serialize, Deserialize, Clone)]
pub(crate) struct TypeInvariantEntry {
    #[serde(default)]
    pub comment: Option<String>,
    pub invariants: Vec<JsonProperty>,
}

/// Returns the std-type-invariants database, mapping a type path key
/// (e.g. `"core::num::nonzero::NonZero"`) to its invariant entries.
pub(crate) fn get_std_type_invariants() -> &'static HashMap<String, TypeInvariantEntry> {
    static TYPE_INVARIANTS: OnceLock<HashMap<String, TypeInvariantEntry>> = OnceLock::new();
    TYPE_INVARIANTS.get_or_init(|| {
        serde_json::from_str(include_str!("assets/std-type-invariants.json"))
            .expect("failed to parse std type invariants")
    })
}

// ── Entry conversion & argument normalization ───────────────────────────────

/// Convert a single [`JsonProperty`] from JSON into the properties it denotes.
///
/// Resolves named parameter references (e.g. `"src"` → `"Arg_0"`), normalizes
/// explicit JSON tokens (`arg:`, `const:`, `ty:`), and delegates to
/// [`Property::parse_list`] for tag-based parsing.  A single entry may expand to
/// several properties (via a compound property or `any`), hence the `Vec` return.
pub(crate) fn entry_to_property<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    entry: &JsonProperty,
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
pub(crate) fn resolve_json_args(
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
pub(crate) fn resolve_json_param_name(arg: &str, param_names: &[String]) -> String {
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
pub(crate) fn normalize_json_contract_arg(arg: &str) -> String {
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
/// Uses [`get_std_contracts_from_json`] for lookup with wildcard fallback,
/// then parses each entry into a [`Property`] via [`entry_to_property`].
pub(crate) fn query_json_contracts<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<Property<'tcx>> {
    let entries = get_std_contracts_from_json(tcx, def_id);
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
