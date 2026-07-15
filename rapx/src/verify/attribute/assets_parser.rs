use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::OnceLock;

use crate::verify::helpers::get_cleaned_def_path_name;

/// Structure of JSON entries.
///
#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct PropertyEntry {
    pub tag: String,
    pub args: Vec<String>,
    #[serde(default)]
    pub kind: Option<String>,
}

/// Looks up backup contracts for a standard-library function by its normalized path.
/// For trait-method impls, resolves to the trait method's path first so that
/// all impls share the same contracts.
///
/// After exact-path lookup, falls back to wildcard patterns by progressively
/// replacing the tail segment with `*`.  For example, for
/// `core::slice::<impl [T]>::as_chunks`, the fallback chain is:
///
/// 1. `core::slice::<impl [T]>::as_chunks`  (exact)
/// 2. `core::slice::<impl [T]>::*`          (all methods of `[T]`)
/// 3. `core::slice::*`                      (all functions in slice module)
/// 4. `core::*`                             (anything in core crate)
pub fn get_std_contracts_from_assets(tcx: TyCtxt<'_>, def_id: DefId) -> &'static [PropertyEntry] {
    let lookup_def_id = resolve_trait_method(tcx, def_id);
    let cleaned_path_name = get_cleaned_def_path_name(tcx, lookup_def_id);
    let db = get_std_contracts_from_json();

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
        segments[i] = "*";
        if segments[i..].iter().all(|s| *s == "*") {
            segments.truncate(i + 1);
        }
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
fn get_std_contracts_from_json() -> &'static HashMap<String, Vec<PropertyEntry>> {
    static STD_CONTRACTS: OnceLock<HashMap<String, Vec<PropertyEntry>>> = OnceLock::new();
    STD_CONTRACTS.get_or_init(|| {
        let raw = include_str!("assets/std-public-contracts.json");
        let normalized = normalize_json_trailing_commas(raw);
        serde_json::from_str(normalized.as_str())
            .unwrap_or_else(|err| panic!("failed to parse verify std contracts backup: {err}"))
    })
}

/// Removes trailing commas that appear immediately before `}` or `]` in JSON text.
///
/// This allows the embedded backup JSON file to remain slightly permissive while
/// still being parsed by `serde_json`.
fn normalize_json_trailing_commas(input: &str) -> String {
    let mut normalized = String::with_capacity(input.len());
    let mut iter = input.char_indices().peekable();

    while let Some((_, ch)) = iter.next() {
        if ch == ',' {
            let mut lookahead = iter.clone();
            while let Some((_, next_ch)) = lookahead.peek() {
                if next_ch.is_whitespace() {
                    lookahead.next();
                } else {
                    break;
                }
            }
            if let Some((_, next_ch)) = lookahead.peek()
                && (*next_ch == '}' || *next_ch == ']')
            {
                continue;
            }
        }
        normalized.push(ch);
    }

    normalized
}

/// Serialisation-friendly struct for the type-invariants JSON.
#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct TypeInvariantEntry {
    #[serde(default)]
    pub comment: Option<String>,
    pub invariants: Vec<PropertyEntry>,
}

/// Returns the std-type-invariants database, mapping a type path key
/// (e.g. `"alloc::boxed::Box<T>"`) to its invariant entries.
pub fn get_std_type_invariants(
) -> &'static HashMap<String, TypeInvariantEntry> {
    static TYPE_INVARIANTS: OnceLock<HashMap<String, TypeInvariantEntry>> = OnceLock::new();
    TYPE_INVARIANTS.get_or_init(|| {
        let raw = include_str!("assets/std-type-invariants.json");
        let normalized = normalize_json_trailing_commas(raw);
        serde_json::from_str(normalized.as_str())
            .unwrap_or_else(|err| panic!("failed to parse std type invariants: {err}"))
    })
}
