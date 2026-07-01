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
}

/// Looks up backup contracts for a standard-library function by its normalized path.
/// For trait-method impls, resolves to the trait method's path first so that
/// all impls share the same contracts.
pub fn get_std_contracts_from_assets(tcx: TyCtxt<'_>, def_id: DefId) -> &'static [PropertyEntry] {
    let lookup_def_id = resolve_trait_method(tcx, def_id);
    let cleaned_path_name = get_cleaned_def_path_name(tcx, lookup_def_id);
    get_std_contracts_from_json()
        .get(&cleaned_path_name)
        .map(Vec::as_slice)
        .unwrap_or(&[])
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
        let raw = include_str!("assets/std-contracts.json");
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
