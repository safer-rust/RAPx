/*
 * This module implements the `audit unsafe-apis` and `audit std-unsafe-apis` commands.
 * It collects all public unsafe functions from the current crate or the standard library
 * and outputs them as JSON.
 */

use crate::analysis::utils::fn_info::{
    check_safety, check_visibility, get_all_std_fns_by_rustc_public,
};
use rustc_hir::{
    ImplItemKind, PatKind, Safety, TraitFn, TraitItemKind,
    def::DefKind,
    def_id::{DefId, LOCAL_CRATE},
};
use rustc_middle::ty::TyCtxt;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct ParamInfo {
    pub name: String,
    pub ty: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct UnsafeApiEntry {
    pub module: String,
    pub name: String,
    pub params: Vec<ParamInfo>,
    pub safety_doc: Option<String>,
}

/// Returns true if `line` is a Markdown heading that should stop content
/// collection for a `# Safety` section at the given `level` (1 or 2).
fn is_heading_stop(line: &str, level: usize) -> bool {
    let is_h1 = line.starts_with("# ") || line == "#";
    if level == 1 {
        return is_h1;
    }
    // level == 2: stop at `#` or `##` headings
    is_h1 || line.starts_with("## ") || line == "##"
}

/// Extract the `# Safety` or `## Safety` section from a Rust doc comment string.
///
/// The `doc` parameter should be the concatenation of all `#[doc = "..."]` attribute
/// values joined by newlines, as returned by `attr.doc_str()`.
///
/// Returns the text of the Safety section (with leading/trailing whitespace trimmed),
/// or `None` if no Safety section is present.
pub fn extract_safety_doc(doc: &str) -> Option<String> {
    let lines: Vec<&str> = doc.lines().collect();
    let mut start_idx: Option<usize> = None;
    let mut safety_level: usize = 0;

    for (i, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if trimmed == "# Safety" {
            safety_level = 1;
            start_idx = Some(i + 1);
            break;
        } else if trimmed == "## Safety" {
            safety_level = 2;
            start_idx = Some(i + 1);
            break;
        }
    }

    let start = start_idx?;

    let mut content_lines: Vec<&str> = Vec::new();
    for line in lines.iter().skip(start) {
        let trimmed = line.trim();
        // Stop at any heading at the same or higher level.
        // For level 1 (`# Safety`), any `#` heading stops the section.
        // For level 2 (`## Safety`), any `#` or `##` heading stops the section.
        if is_heading_stop(trimmed, safety_level) {
            break;
        }
        content_lines.push(trimmed);
    }

    // Trim trailing empty lines
    while content_lines.last().map_or(false, |l| l.is_empty()) {
        content_lines.pop();
    }
    // Trim leading empty lines
    while content_lines.first().map_or(false, |l| l.is_empty()) {
        content_lines.remove(0);
    }

    let content = content_lines.join("\n");
    if content.is_empty() { None } else { Some(content) }
}

pub struct AuditUnsafeApis<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> AuditUnsafeApis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    /// Run audit for the current (local) crate and print JSON to stderr.
    pub fn run_local(&self) {
        let entries = self.collect_local();
        match serde_json::to_string_pretty(&entries) {
            Ok(json) => eprintln!("{}", json),
            Err(e) => eprintln!("audit: JSON serialization error: {}", e),
        }
    }

    /// Run audit for the Rust standard library and print JSON to stderr.
    pub fn run_std(&self) {
        let entries = self.collect_std();
        match serde_json::to_string_pretty(&entries) {
            Ok(json) => eprintln!("{}", json),
            Err(e) => eprintln!("audit: JSON serialization error: {}", e),
        }
    }

    /// Collect doc comment text for a def_id by joining all `#[doc = "..."]` attrs.
    fn get_doc_string(&self, def_id: DefId) -> String {
        self.tcx
            .get_all_attrs(def_id)
            .iter()
            .filter_map(|attr| attr.doc_str())
            .map(|sym| sym.as_str().to_string())
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// Extract the `# Safety` section from the doc comment of a def_id.
    fn get_safety_doc(&self, def_id: DefId) -> Option<String> {
        extract_safety_doc(&self.get_doc_string(def_id))
    }

    /// Get parameter types from the function signature.
    fn get_params(&self, def_id: DefId) -> Vec<ParamInfo> {
        let fn_sig = self.tcx.fn_sig(def_id).instantiate_identity();
        let inputs = fn_sig.skip_binder().inputs();

        // Try to get parameter names from HIR for local functions.
        let param_names = self.get_hir_param_names(def_id);

        inputs
            .iter()
            .enumerate()
            .map(|(i, ty)| {
                let name = param_names
                    .get(i)
                    .cloned()
                    .unwrap_or_else(|| format!("arg{}", i));
                ParamInfo {
                    name,
                    ty: format!("{}", ty),
                }
            })
            .collect()
    }

    /// Attempt to retrieve parameter names from the HIR body for a local function.
    fn get_hir_param_names(&self, def_id: DefId) -> Vec<String> {
        let Some(local_def_id) = def_id.as_local() else {
            return Vec::new();
        };

        let hir_node = self.tcx.hir_node_by_def_id(local_def_id);
        let body_id = match hir_node {
            rustc_hir::Node::Item(item) => {
                if let rustc_hir::ItemKind::Fn { body, .. } = &item.kind {
                    Some(*body)
                } else {
                    None
                }
            }
            rustc_hir::Node::ImplItem(item) => {
                if let ImplItemKind::Fn(_, body) = item.kind {
                    Some(body)
                } else {
                    None
                }
            }
            rustc_hir::Node::TraitItem(item) => {
                if let TraitItemKind::Fn(_, TraitFn::Provided(body)) = item.kind {
                    Some(body)
                } else {
                    None
                }
            }
            _ => None,
        };

        if let Some(body_id) = body_id {
            let body = self.tcx.hir_body(body_id);
            body.params
                .iter()
                .map(|param| match &param.pat.kind {
                    PatKind::Binding(_, _, ident, _) => ident.name.as_str().to_string(),
                    _ => "_".to_string(),
                })
                .collect()
        } else {
            Vec::new()
        }
    }

    /// Build an `UnsafeApiEntry` from a `DefId`.
    fn make_entry(&self, def_id: DefId) -> UnsafeApiEntry {
        let name = self.tcx.item_name(def_id).as_str().to_string();

        let module = if let Some(local_def_id) = def_id.as_local() {
            // For local items, build the module path as `crate_name[::parent_module]`.
            let crate_name = self.tcx.crate_name(LOCAL_CRATE).as_str().to_string();
            let mod_local = self.tcx.parent_module_from_def_id(local_def_id);
            let parent_path = self.tcx.def_path_str(mod_local.to_def_id());
            if parent_path.is_empty() {
                crate_name
            } else {
                format!("{}::{}", crate_name, parent_path)
            }
        } else {
            // For external items, derive the module by stripping the trailing `::name`
            // component from the full qualified path.
            let full_path = self.tcx.def_path_str(def_id);
            if let Some(pos) = full_path.rfind("::") {
                full_path[..pos].to_string()
            } else {
                full_path
            }
        };

        UnsafeApiEntry {
            module,
            name,
            params: self.get_params(def_id),
            safety_doc: self.get_safety_doc(def_id),
        }
    }

    /// Collect all public unsafe `fn` and `AssocFn` items in the local crate.
    fn collect_local(&self) -> Vec<UnsafeApiEntry> {
        let mut entries = Vec::new();

        for local_def_id in self.tcx.mir_keys(()) {
            let def_id = local_def_id.to_def_id();
            let kind = self.tcx.def_kind(def_id);
            if !matches!(kind, DefKind::Fn | DefKind::AssocFn) {
                continue;
            }
            if !check_visibility(self.tcx, def_id) {
                continue;
            }
            if check_safety(self.tcx, def_id) != Safety::Unsafe {
                continue;
            }
            entries.push(self.make_entry(def_id));
        }

        entries
    }

    /// Collect all public unsafe functions from the Rust standard library.
    fn collect_std(&self) -> Vec<UnsafeApiEntry> {
        let mut entries = Vec::new();

        let all_std_fns = get_all_std_fns_by_rustc_public(self.tcx);
        for def_id in all_std_fns {
            if !self.tcx.visibility(def_id).is_public() {
                continue;
            }
            if check_safety(self.tcx, def_id) != Safety::Unsafe {
                continue;
            }
            entries.push(self.make_entry(def_id));
        }

        entries
    }
}

#[cfg(test)]
mod tests {
    use super::extract_safety_doc;

    #[test]
    fn test_extract_safety_doc_basic() {
        let doc = " Some function.\n \n # Safety\n \n The pointer must be valid.\n It must be non-null.";
        let result = extract_safety_doc(doc);
        assert!(result.is_some());
        let content = result.unwrap();
        assert!(content.contains("The pointer must be valid."));
        assert!(content.contains("It must be non-null."));
    }

    #[test]
    fn test_extract_safety_doc_stops_at_next_heading() {
        let doc = " # Safety\n \n Safety text.\n \n # Examples\n \n Example code.";
        let result = extract_safety_doc(doc);
        assert!(result.is_some());
        let content = result.unwrap();
        assert!(content.contains("Safety text."));
        assert!(!content.contains("Example code."));
    }

    #[test]
    fn test_extract_safety_doc_double_hash() {
        let doc = " ## Safety\n \n Must be aligned.\n \n ## Examples\n \n code.";
        let result = extract_safety_doc(doc);
        assert!(result.is_some());
        let content = result.unwrap();
        assert!(content.contains("Must be aligned."));
        assert!(!content.contains("code."));
    }

    #[test]
    fn test_extract_safety_doc_none_when_absent() {
        let doc = " Some function with no safety section.";
        let result = extract_safety_doc(doc);
        assert!(result.is_none());
    }

    #[test]
    fn test_extract_safety_doc_empty_section() {
        let doc = " # Safety\n \n # Examples\n \n code.";
        let result = extract_safety_doc(doc);
        assert!(result.is_none());
    }
}
