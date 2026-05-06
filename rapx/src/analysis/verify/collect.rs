use crate::analysis::Analysis;
use crate::analysis::senryx::contract::PropertyContract;
use crate::analysis::utils::fn_info::{
    ContractEntry, get_cleaned_def_path_name, get_unsafe_callees, parse_contract_target,
};
use regex::Regex;
use rustc_hir::{
    Attribute, BodyId, FnDecl,
    def_id::{DefId, LocalDefId},
    intravisit::{FnKind, Visitor, walk_fn},
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::{Span, Symbol};
use std::collections::{HashMap, HashSet};
use std::sync::OnceLock;
use syn::Expr;

pub type RequiresContracts<'tcx> = Vec<(usize, Vec<usize>, PropertyContract<'tcx>)>;
pub type CalleeRequiresMap<'tcx> = HashMap<DefId, RequiresContracts<'tcx>>;

/// Visitor that collects all functions annotated with `#[rapx::verify]`.
pub struct VerifyAttrCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    pub targets: Vec<DefId>,
    pub unsafe_callees: HashMap<DefId, HashSet<DefId>>,
    pub callee_requires: HashMap<DefId, CalleeRequiresMap<'tcx>>,
}

impl<'tcx> VerifyAttrCollector<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        VerifyAttrCollector {
            tcx,
            targets: Vec::new(),
            unsafe_callees: HashMap::new(),
            callee_requires: HashMap::new(),
        }
    }

    fn is_std_crate_def_id(&self, def_id: DefId) -> bool {
        matches!(
            self.tcx.crate_name(def_id.krate).as_str(),
            "core" | "std" | "alloc"
        )
    }

    fn get_requires_for_unsafe_callee(&self, callee_def_id: DefId) -> RequiresContracts<'tcx> {
        let mut requires = get_contract_from_annotation(self.tcx, callee_def_id);
        if requires.is_empty() && self.is_std_crate_def_id(callee_def_id) {
            requires = get_contract_from_entry(
                self.tcx,
                callee_def_id,
                get_std_backup_contracts(self.tcx, callee_def_id),
            );
        }
        requires
    }

    fn has_rapx_verify_attr(&self, def_id: LocalDefId) -> bool {
        let hir_id = self.tcx.local_def_id_to_hir_id(def_id);

        let rapx = Symbol::intern("rapx");
        let verify = Symbol::intern("verify");

        let attrs = self.tcx.hir_attrs(hir_id);

        attrs.iter().any(|attr| {
            if attr.is_doc_comment().is_some() {
                return false;
            }

            let path = attr.path();

            path.len() == 2 && path[0] == rapx && path[1] == verify
        })
    }
}

impl<'tcx> Visitor<'tcx> for VerifyAttrCollector<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_fn(
        &mut self,
        fk: FnKind<'tcx>,
        fd: &'tcx FnDecl<'tcx>,
        b: BodyId,
        _span: Span,
        id: LocalDefId,
    ) -> Self::Result {
        if self.has_rapx_verify_attr(id) {
            let def_id = id.to_def_id();
            let unsafe_callees = get_unsafe_callees(self.tcx, def_id);
            let callee_requires = unsafe_callees
                .iter()
                .map(|callee_def_id| {
                    (
                        *callee_def_id,
                        self.get_requires_for_unsafe_callee(*callee_def_id),
                    )
                })
                .collect();
            self.unsafe_callees.insert(def_id, unsafe_callees);
            self.callee_requires.insert(def_id, callee_requires);
            self.targets.push(def_id);
        }
        walk_fn(self, fk, fd, b, id);
    }
}

/// Collect Analysis - find all functions annotated with #[rapx::verify]
pub struct VerifyTargetsCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Analysis for VerifyTargetsCollector<'tcx> {
    fn name(&self) -> &'static str {
        "Verify Collect Analysis"
    }

    fn run(&mut self) {
        rap_info!("======== #[rapx::verify] collect ========");
        let mut collector = VerifyAttrCollector::new(self.tcx);
        self.tcx.hir_visit_all_item_likes_in_crate(&mut collector);

        for target_def_id in &collector.targets {
            let target_path = self.tcx.def_path_str(*target_def_id);
            rap_info!(
                "[rapx::verify::collect] target: {} (DefId: {:?})",
                target_path,
                target_def_id
            );

            match collector.unsafe_callees.get(target_def_id) {
                Some(unsafe_callees) if !unsafe_callees.is_empty() => {
                    let mut unsafe_callee_ids: Vec<_> = unsafe_callees.iter().copied().collect();
                    unsafe_callee_ids.sort_by_key(|def_id| self.tcx.def_path_str(*def_id));

                    for unsafe_callee_def_id in unsafe_callee_ids {
                        let unsafe_callee_path = self.tcx.def_path_str(unsafe_callee_def_id);
                        rap_info!(
                            "  unsafe callee: {} (DefId: {:?})",
                            unsafe_callee_path,
                            unsafe_callee_def_id
                        );

                        match collector
                            .callee_requires
                            .get(target_def_id)
                            .and_then(|callee_map| callee_map.get(&unsafe_callee_def_id))
                        {
                            Some(requires) if !requires.is_empty() => {
                                for (local, fields, contract) in requires {
                                    rap_info!(
                                        "    safety contract: local={}, fields={:?}, {:?}",
                                        local,
                                        fields,
                                        contract
                                    );
                                }
                            }
                            _ => {
                                rap_info!("    safety contract: <none>");
                            }
                        }
                    }
                }
                _ => {
                    rap_info!("  unsafe callees: <none>");
                }
            }
        }

        rap_info!(
            "total: {} function(s) annotated with #[rapx::verify]",
            collector.targets.len()
        );
        rap_info!("=======================================");
    }

    fn reset(&mut self) {}
}

impl<'tcx> VerifyTargetsCollector<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        VerifyTargetsCollector { tcx }
    }
}

fn get_contract_from_entry<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    contract_entries: &[ContractEntry],
) -> RequiresContracts<'tcx> {
    let mut results = Vec::new();
    for entry in contract_entries {
        if entry.args.is_empty() {
            continue;
        }

        let local_id = if let Ok(arg_idx) = entry.args[0].parse::<usize>() {
            arg_idx
        } else {
            rap_error!(
                "JSON Contract Error: First argument must be a valid numeric arg index, got {}",
                entry.args[0]
            );
            continue;
        };

        let mut exprs: Vec<Expr> = Vec::new();
        for arg_str in &entry.args {
            match syn::parse_str::<Expr>(arg_str) {
                Ok(expr) => exprs.push(expr),
                Err(_) => {
                    rap_error!(
                        "JSON Contract Error: Failed to parse arg '{}' as Rust Expr for tag {}",
                        arg_str,
                        entry.tag
                    );
                }
            }
        }

        if exprs.len() != entry.args.len() {
            rap_error!(
                "Parse std API args error: Failed to parse arg '{:?}'",
                entry.args
            );
            continue;
        }

        let contract = PropertyContract::new(tcx, def_id, entry.tag.as_str(), &exprs);
        results.push((local_id, Vec::new(), contract));
    }
    results
}

fn is_rapx_tool_attr(attr: &Attribute) -> bool {
    if let Attribute::Unparsed(tool_attr) = attr
        && let Some(first_seg) = tool_attr.path.segments.first()
    {
        return first_seg.as_str() == "rapx";
    }
    false
}

fn is_rapx_requires_attr(attr: &Attribute) -> bool {
    if let Attribute::Unparsed(tool_attr) = attr {
        return tool_attr.path.segments.len() == 2
            && tool_attr.path.segments[0].as_str() == "rapx"
            && tool_attr.path.segments[1].as_str() == "requires";
    }
    false
}

fn is_rapx_inner_attr(attr: &Attribute) -> bool {
    if let Attribute::Unparsed(tool_attr) = attr {
        return tool_attr.path.segments.len() == 2
            && tool_attr.path.segments[0].as_str() == "rapx"
            && tool_attr.path.segments[1].as_str() == "inner";
    }
    false
}

fn is_legacy_precond_inner_attr(attr: &Attribute, attr_str: &str) -> bool {
    static PRECOND_KIND_RE: OnceLock<Regex> = OnceLock::new();
    let precond_kind_re =
        PRECOND_KIND_RE.get_or_init(|| Regex::new(r#"kind\s*=\s*"precond""#).unwrap());
    is_rapx_inner_attr(attr) && precond_kind_re.is_match(attr_str)
}

fn get_contract_from_annotation<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> RequiresContracts<'tcx> {
    const RAPX_PROOF_PLACEHOLDER: &str = "#[rapx::proof(proof)]";
    let mut results = Vec::new();

    for attr in tcx.get_all_attrs(def_id).into_iter() {
        if !is_rapx_tool_attr(attr) {
            continue;
        }

        let attr_str = rustc_hir_pretty::attribute_to_string(&tcx, attr);
        if attr_str.contains(RAPX_PROOF_PLACEHOLDER) {
            continue;
        }
        if !is_rapx_requires_attr(attr) && !is_legacy_precond_inner_attr(attr, attr_str.as_str()) {
            continue;
        }

        let safety_attr = safety_parser::safety::parse_attr_and_get_properties(attr_str.as_str());
        for par in safety_attr.iter() {
            for property in par.tags.iter() {
                let tag_name = property.tag.name();
                let property_args = property.args.clone().into_vec();
                let contract = PropertyContract::new(tcx, def_id, tag_name, &property_args);
                let (local, fields_with_ty) = parse_contract_target(tcx, def_id, property_args);
                let fields = fields_with_ty
                    .into_iter()
                    .map(|(field_idx, _)| field_idx)
                    .collect();
                results.push((local, fields, contract));
            }
        }
    }

    results
}

fn get_verify_std_contracts_json() -> &'static HashMap<String, Vec<ContractEntry>> {
    static STD_CONTRACTS: OnceLock<HashMap<String, Vec<ContractEntry>>> = OnceLock::new();
    STD_CONTRACTS.get_or_init(|| {
        let raw = include_str!("assets/std-contracts.json");
        let normalized = normalize_json_trailing_commas(raw);
        serde_json::from_str(normalized.as_str())
            .unwrap_or_else(|err| panic!("failed to parse verify std contracts backup: {err}"))
    })
}

fn get_std_backup_contracts(tcx: TyCtxt<'_>, def_id: DefId) -> &'static [ContractEntry] {
    let cleaned_path_name = get_cleaned_def_path_name(tcx, def_id);
    get_verify_std_contracts_json()
        .get(&cleaned_path_name)
        .map(Vec::as_slice)
        .unwrap_or(&[])
}

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

#[cfg(test)]
mod tests {
    use super::{get_verify_std_contracts_json, normalize_json_trailing_commas};

    #[test]
    fn std_contracts_backup_contains_core_ptr_read() {
        let std_contracts = get_verify_std_contracts_json();
        assert!(std_contracts.contains_key("core::ptr::read"));
    }

    #[test]
    fn normalize_json_trailing_commas_works() {
        let normalized = normalize_json_trailing_commas("{\"k\":[1,2,],}");
        let parsed: serde_json::Value = serde_json::from_str(normalized.as_str()).unwrap();
        assert_eq!(parsed["k"], serde_json::json!([1, 2]));
    }
}
