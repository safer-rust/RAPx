use crate::analysis::Analysis;
use rustc_hir::{
    Attribute, BodyId, FnDecl, ItemKind,
    def_id::{DefId, LocalDefId},
    intravisit::{FnKind, Visitor},
};
use rustc_middle::{
    hir::nested_filter,
    ty::{TyCtxt, TyKind},
};
use rustc_span::{Span, Symbol};
use std::collections::{HashMap, HashSet};
use syn::Expr;

use super::{
    attribute::assets_parser::*,
    attribute::attr_parser::parse_rapx_attr,
    contract::Property,
    helpers::{Callsite, collect_unsafe_callsites},
    path::{PathExtractor, PathStart},
};

/// A list of parsed `requires` contracts.
pub type FnContracts<'tcx> = Vec<Property<'tcx>>;

/// A list of parsed struct invariants.
pub type StructInvariants<'tcx> = Vec<Property<'tcx>>;

/// Collected verification data for a function annotated with `#[rapx::verify]`.
#[derive(Clone)]
pub struct FunctionTarget<'tcx> {
    /// Function marked with `#[rapx::verify]` and selected as a target to verify.
    pub def_id: DefId,
    /// Owning struct definition when this target to verify is an associated method.
    pub owner_struct_def_id: Option<DefId>,
    /// Concrete unsafe callsites collected from the target MIR body.
    pub callsites: Vec<Callsite<'tcx>>,
    /// Parsed `requires` contracts for each unsafe callee reachable from this target.
    pub callee_requires: HashMap<DefId, FnContracts<'tcx>>,
}

/// Collected verification data for a struct that owns methods marked with `#[rapx::verify]`.
pub struct StructTarget<'tcx> {
    /// Struct that owns one or more methods selected as targets to verify.
    pub def_id: DefId,
    /// Parsed `invariant` contracts attached to the struct.
    pub invariants: StructInvariants<'tcx>,
    /// Methods of this struct selected as targets to verify.
    pub function_targets: Vec<FunctionTarget<'tcx>>,
}

/// Visitor that collects targets annotated with `#[rapx::verify]`.
pub struct VerifyTargetCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// All function targets to verify collected from the current crate.
    pub function_targets: Vec<FunctionTarget<'tcx>>,
    /// All struct targets to verify collected from the current crate.
    pub struct_targets: HashMap<DefId, StructTarget<'tcx>>,
    /// Cached contracts for each callee function so repeated callees are parsed once.
    fn_contract_cache: HashMap<DefId, FnContracts<'tcx>>,
}

impl<'tcx> VerifyTargetCollector<'tcx> {
    /// Creates a new collector for the current type context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        VerifyTargetCollector {
            tcx,
            function_targets: Vec::new(),
            struct_targets: HashMap::new(),
            fn_contract_cache: HashMap::new(),
        }
    }

    /// Returns whether the given definition belongs to a standard Rust crate.
    fn is_std_crate_def_id(&self, def_id: DefId) -> bool {
        matches!(
            self.tcx.crate_name(def_id.krate).as_str(),
            "core" | "std" | "alloc"
        )
    }

    /// Returns (and caches) the contracts for an unsafe callee.
    ///
    /// Contracts are resolved with the following priority:
    /// 1. Inline RAPx annotations attached to the callee.
    /// 2. If no annotations are found and the callee belongs to the standard
    ///    library, fall back to the bundled JSON contract database.
    ///
    /// Results are memoized in `fn_contract_cache` to avoid recomputation.
    fn get_fn_contracts(&mut self, callee_def_id: DefId) -> FnContracts<'tcx> {
        let is_std = self.is_std_crate_def_id(callee_def_id);
        self.fn_contract_cache
            .entry(callee_def_id)
            .or_insert_with(|| {
                // Try to collect contracts from inline RAPx annotations first.
                let mut requires = get_contract_from_annotation(self.tcx, callee_def_id);

                // If no annotation is found and this is a std item,
                // fall back to the precomputed JSON contracts.
                if requires.is_empty() && is_std {
                    requires = get_contract_from_entry(
                        self.tcx,
                        callee_def_id,
                        get_std_contracts_from_assets(self.tcx, callee_def_id),
                    );
                }

                requires
            })
            // `entry` returns a mutable reference; clone to return an owned value.
            .clone()
    }

    /// Checks whether a local function has the exact tool attribute `#[rapx::verify]`.
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

    /// Builds a function target to verify from a function definition.
    fn build_function_target(&mut self, def_id: DefId) -> FunctionTarget<'tcx> {
        let callsites = collect_unsafe_callsites(self.tcx, def_id);
        let unsafe_callees: HashSet<_> = callsites.iter().map(|callsite| callsite.callee).collect();
        let callee_requires = unsafe_callees
            .iter()
            .map(|callee_def_id| (*callee_def_id, self.get_fn_contracts(*callee_def_id)))
            .collect();

        FunctionTarget {
            def_id,
            owner_struct_def_id: self.get_owner_struct_def_id(def_id),
            callsites,
            callee_requires,
        }
    }

    /// Returns the owning struct definition when the function is a method on a struct.
    fn get_owner_struct_def_id(&self, def_id: DefId) -> Option<DefId> {
        let assoc_item = self.tcx.opt_associated_item(def_id)?;
        let impl_id = assoc_item.impl_container(self.tcx)?;
        let self_ty = self.tcx.type_of(impl_id).skip_binder();

        match self_ty.kind() {
            TyKind::Adt(adt_def, _) => Some(adt_def.did()),
            _ => None,
        }
    }

    /// Adds a function target and updates its owning struct target when applicable.
    fn push_function_target(&mut self, function_target: FunctionTarget<'tcx>) {
        self.function_targets.push(function_target.clone());

        if let Some(struct_def_id) = function_target.owner_struct_def_id {
            self.struct_targets
                .entry(struct_def_id)
                .or_insert_with(|| StructTarget {
                    def_id: struct_def_id,
                    invariants: get_struct_invariants_from_annotation(
                        self.tcx,
                        struct_def_id,
                        function_target.def_id,
                    ),
                    function_targets: Vec::new(),
                })
                .function_targets
                .push(function_target);
        }
    }
}

impl<'tcx> Visitor<'tcx> for VerifyTargetCollector<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    /// Visits each function body and records those annotated with `#[rapx::verify]`.
    ///
    /// For every function target to verify, this also computes its unsafe callees
    /// and the safety preconditions required by those callees.
    fn visit_fn(
        &mut self,
        _fk: FnKind<'tcx>,
        _fd: &'tcx FnDecl<'tcx>,
        _b: BodyId,
        _span: Span,
        id: LocalDefId,
    ) -> Self::Result {
        if self.has_rapx_verify_attr(id) {
            let def_id = id.to_def_id();
            let function_target = self.build_function_target(def_id);
            self.push_function_target(function_target);
        }
    }
}

/// Analysis pass that finds all targets annotated with `#[rapx::verify]`.
pub struct PrepareTargets<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Analysis for PrepareTargets<'tcx> {
    fn name(&self) -> &'static str {
        "Verify Identify Targets Analysis"
    }

    /// Runs the collection pass and logs targets, struct invariants, unsafe callees, and contracts.
    fn run(&mut self) {
        rap_info!("======== #[rapx::verify] identify targets ========");
        let mut collector = VerifyTargetCollector::new(self.tcx);
        self.tcx.hir_visit_all_item_likes_in_crate(&mut collector);

        for function_target in collector
            .function_targets
            .iter()
            .filter(|target| target.owner_struct_def_id.is_none())
        {
            self.log_function_target(function_target, false);
        }

        let mut struct_ids: Vec<_> = collector.struct_targets.keys().copied().collect();
        struct_ids.sort_by_key(|def_id| self.tcx.def_path_str(*def_id));

        for struct_def_id in struct_ids {
            let Some(struct_target) = collector.struct_targets.get(&struct_def_id) else {
                continue;
            };
            let struct_path = self.tcx.def_path_str(struct_target.def_id);
            rap_info!(
                "[rapx::verify::identify-targets] struct target: {} (DefId: {:?})",
                struct_path,
                struct_target.def_id
            );

            if struct_target.invariants.is_empty() {
                rap_info!("  struct invariants: <none>");
            } else {
                for property in &struct_target.invariants {
                    rap_info!(
                        "  struct invariant: kind={:?}, args={:?}",
                        property.kind,
                        property.args
                    );
                }
            }

            for function_target in &struct_target.function_targets {
                self.log_function_target(function_target, true);
            }
        }

        let total_free_function_targets = collector
            .function_targets
            .iter()
            .filter(|target| target.owner_struct_def_id.is_none())
            .count();
        let total_method_targets = collector
            .function_targets
            .iter()
            .filter(|target| target.owner_struct_def_id.is_some())
            .count();
        let total_struct_targets = collector.struct_targets.len();

        rap_info!(
            "total: {} free function target(s) to verify, {} method target(s) to verify, {} struct target(s) to verify",
            total_free_function_targets,
            total_method_targets,
            total_struct_targets
        );
        rap_info!("=======================================");
    }

    fn reset(&mut self) {}
}

impl<'tcx> PrepareTargets<'tcx> {
    /// Creates a new analysis instance.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        PrepareTargets { tcx }
    }

    /// Logs one function target and all contracts collected from its unsafe callees.
    fn log_function_target(&self, target: &FunctionTarget<'tcx>, nested_under_struct: bool) {
        let target_path = self.tcx.def_path_str(target.def_id);
        let prefix = if nested_under_struct {
            "  method target"
        } else {
            "[rapx::verify::identify-targets] function target"
        };
        rap_info!("{}: {} (DefId: {:?})", prefix, target_path, target.def_id);

        if let Some(struct_def_id) = target.owner_struct_def_id {
            let struct_path = self.tcx.def_path_str(struct_def_id);
            rap_info!(
                "    owner struct: {} (DefId: {:?})",
                struct_path,
                struct_def_id
            );
        }

        if target.callee_requires.is_empty() {
            rap_info!("    unsafe callees: <none>");
            return;
        }

        let mut unsafe_callee_ids: Vec<_> = target.callee_requires.keys().copied().collect();
        unsafe_callee_ids.sort_by_key(|def_id| self.tcx.def_path_str(*def_id));

        for unsafe_callee_def_id in unsafe_callee_ids {
            let unsafe_callee_path = self.tcx.def_path_str(unsafe_callee_def_id);
            rap_info!(
                "    unsafe callee: {} (DefId: {:?})",
                unsafe_callee_path,
                unsafe_callee_def_id
            );

            match target.callee_requires.get(&unsafe_callee_def_id) {
                Some(requires) if !requires.is_empty() => {
                    for property in requires {
                        rap_info!(
                            "      safety contract: kind={:?}, args={:?}",
                            property.kind,
                            property.args
                        );
                    }
                }
                _ => {
                    rap_info!("      safety contract: <none>");
                }
            }
        }

        self.log_function_paths(target);
    }

    /// Logs unsafe callsites and SCC-aware path skeletons for one target.
    fn log_function_paths(&self, target: &FunctionTarget<'tcx>) {
        if target.callsites.is_empty() {
            rap_info!("    unsafe callsites: <none>");
            return;
        }

        let result = PathExtractor::new(self.tcx, target.def_id, target.callsites.clone()).run();

        rap_info!("    detected SCC region(s): {}", result.scc_regions().len());
        for scc_info in result.scc_regions() {
            let body: Vec<_> = scc_info
                .blocks
                .iter()
                .map(|bb| format!("bb{}", bb.as_usize()))
                .collect();
            let exits: Vec<_> = scc_info
                .exits
                .iter()
                .map(|exit| format!("bb{}->bb{}", exit.from.as_usize(), exit.to.as_usize()))
                .collect();
            rap_info!(
                "      SCC bb{}: body={:?}, exits={:?}",
                scc_info.representative.as_usize(),
                body,
                exits
            );
        }

        for (display_index, callsite) in result.callsites().iter().enumerate() {
            rap_info!(
                "    unsafe callsite #{}: {} at bb{} ({} arg(s))",
                display_index,
                callsite.callee_name(self.tcx),
                callsite.block.as_usize(),
                callsite.args.len()
            );

            let mut callsite_paths: Vec<_> = result.paths_for(callsite.location()).iter().collect();
            callsite_paths.sort_by_key(|path| path.describe());

            if callsite_paths.is_empty() {
                rap_info!("      paths: <none>");
                continue;
            }

            for (path_idx, path) in callsite_paths.iter().enumerate() {
                let kind = match path.start {
                    PathStart::FunctionEntry => "entry",
                    PathStart::SccRepresentative { representative } => {
                        rap_info!(
                            "      path {} kind: scc-representative(bb{})",
                            path_idx,
                            representative.as_usize()
                        );
                        rap_info!("      path {}: {}", path_idx, path.describe());
                        continue;
                    }
                };
                rap_info!("      path {} kind: {}", path_idx, kind);
                rap_info!("      path {}: {}", path_idx, path.describe());
            }
        }
    }
}

/// Builds contracts from backup JSON entries.
///
/// Each entry stores property-expression arguments that are passed directly into
/// `Property::new`. The target information is resolved by `Property` itself
/// from those arguments.
fn get_contract_from_entry<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    contract_entries: &[PropertyEntry],
) -> FnContracts<'tcx> {
    let mut results = Vec::new();
    for entry in contract_entries {
        if entry.args.is_empty() {
            continue;
        }

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

        let property = Property::new(tcx, def_id, entry.tag.as_str(), &exprs);
        results.push(property);
    }
    results
}

/// Returns whether an attribute is exactly `#[rapx::requires(...)]`.
fn is_rapx_requires_attr(attr: &Attribute) -> bool {
    matches!(
        attr,
        Attribute::Unparsed(tool_attr)
            if tool_attr.path.segments.len() == 2
                && tool_attr.path.segments[0].as_str() == "rapx"
                && tool_attr.path.segments[1].as_str() == "requires"
    )
}

/// Collects properties from `#[rapx::requires(...)]` attributes.
fn collect_properties_from_requires_attrs<'tcx>(
    tcx: TyCtxt<'tcx>,
    attrs: impl IntoIterator<Item = &'tcx Attribute>,
    property_def_id: DefId,
    parse_error_label: &str,
) -> Vec<Property<'tcx>> {
    let mut results = Vec::new();

    for attr in attrs {
        if !is_rapx_requires_attr(attr) {
            continue;
        }

        let attr_str = rustc_hir_pretty::attribute_to_string(&tcx, attr);
        let parsed = match parse_rapx_attr(attr_str.as_str(), "requires") {
            Ok(parsed) => parsed,
            Err(err) => {
                rap_error!(
                    "Failed to parse RAPx {} attr '{}': {}",
                    parse_error_label,
                    attr_str,
                    err
                );
                continue;
            }
        };

        results.extend(parsed.properties.into_iter().map(|property| {
            Property::new(tcx, property_def_id, property.tag.as_str(), &property.args)
        }));
    }

    results
}

/// Parses `requires` contracts from source-level RAPx annotations attached to a definition.
fn get_contract_from_annotation<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> FnContracts<'tcx> {
    collect_properties_from_requires_attrs(tcx, tcx.get_all_attrs(def_id), def_id, "requires")
}

/// Parses struct invariants from source-level RAPx annotations attached to a struct definition.
fn get_struct_invariants_from_annotation<'tcx>(
    tcx: TyCtxt<'tcx>,
    struct_def_id: DefId,
    context_def_id: DefId,
) -> StructInvariants<'tcx> {
    let Some(local_def_id) = struct_def_id.as_local() else {
        return Vec::new();
    };

    let item = tcx.hir_expect_item(local_def_id);
    if !matches!(item.kind, ItemKind::Struct(..)) {
        return Vec::new();
    }

    collect_properties_from_requires_attrs(
        tcx,
        tcx.get_all_attrs(struct_def_id),
        context_def_id,
        "invariant",
    )
}
