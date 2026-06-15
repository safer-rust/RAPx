use crate::analysis::Analysis;
use crate::cli::VerifyMode;
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
    helpers::{Callsite, collect_return_block_indices, collect_unsafe_callsites},
    path::PathExtractor,
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
    /// Parsed struct invariants that methods of the owning struct must maintain.
    pub struct_invariants: Vec<Property<'tcx>>,
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
    mode: VerifyMode,
    /// All function targets to verify collected from the current crate.
    pub function_targets: Vec<FunctionTarget<'tcx>>,
    /// All struct targets to verify collected from the current crate.
    pub struct_targets: HashMap<DefId, StructTarget<'tcx>>,
    /// Cached contracts for each callee function so repeated callees are parsed once.
    fn_contract_cache: HashMap<DefId, FnContracts<'tcx>>,
}

impl<'tcx> VerifyTargetCollector<'tcx> {
    /// Creates a new collector for the current type context.
    pub fn new(tcx: TyCtxt<'tcx>, mode: VerifyMode) -> Self {
        VerifyTargetCollector {
            tcx,
            mode,
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

        let owner_struct_def_id = self.get_owner_struct_def_id(def_id);
        let struct_invariants = owner_struct_def_id
            .map(|struct_def_id| {
                get_struct_invariants_from_annotation(self.tcx, struct_def_id, def_id)
            })
            .unwrap_or_default();

        FunctionTarget {
            def_id,
            owner_struct_def_id,
            callsites,
            callee_requires,
            struct_invariants,
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

    /// Visits each function body and records verification targets.
    ///
    /// In `targeted` mode, only functions annotated with `#[rapx::verify]` are collected.
    /// In `all` and `invariantless` modes, every function with an unsafe callee is collected
    /// (plus struct invariants where applicable, except in `invariantless` mode).
    fn visit_fn(
        &mut self,
        _fk: FnKind<'tcx>,
        _fd: &'tcx FnDecl<'tcx>,
        _b: BodyId,
        _span: Span,
        id: LocalDefId,
    ) -> Self::Result {
        if matches!(self.mode, VerifyMode::Targeted) && !self.has_rapx_verify_attr(id) {
            return;
        }

        let def_id = id.to_def_id();
        let function_target = self.build_function_target(def_id);

        match self.mode {
            VerifyMode::Targeted => {}
            VerifyMode::All => {
                if function_target.callsites.is_empty()
                    && function_target.struct_invariants.is_empty()
                {
                    return;
                }
            }
            VerifyMode::Invariantless => {
                // TODO: skip struct invariant checks during verification.
                // For now, target collection works like `all` but ignores invariants.
                if function_target.callsites.is_empty() {
                    return;
                }
            }
        }

        self.push_function_target(function_target);
    }
}

/// Analysis pass that finds all verification targets.
///
/// In `targeted` mode, only functions annotated with `#[rapx::verify]` are listed.
/// In `all` mode, all functions with unsafe callees or struct invariants are listed.
pub struct PrepareTargets<'tcx> {
    tcx: TyCtxt<'tcx>,
    mode: VerifyMode,
}

impl<'tcx> Analysis for PrepareTargets<'tcx> {
    fn name(&self) -> &'static str {
        "Verify Identify Targets Analysis"
    }

    fn run(&mut self) {
        let mut collector = VerifyTargetCollector::new(self.tcx, self.mode);
        self.tcx.hir_visit_all_item_likes_in_crate(&mut collector);

        // Free functions (no owning struct)
        let free_targets: Vec<_> = collector
            .function_targets
            .iter()
            .filter(|target| target.owner_struct_def_id.is_none())
            .collect();
        for target in &free_targets {
            let target_path = self.tcx.def_path_str(target.def_id);
            rap_info!("============================================================");
            rap_info!(
                "[rapx::verify] prepare targets for free function: {}",
                target_path
            );
            rap_info!("============================================================");
            self.log_free_function_unsafe_callees(target);
            rap_info!("");
        }

        // Structs with methods
        let mut struct_ids: Vec<_> = collector.struct_targets.keys().copied().collect();
        struct_ids.sort_by_key(|def_id| self.tcx.def_path_str(*def_id));

        for struct_def_id in struct_ids {
            let Some(struct_target) = collector.struct_targets.get(&struct_def_id) else {
                continue;
            };
            let struct_path = self.tcx.def_path_str(struct_target.def_id);

            rap_info!("============================================================");
            rap_info!("[rapx::verify] prepare targets for struct: {}", struct_path);
            rap_info!("============================================================");

            self.log_struct_invariants(struct_target);

            for target in &struct_target.function_targets {
                self.log_method_target(target);
            }

            rap_info!("");
        }

        let total_free = free_targets.len();
        let total_method = collector
            .function_targets
            .iter()
            .filter(|target| target.owner_struct_def_id.is_some())
            .count();
        let total_struct = collector.struct_targets.len();

        rap_info!("============================================================");
        rap_info!(
            "[rapx::verify] total: {} free function(s), {} method(s), {} struct(s)",
            total_free,
            total_method,
            total_struct
        );
        rap_info!("============================================================");
    }

    fn reset(&mut self) {}
}

impl<'tcx> PrepareTargets<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, mode: VerifyMode) -> Self {
        PrepareTargets { tcx, mode }
    }

    fn log_struct_invariants(&self, struct_target: &StructTarget<'tcx>) {
        if struct_target.invariants.is_empty() {
            rap_info!("  struct invariants: <none>");
        } else {
            rap_info!("  struct invariants:");
            for property in &struct_target.invariants {
                rap_info!("    - {:?}, args={:?}", property.kind, property.args);
            }
        }
    }

    fn log_method_target(&self, target: &FunctionTarget<'tcx>) {
        let target_path = self.tcx.def_path_str(target.def_id);
        let name = target_path.rsplit("::").next().unwrap_or(&target_path);
        let dashes = 62usize.saturating_sub(10 + name.len());
        rap_info!("  --- method: {name} {}", "-".repeat(dashes));

        let return_blocks = collect_return_block_indices(self.tcx, target.def_id);
        rap_info!(
            "      return checkpoints: {} block(s) {:?}",
            return_blocks.len(),
            return_blocks
                .iter()
                .map(|bb| bb.as_usize())
                .collect::<Vec<_>>()
        );

        self.log_unsafe_callees_and_contracts(target);
        self.log_callsite_paths(target);
    }

    fn log_free_function_unsafe_callees(&self, target: &FunctionTarget<'tcx>) {
        self.log_unsafe_callees_and_contracts(target);
        self.log_callsite_paths(target);
    }

    fn log_unsafe_callees_and_contracts(&self, target: &FunctionTarget<'tcx>) {
        if target.callee_requires.is_empty() {
            rap_info!("      unsafe callsites: <none>");
            return;
        }

        let mut unsafe_callee_ids: Vec<_> = target.callee_requires.keys().copied().collect();
        unsafe_callee_ids.sort_by_key(|def_id| self.tcx.def_path_str(*def_id));

        for unsafe_callee_def_id in unsafe_callee_ids {
            let unsafe_callee_path = self.tcx.def_path_str(unsafe_callee_def_id);
            rap_info!("      unsafe callee: {}", unsafe_callee_path,);

            if let Some(requires) = target.callee_requires.get(&unsafe_callee_def_id) {
                if requires.is_empty() {
                    rap_info!("        safety contracts: <none>");
                } else {
                    rap_info!("        safety contracts:");
                    for property in requires {
                        rap_info!("          - {:?}, args={:?}", property.kind, property.args);
                    }
                }
            }
        }
    }

    fn log_callsite_paths(&self, target: &FunctionTarget<'tcx>) {
        if target.callsites.is_empty() {
            return;
        }

        let result = PathExtractor::new(self.tcx, target.def_id, target.callsites.clone(), 0).run();
        rap_info!("      callsite paths:");
        for (display_index, callsite) in result.callsites().iter().enumerate() {
            rap_info!(
                "        #{} {} at bb{} ({} arg(s))",
                display_index,
                callsite.callee_name(self.tcx),
                callsite.block.as_usize(),
                callsite.args.len()
            );

            let mut callsite_paths: Vec<_> = result.paths_for(callsite.location()).iter().collect();
            callsite_paths.sort_by_key(|path| path.describe());

            if callsite_paths.is_empty() {
                rap_info!("          paths: <none>");
                continue;
            }

            for (path_idx, path) in callsite_paths.iter().enumerate() {
                rap_info!("          path {}: {}", path_idx, path.describe());
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

fn is_rapx_named_attr(attr: &Attribute, name: &str) -> bool {
    matches!(
        attr,
        Attribute::Unparsed(tool_attr)
            if tool_attr.path.segments.len() == 2
                && tool_attr.path.segments[0].as_str() == "rapx"
                && tool_attr.path.segments[1].as_str() == name
    )
}

/// Collects properties from `#[rapx::requires(...)]` attributes.
fn collect_properties_from_requires_attrs<'tcx>(
    tcx: TyCtxt<'tcx>,
    attrs: impl IntoIterator<Item = &'tcx Attribute>,
    property_def_id: DefId,
    parse_error_label: &str,
) -> Vec<Property<'tcx>> {
    collect_properties_from_named_attrs(tcx, attrs, property_def_id, parse_error_label, "requires")
}

/// Collects properties from `#[rapx::invariant(...)]` attributes.
fn collect_properties_from_invariant_attrs<'tcx>(
    tcx: TyCtxt<'tcx>,
    attrs: impl IntoIterator<Item = &'tcx Attribute>,
    property_def_id: DefId,
    parse_error_label: &str,
) -> Vec<Property<'tcx>> {
    collect_properties_from_named_attrs(tcx, attrs, property_def_id, parse_error_label, "invariant")
}

fn collect_properties_from_named_attrs<'tcx>(
    tcx: TyCtxt<'tcx>,
    attrs: impl IntoIterator<Item = &'tcx Attribute>,
    property_def_id: DefId,
    parse_error_label: &str,
    attr_name: &str,
) -> Vec<Property<'tcx>> {
    let mut results = Vec::new();

    for attr in attrs {
        if !is_rapx_named_attr(attr, attr_name) {
            continue;
        }

        let attr_str = rustc_hir_pretty::attribute_to_string(&tcx, attr);
        let parsed = match parse_rapx_attr(attr_str.as_str(), attr_name) {
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

    let mut invariants = collect_properties_from_requires_attrs(
        tcx,
        tcx.get_all_attrs(struct_def_id),
        context_def_id,
        "invariant",
    );
    invariants.extend(collect_properties_from_invariant_attrs(
        tcx,
        tcx.get_all_attrs(struct_def_id),
        context_def_id,
        "invariant",
    ));
    invariants
}
