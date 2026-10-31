use crate::analysis::path::{CallBinding, CallConstArg, PathTree};
use crate::compat::{FxHashMap, FxHashSet};
use crate::helpers::mir_utils;
use crate::limit::{HINTED_CALLEE_BLOCK_LIMIT, LOCAL_CALLEE_BLOCK_LIMIT};
use crate::verify::target::CalleeBodies;
#[cfg(rapx_has_attr_ir)]
use rustc_attr_ir::InlineAttr;
#[cfg(not(rapx_has_attr_ir))]
use rustc_hir::attrs::InlineAttr;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Operand, Terminator, TerminatorKind},
    ty::{EarlyBinder, Instance, InstanceKind, TyCtxt, TyKind, TypingEnv},
};

/// Maps callsites to callee block identities and argument bindings.
pub(crate) struct CallSiteIndex<'tcx> {
    tcx: TyCtxt<'tcx>,
    blocks: Vec<(DefId, usize)>,
    bodies: FxHashMap<usize, Body<'tcx>>,
    instances: FxHashMap<usize, Instance<'tcx>>,
    callee_bodies: CalleeBodies<'tcx>,
    bindings: FxHashMap<usize, CallBinding>,
    pub(crate) entries: FxHashMap<usize, Vec<usize>>,
}

impl<'tcx> CallSiteIndex<'tcx> {
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        root: DefId,
        body: Option<Body<'tcx>>,
        callee_bodies: CalleeBodies<'tcx>,
    ) -> Self {
        let block_count = body
            .as_ref()
            .map(|body| body.basic_blocks.len())
            .unwrap_or_else(|| tcx.optimized_mir(root).basic_blocks.len());
        let blocks = (0..block_count)
            .map(|index| (root, index))
            .collect();
        let mut bodies = FxHashMap::default();
        if let Some(body) = body {
            bodies.insert(0, body);
        }
        Self {
            tcx,
            blocks,
            bodies,
            instances: FxHashMap::default(),
            callee_bodies,
            bindings: FxHashMap::default(),
            entries: FxHashMap::default(),
        }
    }

    pub(crate) fn attach_metadata(self, tree: &mut PathTree) {
        let mut parents = FxHashMap::default();
        for (&call_block, entries) in &self.entries {
            let parent = self.blocks[call_block].0;
            for &entry in entries {
                parents.insert(entry, parent);
            }
        }
        let expanded_calls = self.entries.keys().copied().collect();
        tree.set_block_metadata(self.blocks, self.bindings, parents, expanded_calls);
    }

    pub(crate) fn blocks(&self) -> &[(DefId, usize)] {
        &self.blocks
    }

    pub(crate) fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub(crate) fn body(&self, block: usize) -> &Body<'tcx> {
        let (def_id, local) = self.blocks[block];
        self.bodies
            .get(&(block - local))
            .unwrap_or_else(|| self.tcx.optimized_mir(def_id))
    }

    pub(crate) fn has_body_override(&self, entry: usize) -> bool {
        self.bodies.contains_key(&entry)
    }

    pub(crate) fn unambiguous_bodies(&self) -> CalleeBodies<'tcx> {
        let mut bodies = self.callee_bodies.clone();
        let mut chosen = FxHashMap::default();
        let mut conflicting = FxHashSet::default();
        for (&entry, &instance) in &self.instances {
            let callee = self.blocks[entry].0;
            if let Some(previous) = chosen.insert(callee, (instance, entry))
                && previous.0 != instance
            {
                conflicting.insert(callee);
            }
        }
        for &entry in self.bindings.keys() {
            let callee = self.blocks[entry].0;
            if chosen.contains_key(&callee) && !self.instances.contains_key(&entry) {
                conflicting.insert(callee);
            }
        }
        for (callee, (_, entry)) in chosen {
            if !conflicting.contains(&callee)
                && let Some(body) = self.bodies.get(&entry)
            {
                bodies.insert(callee, &*self.tcx.arena.alloc(body.clone()));
            }
        }
        for callee in conflicting {
            bodies.remove(&callee);
        }
        bodies
    }

    fn terminator(&self, block: usize) -> Option<&Terminator<'tcx>> {
        let (_, local) = self.blocks[block];
        self.body(block)
            .basic_blocks
            .get(BasicBlock::from(local))
            .and_then(|data| data.terminator.as_ref())
    }

    pub(crate) fn normal_successor(&self, block: usize) -> Option<usize> {
        let (_, local) = self.blocks[block];
        let TerminatorKind::Call {
            target: Some(target),
            ..
        } = &self.terminator(block)?.kind
        else {
            return None;
        };
        Some(block - local + target.as_usize())
    }

    pub(crate) fn collect(&mut self) {
        let mut expanded = FxHashSet::default();
        expanded.insert(self.blocks[0].0);
        let mut next_block = 0;
        loop {
            let block_count = self.blocks.len();
            let mut pending = Vec::new();
            for block in next_block..block_count {
                let Some(terminator) = self.terminator(block) else {
                    continue;
                };
                let TerminatorKind::Call {
                    func,
                    target: Some(_),
                    ..
                } = &terminator.kind
                else {
                    continue;
                };
                let Some(base_callee) = mir_utils::dep_callee_def_id(func) else {
                    continue;
                };
                let actual_caller = self.blocks[block].0;
                // Bodies instantiated under the root retain its unresolved
                // generic arguments (not the callee's parameter indices).
                let caller = if self.callee_bodies.contains_key(&actual_caller) {
                    self.blocks[0].0
                } else {
                    actual_caller
                };
                let cross_crate = base_callee.as_local().is_none();
                let is_trait_method = self
                    .tcx
                    .opt_associated_item(base_callee)
                    .and_then(|item| item.trait_container(self.tcx))
                    .is_some();
                let registry_handled = crate::verify::call_summary::effects::has_registry_entry(Some(
                    base_callee,
                )) || crate::verify::target::has_slice_offset_ensures(self.tcx, base_callee);
                let resolve_to_impl = !cross_crate || !is_trait_method || !registry_handled;
                if caller.as_local().is_none() && !(is_trait_method && resolve_to_impl) {
                    continue;
                }
                let callee = if resolve_to_impl {
                    mir_utils::dep_callee_resolved_def_id(self.tcx, caller, func)
                        .unwrap_or(base_callee)
                } else {
                    base_callee
                };
                if !crate::verify::options::should_inline_constructor(self.tcx, callee) {
                    continue;
                }
                // An instantiated root can resolve Clone at this callsite.
                // Leave the call in the path so the VM executes that exact MIR.
                if self.bodies.contains_key(&0)
                    && crate::def_ids::nomir_api::clone() == Some(base_callee)
                    && mir_utils::resolve_callee_instance(self.tcx, caller, func).is_some_and(
                        |instance| {
                            matches!(instance.def, InstanceKind::Item(_))
                                && instance.def_id() == callee
                                && instance
                                    .args
                                    .types()
                                    .all(|ty| !mir_utils::ty_has_type_param(ty))
                        },
                    )
                    && self.tcx.is_mir_available(callee)
                {
                    continue;
                }
                if is_trait_method {
                    let is_virtual = mir_utils::resolve_callee_instance(self.tcx, caller, func)
                        .is_some_and(|instance| mir_utils::instance_def_id(self.tcx, instance).1);
                    if is_virtual {
                        if !registry_handled {
                            for candidate in mir_utils::trait_impl_candidates(self.tcx, base_callee)
                                .into_iter()
                                .take(crate::limit::trait_impl_limit())
                            {
                                if self.tcx.is_mir_available(candidate)
                                    && !expanded.contains(&candidate)
                                {
                                    pending.push((block, candidate, None));
                                }
                            }
                        }
                        continue;
                    }
                }
                let generic_const_call = cross_crate
                    && mir_utils::has_generic_const_call_argument(self.tcx, callee);
                let returns_adt = self.tcx.is_mir_available(callee)
                    && matches!(
                        self.tcx.optimized_mir(callee).return_ty().kind(),
                        TyKind::Adt(..)
                    );
                let instantiate = self.tcx.is_mir_available(callee)
                    && ((cross_crate
                    && (crate::def_ids::other_api::is_slice_get(Some(base_callee))
                        || (returns_adt && (mir_utils::has_unmodeled_generic_call(self.tcx, callee)
                            || generic_const_call))))
                        || self.tcx.optimized_mir(callee).basic_blocks.len() == 1
                        || (self.tcx.optimized_mir(callee).basic_blocks.len() == 2
                            && returns_adt));
                let instance = instantiate
                    .then(|| mir_utils::resolve_callee_instance(self.tcx, caller, func))
                    .flatten()
                    .filter(|instance| {
                        matches!(instance.def, InstanceKind::Item(_))
                            && instance.def_id() == callee
                            && !instance.args.is_empty()
                            && instance.args.types().all(|ty| !mir_utils::ty_has_type_param(ty))
                            && instance.args.consts().all(|c| {
                                !matches!(c.kind(), rustc_middle::ty::ConstKind::Param(_))
                            })
                    });
                if generic_const_call && instance.is_none() && returns_adt {
                    continue;
                }
                let cross_crate_trait_default =
                    cross_crate && is_trait_method && self.tcx.is_mir_available(base_callee);
                if crate::def_ids::intrinsic_api::is_intrinsic(self.tcx, callee)
                    || !self.tcx.is_mir_available(callee)
                    || expanded.contains(&callee)
                    || (crate::verify::call_summary::effects::has_registry_entry(Some(callee))
                        && !crate::verify::options::force_inline_constructor(self.tcx, callee))
                    || crate::verify::target::has_slice_offset_ensures(self.tcx, callee)
                    || crate::def_ids::other_api::is_ub_check(self.tcx, callee)
                    || cross_crate_trait_default
                {
                    continue;
                }
                let small_local = !cross_crate && {
                    let limit = if matches!(
                        self.tcx.codegen_fn_attrs(callee).inline,
                        InlineAttr::Hint | InlineAttr::Always
                    ) {
                        HINTED_CALLEE_BLOCK_LIMIT
                    } else {
                        LOCAL_CALLEE_BLOCK_LIMIT
                    };
                    self.tcx.optimized_mir(callee).basic_blocks.len() <= limit
                };
                if cross_crate || small_local {
                    pending.push((block, callee, instance));
                }
            }
            next_block = block_count;
            if pending.is_empty() {
                break;
            }
            for (_, callee, _) in &pending {
                expanded.insert(*callee);
            }
            for (block, callee, instance) in pending {
                self.insert(block, callee, instance);
            }
        }
        for entries in self.entries.values_mut() {
            entries.sort_unstable();
        }
    }

    fn insert(&mut self, call_block: usize, callee: DefId, instance: Option<Instance<'tcx>>) {
        let Some(terminator) = self.terminator(call_block) else {
            return;
        };
        let TerminatorKind::Call {
            args, destination, ..
        } = &terminator.kind
        else {
            return;
        };
        let arg_locals = args
            .iter()
            .filter_map(|arg| arg.node.place().map(|place| place.local.as_usize()))
            .collect();
        let arg_consts = args
            .iter()
            .enumerate()
            .filter_map(|(index, arg)| {
                if let Some(value) = mir_utils::operand_const_u64(&arg.node) {
                    return Some((index + 1, CallConstArg::Literal(value)));
                }
                let Operand::Constant(constant) = &arg.node else {
                    return None;
                };
                let rustc_middle::mir::Const::Ty(_, value) = constant.const_ else {
                    return None;
                };
                matches!(value.kind(), rustc_middle::ty::ConstKind::Param(_)).then(|| {
                    (
                        index + 1,
                        CallConstArg::Symbol(format!("{:?}", constant.const_)),
                    )
                })
            })
            .collect();
        let arg_field_offsets = args
            .iter()
            .enumerate()
            .filter_map(|(index, arg)| {
                let Operand::Constant(constant) = &arg.node else {
                    return None;
                };
                mir_utils::offset_of_container(self.tcx, &constant.const_).map(|_| index + 1)
            })
            .collect();
        let binding = CallBinding {
            arg_locals,
            arg_consts,
            arg_field_offsets,
            dest_local: destination.local.as_usize(),
        };
        let actual_parent = self.blocks[call_block].0;
        let parent = if self.callee_bodies.contains_key(&actual_parent) {
            self.blocks[0].0
        } else {
            actual_parent
        };
        let instantiated_body = instance.map(|instance| {
                let mir = self.tcx.optimized_mir(instance.def_id());
                instance.instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    TypingEnv::post_analysis(self.tcx, parent),
                    EarlyBinder::bind(self.tcx, mir.clone()),
                )
            }).or_else(|| self.callee_bodies.get(&callee).map(|body| (**body).clone()));
        let block_count = instantiated_body
            .as_ref()
            .map(|body| body.basic_blocks.len())
            .unwrap_or_else(|| self.tcx.optimized_mir(callee).basic_blocks.len());
        let entry = self.blocks.len();
        if let Some(instance) = instance {
            self.instances.insert(entry, instance);
        }
        self.blocks
            .extend((0..block_count).map(|local| (callee, local)));
        if let Some(body) = instantiated_body {
            self.bodies.insert(entry, body);
        }
        self.bindings.insert(entry, binding);
        self.entries.entry(call_block).or_default().push(entry);
    }
}
