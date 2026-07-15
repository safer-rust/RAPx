use super::PathTree;
use crate::compat::{FxHashMap, FxHashSet};
use crate::graphs::{
    cfg::{CfgBlock, ControlFlowGraph},
    scc::{Scc, SccInfo},
};
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, BinOp, Local, Operand, Rvalue, StatementKind, SwitchTargets,
        Terminator, TerminatorKind, UnOp, UnwindAction,
    },
    ty::{TyCtxt, TyKind, TypingEnv},
};
use rustc_span::def_id::DefId;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// Maximum number of whole-CFG paths collected before stopping enumeration.
const WHOLE_CFG_PATH_LIMIT: usize = 4000;
/// Maximum DFS depth for whole-CFG path enumeration.
const WHOLE_CFG_PATH_DEPTH_LIMIT: usize = 256;
/// Bounded cache size for SCC path enumeration.
const SCC_PATH_CACHE_LIMIT: usize = 2048;
/// Maximum DFS depth for intra-SCC path enumeration.
const SCC_MAX_DEPTH: usize = 128;
/// Maximum number of distinct paths collected per SCC.
const SCC_MAX_SEEN_PATHS: usize = 128;
/// Maximum path length within an SCC traversal.
const SCC_MAX_PATH_LEN: usize = 200;

/// Check whether the current entry→entry sub-path introduces a new block
/// *sequence* (not just new blocks).  Different branch choices inside the SCC
/// produce different sequences even when all block IDs have already been seen,
/// e.g. `if i % 2 == 0 { A } else { B }` alternates between two paths through
/// the same set of blocks on successive loop iterations.
fn check_postfix_segment(
    path: &[usize],
    enter: usize,
    segment_counts: &mut FxHashMap<Vec<usize>, usize>,
    max_repeats: usize,
) -> bool {
    let segment = extract_segment(path, enter);
    let count = segment_counts.entry(segment).or_insert(0);
    *count += 1;
    *count == 1 || *count - 1 <= max_repeats
}

fn extract_segment(path: &[usize], enter: usize) -> Vec<usize> {
    let prev_pos = path[..path.len() - 1]
        .iter()
        .rposition(|&node| node == enter)
        .unwrap_or(0);
    path[prev_pos + 1..path.len() - 1].to_vec()
}

#[derive(Clone, Debug)]
/// A single enumerated acyclic path through an SCC region.
///
/// `blocks` is the ordered sequence of MIR block indices from the SCC entry
/// to the last block before exiting. The last block may have multiple CFG
/// successors outside the SCC (e.g. a `SwitchInt` branching to different
/// out-of-SCC targets), which are stored in `exit_successors`.
///
/// For example, in a loop with `switch x { A => loop_body, B => done1, C => done2 }`,
/// the corresponding `SccPath` would have `exit_successors = [done1, done2]`
/// — the DFS forks recursively into each of these when constructing whole-CFG paths.
pub struct SccPath {
    pub blocks: Vec<usize>,
    pub exit_successors: Vec<usize>,
}

/// Per-block info collected during construction for path reachability
/// analysis.  Each block's assignments, constants, and copy chains are
/// stored together so they can be read with a single index lookup.
#[derive(Clone, Debug, Default)]
pub struct BlockConstantInfo {
    pub assigned_locals: FxHashSet<usize>,
    pub constants: FxHashMap<usize, usize>,
    pub constraint_copies: FxHashMap<usize, usize>,
    /// Maps a boolean local (e.g., a guard result) to the binary comparison
    /// that produced it: `(op, lhs_local, rhs_kind)`.
    pub comparison_sources: FxHashMap<usize, ComparisonSource>,
    /// Set of locals that are provably non-null (e.g. assigned from
    /// `Box::into_raw`).  Used for path reachability pruning.
    pub known_nonnull_locals: FxHashSet<usize>,
    pub negation_sources: FxHashMap<usize, usize>,
    pub and_sources: FxHashMap<usize, (usize, usize)>,
}
/// Records the origin of a boolean temporary produced by a binary
/// comparison during guard-clause evaluation.
#[derive(Clone, Debug)]
pub struct ComparisonSource {
    pub op: rustc_middle::mir::BinOp,
    pub lhs_local: usize,
    pub rhs_local: usize,
}

/// Encode a `(local, field_index)` pair into a single `usize`.
const AGGREGATE_FIELD_MULT: usize = 256;
const AGGREGATE_FIELD_SENTINEL: usize = 1 << (usize::BITS as usize - 1);

fn encode_aggregate_field(local: usize, field: usize) -> usize {
    debug_assert!(field < AGGREGATE_FIELD_MULT);
    AGGREGATE_FIELD_SENTINEL | (local * AGGREGATE_FIELD_MULT + field)
}

fn decode_aggregate_field(encoded: usize) -> Option<(usize, usize)> {
    if encoded & AGGREGATE_FIELD_SENTINEL == 0 {
        return None;
    }
    let raw = encoded & !AGGREGATE_FIELD_SENTINEL;
    Some((raw / AGGREGATE_FIELD_MULT, raw % AGGREGATE_FIELD_MULT))
}

fn first_field_projection(place: &rustc_middle::mir::Place<'_>) -> Option<usize> {
    for proj in place.projection.iter() {
        if let rustc_middle::mir::ProjectionElem::Field(field, _) = proj {
            return Some(field.as_usize());
        }
    }
    None
}

/// Enum discriminant metadata used by [`check_switch_transition`].
///
/// `source_of` maps a discriminant local to the ADT local it was read from
/// (via `Rvalue::Discriminant`).  `variant_count_of` tracks the number of
/// variants for each ADT local, used to determine whether a `SwitchInt`
/// otherwise-target is uniquely determined.
#[derive(Clone, Debug, Default)]
pub struct DiscriminantInfo {
    pub source_of: FxHashMap<usize, usize>,
    pub variant_count_of: FxHashMap<usize, usize>,
}

/// CFG augmented with per-block constant info and discriminant metadata
/// for path reachability analysis.
///
/// `PathGraph` wraps a `ControlFlowGraph` and adds block-indexed data
/// that track assignments, constants, and copy chains.  These are used by
/// [`check_transition`](PathGraph::check_transition) to update a set of
/// discriminant constraints while traversing the CFG, enabling early
/// pruning of infeasible `SwitchInt` branches during path enumeration.
#[derive(Clone)]
pub struct PathGraph<'tcx> {
    pub cfg: ControlFlowGraph<'tcx>,
    pub block_info: Vec<BlockConstantInfo>,
    pub disc_info: DiscriminantInfo,
    /// Global store: maps encoded `(local, field_idx)` to source local from Aggregates.
    pub aggregate_field_sources: FxHashMap<usize, usize>,
    /// Global store: maps `dest` to `src` for pointer-cast chains.
    pub cast_chains: FxHashMap<usize, usize>,
    /// Global store: maps `_dest` to encoded `(base, field_idx)` from field-projection copies.
    pub field_projection_source: FxHashMap<usize, usize>,
}

impl<'tcx> PathGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> PathGraph<'tcx> {
        let body = tcx.optimized_mir(def_id);
        let basicblocks = &body.basic_blocks;
        let mut cfg_blocks = Vec::<CfgBlock>::new();
        let mut block_info = Vec::new();
        let mut disc_info = DiscriminantInfo::default();
        let mut aggregate_field_sources: FxHashMap<usize, usize> = FxHashMap::default();
        let mut field_projection_source: FxHashMap<usize, usize> = FxHashMap::default();
        let mut cast_chains: FxHashMap<usize, usize> = FxHashMap::default();

        for i in 0..basicblocks.len() {
            let bb = &basicblocks[BasicBlock::from(i)];
            let mut cfg_block = CfgBlock::new(i, bb.is_cleanup);
            let mut info = BlockConstantInfo::default();

            for stmt in &bb.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (place, rvalue) = &**assign;
                    let dest = place.local.as_usize();
                    info.assigned_locals.insert(dest);
                    match rvalue {
                        Rvalue::Use(Operand::Constant(c), ..) => {
                            let typing_env = TypingEnv::post_analysis(tcx, def_id);
                            let val = match c.const_.ty().kind() {
                                TyKind::Bool => c
                                    .const_
                                    .try_eval_bool(tcx, typing_env)
                                    .map(|b| if b { 1 } else { 0 }),
                                TyKind::Int(_) | TyKind::Uint(_) => {
                                    c.const_.try_eval_bits(tcx, typing_env).map(|v| v as usize)
                                }
                                _ => None,
                            };
                            if let Some(val) = val {
                                info.constants.insert(dest, val);
                            }
                        }
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) => {
                            let src_local = src.local.as_usize();
                            if let Some(field_proj) = first_field_projection(src) {
                                let encoded = encode_aggregate_field(src_local, field_proj);
                                field_projection_source.insert(dest, encoded);
                            }
                            info.constraint_copies.insert(dest, src_local);
                        }
                        Rvalue::Discriminant(rv_place) => {
                            disc_info.source_of.insert(dest, rv_place.local.as_usize());
                            let src_local = rv_place.local.as_usize();
                            if !disc_info.variant_count_of.contains_key(&src_local) {
                                let src_ty = body.local_decls[rv_place.local].ty;
                                if let TyKind::Adt(adt_def, _) = src_ty.kind() {
                                    let num = adt_def.variants().len();
                                    if num > 0 {
                                        disc_info.variant_count_of.insert(src_local, num);
                                    }
                                }
                            }
                        }
                        Rvalue::Aggregate(kind, operands) => {
                            if let AggregateKind::Adt(_, _, _, _, _) = kind.as_ref() {
                                let agg_local = place.local.as_usize();
                                for (field_idx, operand) in operands.iter().enumerate() {
                                    if let Operand::Copy(src) | Operand::Move(src) = operand {
                                        let key = encode_aggregate_field(agg_local, field_idx);
                                        let src_local = src.local.as_usize();
                                        aggregate_field_sources.insert(key, src_local);
                                    }
                                }
                            }
                            let discr = match kind.as_ref() {
                                AggregateKind::Adt(_, variant_idx, _, _, _) => {
                                    Some(variant_idx.as_usize())
                                }
                                _ => None,
                            };
                            if let Some(discr) = discr {
                                info.constants.insert(dest, discr);
                                if !disc_info.variant_count_of.contains_key(&dest) {
                                    let dest_ty = body.local_decls[place.local].ty;
                                    if let TyKind::Adt(adt_def, _) = dest_ty.kind() {
                                        let num = adt_def.variants().len();
                                        if num > 0 {
                                            disc_info.variant_count_of.insert(dest, num);
                                        }
                                    }
                                }
                            }
                        }
                        Rvalue::BinaryOp(op, operands)
                            if matches!(
                                op,
                                BinOp::Lt
                                    | BinOp::Le
                                    | BinOp::Gt
                                    | BinOp::Ge
                                    | BinOp::Eq
                                    | BinOp::Ne
                                    | BinOp::BitAnd
                            ) =>
                        {
                            let (lhs, rhs): (&Operand<'_>, &Operand<'_>) =
                                (&operands.0, &operands.1);
                            let lhs_local = match lhs {
                                Operand::Copy(l) | Operand::Move(l) if l.projection.is_empty() => {
                                    Some(l.local.as_usize())
                                }
                                _ => None,
                            };
                            // Allow Constant RHS (e.g. `Ne(ptr, const 0_usize)` for null checks)
                            let rhs_is_zero = match rhs {
                                Operand::Constant(c) => {
                                    let typing_env = TypingEnv::post_analysis(tcx, def_id);
                                    c.const_
                                        .try_eval_bits(tcx, typing_env)
                                        .map(|v| v == 0)
                                        .unwrap_or(false)
                                }
                                _ => false,
                            };
                            if let Some(lhs_local) = lhs_local {
                                let rhs_local = if rhs_is_zero {
                                    0
                                } else {
                                    match rhs {
                                        Operand::Copy(r) | Operand::Move(r)
                                            if r.projection.is_empty() =>
                                        {
                                            r.local.as_usize()
                                        }
                                        _ => {
                                            continue;
                                        }
                                    }
                                };
                                info.comparison_sources.insert(
                                    dest,
                                    ComparisonSource {
                                        op: *op,
                                        lhs_local,
                                        rhs_local,
                                    },
                                );
                                if matches!(op, BinOp::BitAnd)
                                    && matches!(body.local_decls[place.local].ty.kind(), TyKind::Bool)
                                {
                                    info.and_sources.insert(dest, (lhs_local, rhs_local));
                                }
                            }
                        }
                        Rvalue::UnaryOp(unop, operand) => {
                            if matches!(unop, UnOp::Not)
                                && let Operand::Copy(src) | Operand::Move(src) = operand
                            {
                                info.negation_sources.insert(dest, src.local.as_usize());
                            }
                        }
                        Rvalue::Cast(_, operand, _) => {
                            if let Operand::Copy(src) | Operand::Move(src) = operand
                                && matches!(
                                    body.local_decls[place.local].ty.kind(),
                                    TyKind::RawPtr(..) | TyKind::Int(..) | TyKind::Uint(..)
                                )
                            {
                                cast_chains.insert(dest, src.local.as_usize());
                            }
                        }
                        _ => {} // close match rvalue
                    }
                }
            }

            let Some(terminator) = &bb.terminator else {
                cfg_blocks.push(cfg_block);
                block_info.push(info);
                continue;
            };

            if let TerminatorKind::Call { destination, ref func, .. } = terminator.kind {
                let name = super::super::super::verify::call_summary::call_name(tcx, func);
                if name.contains("::into_raw")
                    || (name.contains("::new") && name.contains("Box"))
                {
                    info.known_nonnull_locals.insert(destination.local.as_usize());
                }
                if name.contains("null_mut") || (name.contains("null") && name.contains("ptr::")) {
                    info.constants.insert(destination.local.as_usize(), 0);
                }
            }

            match terminator.kind.clone() {
                TerminatorKind::Goto { ref target } => {
                    cfg_block.add_next(target.as_usize());
                }
                TerminatorKind::SwitchInt {
                    discr: _,
                    ref targets,
                } => {
                    for (_, ref target) in targets.iter() {
                        cfg_block.add_next(target.as_usize());
                    }
                    cfg_block.add_next(targets.otherwise().as_usize());
                }
                TerminatorKind::Drop {
                    place: _,
                    target,
                    unwind,
                    replace: _,
                    drop: _,
                    #[cfg(not(rapx_rustc_ge_198))]
                        async_fut: _,
                } => {
                    cfg_block.add_next(target.as_usize());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                TerminatorKind::Call {
                    ref target,
                    ref unwind,
                    ..
                } => {
                    if let Some(tt) = target {
                        cfg_block.add_next(tt.as_usize());
                    }
                    if let UnwindAction::Cleanup(tt) = unwind {
                        cfg_block.add_next(tt.as_usize());
                    }
                }
                TerminatorKind::Assert {
                    cond: _,
                    expected: _,
                    msg: _,
                    ref target,
                    ref unwind,
                } => {
                    cfg_block.add_next(target.as_usize());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                TerminatorKind::Yield {
                    value: _,
                    ref resume,
                    resume_arg: _,
                    ref drop,
                } => {
                    cfg_block.add_next(resume.as_usize());
                    if let Some(target) = drop {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                TerminatorKind::FalseEdge {
                    ref real_target,
                    imaginary_target: _,
                } => {
                    cfg_block.add_next(real_target.as_usize());
                }
                TerminatorKind::FalseUnwind {
                    ref real_target,
                    unwind: _,
                } => {
                    cfg_block.add_next(real_target.as_usize());
                }
                TerminatorKind::InlineAsm {
                    template: _,
                    operands: _,
                    options: _,
                    line_spans: _,
                    ref unwind,
                    targets,
                    asm_macro: _,
                } => {
                    for target in targets {
                        cfg_block.add_next(target.as_usize());
                    }
                    if let UnwindAction::Cleanup(target) = unwind {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                _ => {}
            }

            cfg_blocks.push(cfg_block);
            block_info.push(info);
        }

        let cfg = ControlFlowGraph::new(def_id, tcx, cfg_blocks);

        PathGraph {
            cfg,
            block_info,
            disc_info,
            aggregate_field_sources,
            field_projection_source,
            cast_chains,
        }
    }

    pub fn find_scc(&mut self) {
        self.cfg.find_scc();
        self.populate_all_child_sccs();
    }

    pub fn def_id(&self) -> DefId {
        self.cfg.def_id
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.cfg.tcx
    }

    pub fn cfg_block(&self, index: usize) -> &CfgBlock {
        self.cfg.block(index)
    }

    pub fn cfg_block_mut(&mut self, index: usize) -> &mut CfgBlock {
        self.cfg.block_mut(index)
    }

    /// Retrieve the MIR terminator for the block at `index` on demand.
    pub fn terminator(&self, index: usize) -> Option<&Terminator<'tcx>> {
        self.cfg.terminator(index)
    }

    pub fn is_cleanup_block(&self, index: usize) -> bool {
        self.cfg
            .blocks
            .get(index)
            .map(|b| b.is_cleanup)
            .unwrap_or(false)
    }

    /// Get the number of variants for a constraint local.
    /// First checks the pre-populated `variant_count_of` hashmap,
    /// then falls back to the local's declared type (for ADT locals
    /// that gained their type through field projections in nested
    /// destructuring patterns rather than explicit construction).
    fn get_variant_count(&self, local: usize) -> Option<usize> {
        if let Some(&count) = self.disc_info.variant_count_of.get(&local) {
            return Some(count);
        }
        let body = self.cfg.tcx.optimized_mir(self.cfg.def_id);
        let mut ty = body.local_decls[Local::from_usize(local)].ty;
        while let TyKind::Ref(_, inner_ty, _) | TyKind::RawPtr(inner_ty, _) = ty.kind() {
            ty = *inner_ty;
        }
        match ty.kind() {
            TyKind::Adt(adt_def, _) if adt_def.is_enum() => Some(adt_def.variants().len()),
            _ => None,
        }
    }

    /// Check a single transition `cur -> next` for reachability and update
    /// discriminant constraints. Returns `false` if the transition is
    /// provably unreachable.
    pub fn check_transition(
        &self,
        cur: usize,
        next: usize,
        constraints: &mut FxHashMap<usize, usize>,
    ) -> bool {
        if cur >= self.cfg.blocks.len() || next >= self.cfg.blocks.len() {
            return false;
        }

        if let Some(info) = self.block_info.get(cur) {
            for local in &info.assigned_locals {
                if let Some(&src) = info.constraint_copies.get(local) {
                    if let Some(val) = self.resolve_local_value(src, constraints) {
                        constraints.insert(*local, val);
                        continue;
                    }
                    if let Some(&dst_val) = constraints.get(local) {
                        constraints.insert(src, dst_val);
                        constraints.insert(*local, dst_val);
                        continue;
                    }
                }
                if let Some(&val) = info.constants.get(local) {
                    constraints.insert(*local, val);
                    continue;
                }
                constraints.remove(local);
            }
            for local in &info.known_nonnull_locals {
                constraints.insert(*local, usize::MAX);
            }
        }

        // Also clear constraints for locals assigned by the terminator
        // (e.g. _13 = Iterator::next() in a Call terminator). The block's
        // assigned_locals only covers statement-level assignments, so
        // terminator-side assignments are handled here.
        if let Some(terminator) = self.terminator(cur) {
            let assigned = match &terminator.kind {
                TerminatorKind::Call { destination, .. } => Some(destination.local.as_usize()),
                TerminatorKind::Yield { resume_arg, .. } => Some(resume_arg.local.as_usize()),
                _ => None,
            };
            if let Some(local) = assigned {
                // Propagate known nullness from BlockConstantInfo.
                if let Some(block_info) = self.block_info.get(cur) {
                    if let Some(&val) = block_info.constants.get(&local) {
                        constraints.insert(local, val);
                    } else if block_info.known_nonnull_locals.contains(&local) {
                        constraints.insert(local, usize::MAX);
                    } else {
                        constraints.remove(&local);
                    }
                } else {
                    constraints.remove(&local);
                }
            }
        }

        let successors = &self.cfg.block(cur).next;
        if !successors.contains(&next) {
            if !self.is_unwind_target(cur, next) {
                return false;
            }
        }

        if !self.check_switch_transition(cur, next, constraints) {
            return false;
        }

        if !self.check_assert_transition(cur, next, constraints) {
            return false;
        }

        true
    }

    fn check_assert_transition(
        &self,
        cur: usize,
        next: usize,
        constraints: &FxHashMap<usize, usize>,
    ) -> bool {
        let Some(terminator) = self.cfg.terminator(cur) else { return true };
        let TerminatorKind::Assert { cond, target, .. } = &terminator.kind else {
            return true;
        };
        if next != target.as_usize() {
            return true;
        }
        let cond_local = match cond {
            Operand::Copy(p) | Operand::Move(p) => p.local.as_usize(),
            Operand::Constant(c) => {
                let typing_env =
                    rustc_middle::ty::TypingEnv::post_analysis(self.cfg.tcx, self.cfg.def_id);
                return c.const_.try_eval_bool(self.cfg.tcx, typing_env).unwrap_or(true);
            }
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => return true,
        };
        self.resolve_bool_local(cond_local, constraints)
            .map_or(true, |v| v == 1)
    }

    fn resolve_simple_bool(
        &self,
        local: usize,
        constraints: &FxHashMap<usize, usize>,
    ) -> Option<usize> {
        if let Some(&val) = constraints.get(&local)
            && val <= 1
        {
            return Some(val);
        }
        for info in &self.block_info {
            if let Some(&val) = info.constants.get(&local)
                && val <= 1
            {
                return Some(val);
            }
            if let Some(cmp) = info.comparison_sources.get(&local) {
                if matches!(cmp.op, BinOp::Eq | BinOp::Ne) {
                    let is_eq = matches!(cmp.op, BinOp::Eq);
                    let lhs_val = self.resolve_local_value(cmp.lhs_local, constraints);
                    let rhs_val = self.resolve_local_value(cmp.rhs_local, constraints);
                    if let Some(known_val) = lhs_val.or(rhs_val) {
                        let other = if lhs_val.is_some() {
                            cmp.rhs_local
                        } else {
                            cmp.lhs_local
                        };
                        return Some(if is_eq {
                            if known_val == other { 1 } else { 0 }
                        } else {
                            if known_val != other { 1 } else { 0 }
                        });
                    }
                }
            }
        }
        None
    }

    fn resolve_bool_local(
        &self,
        local: usize,
        constraints: &FxHashMap<usize, usize>,
    ) -> Option<usize> {
        let mut stack = vec![(local, false)];
        let mut seen = FxHashSet::default();
        while let Some((cur, negated)) = stack.pop() {
            let key = if negated { cur | (1 << 31) } else { cur };
            if !seen.insert(key) { continue; }
            if let Some(v) = self.resolve_simple_bool(cur, constraints) {
                return Some(if negated { 1 - v } else { v });
            }
            for info in &self.block_info {
                if let Some(&src) = info.constraint_copies.get(&cur) {
                    stack.push((src, negated));
                }
                if let Some(&src) = info.negation_sources.get(&cur) {
                    stack.push((src, !negated));
                }
                if let Some(&(lhs, rhs)) = info.and_sources.get(&cur) {
                    let a = self.resolve_simple_bool(lhs, constraints);
                    let b = self.resolve_simple_bool(rhs, constraints);
                    if let (Some(a), Some(b)) = (a, b) {
                        let r = if a == 1 && b == 1 { 1 } else { 0 };
                        return Some(if negated { 1 - r } else { r });
                    }
                }
            }
            if let Some(&src) = self.cast_chains.get(&cur) {
                stack.push((src, negated));
            }
        }
        None
    }

    /// Check whether `cur → next` is a valid `SwitchInt` transition given
    /// current discriminant constraints. Returns `false` when the transition
    /// contradicts a known discriminant value. Also records newly learned
    /// constraints from the taken branch into `constraints`.
    fn check_switch_transition(
        &self,
        cur: usize,
        next: usize,
        constraints: &mut FxHashMap<usize, usize>,
    ) -> bool {
        let Some(terminator) = self.cfg.terminator(cur) else {
            return true;
        };

        match &terminator.kind {
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr_local = discr.place().map(|p| p.local.as_usize());
                let constraint_local = discr_local
                    .and_then(|l| self.disc_info.source_of.get(&l).copied())
                    .or(discr_local);

                // Collect all possible successor blocks for this switch.
                let all_targets: FxHashSet<usize> = targets
                    .iter()
                    .map(|(_, bb)| bb.as_usize())
                    .chain(std::iter::once(targets.otherwise().as_usize()))
                    .collect();

                if !all_targets.contains(&next) {
                    return false;
                }

                // Try to evaluate a concrete constant for the discriminant.
                let const_val = match discr {
                    Operand::Constant(c) => c
                        .const_
                        .try_eval_target_usize(
                            self.cfg.tcx,
                            TypingEnv::post_analysis(self.cfg.tcx, self.cfg.def_id),
                        )
                        .map(|v| v as usize),
                    _ => None,
                };

                if let Some(val) = const_val {
                    // Discriminant is a literal constant — only one target is
                    // reachable.
                    let expected = resolve_switch_target(targets, val as u128);
                    if next != expected {
                        return false;
                    }
                    if let Some(local) = constraint_local {
                        constraints.insert(local, val);
                    }
                    return true;
                }

                if let Some(local) = constraint_local {
                    if let Some(&known_val) = constraints.get(&local) {
                        let expected = resolve_switch_target(targets, known_val as u128);
                        if next != expected {
                            return false;
                        }
                        return true;
                    }
                }

                // Try to infer the discriminant from a comparison source
                // (e.g. `_X = Ne(ptr, 0)`) when we know whether `ptr` is null.
                if let Some(discr_local) = discr_local
                    && let Some(info) = self.block_info.get(cur)
                    && let Some(cmp) = info.comparison_sources.get(&discr_local)
                    && matches!(cmp.op, BinOp::Ne | BinOp::Eq)
                {
                    let is_ne = matches!(cmp.op, BinOp::Ne);
                    let pointer_is_nonnull = self.local_is_known_nonnull(
                        constraints, cmp.lhs_local,
                    );
                    let pointer_is_null = self.local_is_known_null(
                        constraints, cmp.lhs_local,
                    );
                    if pointer_is_nonnull {
                        let expected_val = if is_ne { 1 } else { 0 };
                        let expected = resolve_switch_target(targets, expected_val);
                        let val = expected_val as usize;
                        constraints.insert(discr_local, val);
                        if let Some(local) = constraint_local {
                            constraints.insert(local, val);
                        }
                        if next != expected {
                            return false;
                        }
                        return true;
                    }
                    if pointer_is_null {
                        let expected_val = if is_ne { 0 } else { 1 };
                        let expected = resolve_switch_target(targets, expected_val);
                        let val = expected_val as usize;
                        constraints.insert(discr_local, val);
                        if let Some(local) = constraint_local {
                            constraints.insert(local, val);
                        }
                        if next != expected {
                            return false;
                        }
                        return true;
                    }
                }

                // No prior constraint — conservatively allow any valid target
                // and record the newly learned constraint from the taken branch.
                if next == targets.otherwise().as_usize() {
                    if let Some(local) = constraint_local {
                        if let Some(num_variants) = self.get_variant_count(local) {
                            let all_covered = (0..num_variants)
                                .all(|v| targets.iter().any(|(tv, _)| tv == v as u128));
                            if all_covered {
                                return false;
                            }
                        }
                    }
                }

                self.learn_constraint_with_backprop(
                    cur,
                    constraint_local,
                    &targets,
                    next,
                    constraints,
                );

                true
            }
            _ => true,
        }
    }

    /// After learning a constraint for a discriminant local, propagate the
    /// constraint backward through the copy chain so that source locals also
    /// receive the value. This prevents losing track of the constraint when
    /// the destination temporary is reassigned on loop back-edges.
    fn learn_constraint_with_backprop(
        &self,
        cur: usize,
        constraint_local: Option<usize>,
        targets: &SwitchTargets,
        next: usize,
        constraints: &mut FxHashMap<usize, usize>,
    ) {
        let Some(local) = constraint_local else {
            return;
        };
        let Some((val, _)) = targets.iter().find(|(_, bb)| bb.as_usize() == next) else {
            if let Some(inferred) = self.infer_otherwise_value(targets, local) {
                constraints.insert(local, inferred);
                self.backprop_constraint(cur, local, inferred, constraints);
            }
            return;
        };
        let val = val as usize;
        constraints.insert(local, val);
        self.backprop_constraint(cur, local, val, constraints);
    }

    fn backprop_constraint(
        &self,
        cur: usize,
        local: usize,
        val: usize,
        constraints: &mut FxHashMap<usize, usize>,
    ) {
        let Some(info) = self.block_info.get(cur) else {
            return;
        };
        let mut current = local;
        while let Some(&src) = info.constraint_copies.get(&current) {
            if current == src {
                break;
            }
            constraints.insert(src, val);
            current = src;
        }
    }

    /// Recursively resolve a local's value through constraint copies,
    /// cast chains, field projections, and aggregate sources (global maps).
    fn resolve_local_value(
        &self,
        local: usize,
        constraints: &FxHashMap<usize, usize>,
    ) -> Option<usize> {
        let mut stack = vec![local];
        let mut seen = FxHashSet::default();
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur) {
                continue;
            }
            if let Some(&val) = constraints.get(&cur) {
                return Some(val);
            }
            // Follow constraint copies in any block (per-block metadata).
            for info in &self.block_info {
                if let Some(&src) = info.constraint_copies.get(&cur) {
                    stack.push(src);
                }
                if let Some(&val) = info.constants.get(&cur) {
                    return Some(val);
                }
            }
            // Follow global cast chains.
            if let Some(&cast_src) = self.cast_chains.get(&cur) {
                stack.push(cast_src);
            }
            // Follow field projection -> aggregate source.
            if let Some(&encoded) = self.field_projection_source.get(&cur) {
                if let Some((agg_local, field_idx)) = decode_aggregate_field(encoded) {
                    let key = encode_aggregate_field(agg_local, field_idx);
                    if let Some(&source) = self.aggregate_field_sources.get(&key) {
                        stack.push(source);
                    }
                }
            }
        }
        None
    }

    /// For the "otherwise" branch of a `SwitchInt`, try to infer the single
    /// concrete value that the discriminant must have (because all other
    /// possible values are covered by explicit targets).
    fn infer_otherwise_value(&self, targets: &SwitchTargets, discr_local: usize) -> Option<usize> {
        let body = self.cfg.tcx.optimized_mir(self.cfg.def_id);
        let mut discr_ty = body.local_decls[Local::from_usize(discr_local)].ty;
        while let TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) = discr_ty.kind() {
            discr_ty = *inner;
        }

        let possible_values: Vec<usize> = match discr_ty.kind() {
            TyKind::Bool => vec![0, 1],
            TyKind::Adt(adt_def, _) if adt_def.is_enum() => (0..adt_def.variants().len()).collect(),
            _ => return None,
        };

        let explicit_values: FxHashSet<usize> = targets.iter().map(|(v, _)| v as usize).collect();
        let remaining: Vec<usize> = possible_values
            .into_iter()
            .filter(|v| !explicit_values.contains(v))
            .collect();

        if remaining.len() == 1 {
            Some(remaining[0])
        } else {
            None
        }
    }

    /// Check whether `next` is an unwind target reachable from `cur` via a
    /// call or drop terminator (may not be recorded as a normal CFG successor).
    fn is_unwind_target(&self, cur: usize, next: usize) -> bool {
        let Some(terminator) = self.cfg.terminator(cur) else {
            return false;
        };

        let unwind = match &terminator.kind {
            TerminatorKind::Call { unwind, .. }
            | TerminatorKind::Drop { unwind, .. }
            | TerminatorKind::Assert { unwind, .. } => unwind,
            _ => return false,
        };

        if let UnwindAction::Cleanup(target) = unwind {
            return target.as_usize() == next;
        }
        false
    }

    /// Return true if `local` is known to be a non-null pointer.
    fn local_is_known_nonnull(
        &self,
        constraints: &FxHashMap<usize, usize>,
        local: usize,
    ) -> bool {
        let Some(&val) = constraints.get(&local) else {
            return false;
        };
        val > 0
    }

    /// Return true if `local` is known to be a null pointer.
    fn local_is_known_null(
        &self,
        constraints: &FxHashMap<usize, usize>,
        local: usize,
    ) -> bool {
        let Some(&val) = constraints.get(&local) else {
            return false;
        };
        val == 0
    }

    /// Populate the `child_sccs` field for a given SCC entry block, then
    /// recurse into those child SCCs. Called eagerly from `find_scc()` so
    /// that enumeration can be purely read-only on the graph.
    fn populate_child_sccs(&mut self, enter: usize) {
        let nodes: Vec<usize> = self.cfg.block(enter).scc.nodes.iter().cloned().collect();
        let mut child_enters = Vec::new();
        let mut seen = FxHashSet::default();

        for node in nodes {
            if let Some(block) = self.cfg.blocks.get(node) {
                let node_enter = block.scc.enter;
                let non_trivial = !block.scc.nodes.is_empty();
                if node_enter != enter && non_trivial && seen.insert(node_enter) {
                    child_enters.push(node_enter);
                }
            }
        }

        self.cfg.block_mut(enter).scc.child_sccs = child_enters;

        let child_count = self.cfg.block(enter).scc.child_sccs.len();
        for i in 0..child_count {
            let child_enter = self.cfg.block(enter).scc.child_sccs[i];
            self.populate_child_sccs(child_enter);
        }
    }

    fn populate_all_child_sccs(&mut self) {
        let mut visited = FxHashSet::default();
        let block_count = self.cfg.blocks.len();
        for i in 0..block_count {
            let scc = &self.cfg.block(i).scc;
            let enter = scc.enter;
            if scc.nodes.is_empty() || !visited.insert(enter) {
                continue;
            }
            self.populate_child_sccs(enter);
        }
    }
}

/// Hash of the constraint state accumulated along a path prefix.
///
/// Computed by walking the prefix, collecting `(local → constant_value)`
/// bindings from each block's [`BlockConstantInfo`], sorting them, and
/// hashing the result.  Used by [`PathEnumerator::visited_sccs`] to
/// skip redundant re-entries into the same SCC with the same state.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct ConstraintHash(u64);

impl ConstraintHash {
    fn from_path(path: &[usize], graph: &PathGraph<'_>) -> Self {
        let mut hasher = DefaultHasher::new();
        let mut constraints: FxHashMap<usize, usize> = FxHashMap::default();

        for &block in path.iter() {
            if let Some(info) = graph.block_info.get(block) {
                for local in &info.assigned_locals {
                    if let Some(&src) = info.constraint_copies.get(local) {
                        if let Some(&src_val) = constraints.get(&src) {
                            constraints.insert(*local, src_val);
                            continue;
                        }
                        if let Some(&dst_val) = constraints.get(local) {
                            constraints.insert(src, dst_val);
                            constraints.insert(*local, dst_val);
                            continue;
                        }
                    }
                    if let Some(&val) = info.constants.get(local) {
                        constraints.insert(*local, val);
                        continue;
                    }
                    constraints.remove(local);
                }
            }
        }

        let mut entries: Vec<(usize, usize)> = constraints.into_iter().collect();
        entries.sort();
        entries.hash(&mut hasher);
        ConstraintHash(hasher.finish())
    }
}

/// Key for [`PathEnumerator::scc_paths`] and [`PathEnumerator::visited_sccs`] and [`PathEnumerator::visited_sccs`]:
/// which SCC entry block, with what constraint state, and how many
/// additional postfix repeats are allowed.
///
/// In `scc_paths` the `constraint` field is unused (cache keyed by
/// `entry` + `repeat`); in `visited_sccs` the `repeat` field is
/// unused (deduplicated by `entry` + `constraint`).
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct SccKey {
    pub entry: usize,
    pub repeat: usize,
    pub constraint: ConstraintHash,
}

/// Builds a [`PathTree`] by depth-first enumeration of whole-CFG paths.
///
/// The enumerator holds a `&PathGraph` (which must have `find_scc()` called
/// beforehand) and two caches:
///
/// The **constraint hash** used by `visited_sccs` is a
/// [`ConstraintHash`]: it walks the current path prefix, accumulates
/// `(local → constant_value)` bindings from each block's
/// [`BlockConstantInfo`], sorts them, and hashes the result.  Different
/// constraint states (e.g. a loop variable changing from `true` to
/// `false`) produce different hashes.
///
/// 1. `scc_paths` — maps [`SccKey`] to a list of acyclic paths through
///    that SCC.  Reused across repeated enumerations of the same function
///    with different repeat counts.
///
/// 2. `visited_sccs` — set of [`SccKey`] entries already explored
///    (matched by `entry` + `constraint`, ignoring `repeat`).
///    When the same SCC is reached with the same constraint state, its
///    sub-paths are identical, so the re-entry is skipped.
///
/// Constraint-based filtering runs incrementally during DFS via
/// [`PathGraph::check_transition`], so only feasible paths are inserted
/// into the resulting tree.
pub struct PathEnumerator<'g, 'tcx> {
    graph: &'g PathGraph<'tcx>,
    scc_paths: FxHashMap<SccKey, Vec<SccPath>>,
    visited_sccs: FxHashSet<SccKey>,
}

impl<'g, 'tcx> PathEnumerator<'g, 'tcx> {
    pub fn new(graph: &'g PathGraph<'tcx>) -> Self {
        PathEnumerator {
            graph,
            scc_paths: FxHashMap::default(),
            visited_sccs: FxHashSet::default(),
        }
    }

    /// Enumerate all whole-CFG paths, pruning infeasible transitions via
    /// incremental constraint-based filtering during DFS.
    ///
    /// SCC regions are flattened into a bounded set of acyclic paths.
    pub fn enumerate_paths(&mut self) -> PathTree {
        self.enumerate_paths_repeat(0)
    }

    /// Enumerate whole-CFG paths allowing each SCC postfix segment to repeat
    /// up to `postfix_repeat` additional times. `postfix_repeat = 0` gives
    /// the same result as `enumerate_paths`.
    pub fn enumerate_paths_repeat(&mut self, postfix_repeat: usize) -> PathTree {
        let mut tree = PathTree::new();

        if self.graph.cfg.blocks.is_empty() {
            return tree;
        }

        self.collect_whole_cfg_paths(
            0,
            &mut vec![0],
            &mut tree,
            0,
            postfix_repeat,
            &FxHashMap::default(),
        );

        tree
    }

    /// Enumerate all acyclic paths through `scc` starting at `start`,
    /// allowing each postfix segment to repeat up to `postfix_repeat`
    /// additional times.
    ///
    /// Results are cached per `(def_id, scc_enter, postfix_repeat)`.
    pub fn find_scc_paths_repeat(
        &mut self,
        start: usize,
        scc: &SccInfo,
        postfix_repeat: usize,
    ) -> Vec<SccPath> {
        let cache_key = SccKey {
            entry: scc.enter,
            repeat: postfix_repeat,
            constraint: ConstraintHash::default(),
        };
        if let Some(cached) = self.scc_paths.get(&cache_key) {
            return cached.clone();
        }

        let mut out = Vec::new();
        let mut seen: FxHashSet<Vec<usize>> = FxHashSet::default();
        let mut path = vec![start];
        let mut segment_counts = FxHashMap::default();

        self.dfs_scc_tree(
            scc,
            start,
            &mut path,
            &mut segment_counts,
            postfix_repeat,
            &mut out,
            &mut seen,
            0,
        );

        if self.scc_paths.len() >= SCC_PATH_CACHE_LIMIT {
            self.scc_paths.clear();
        }
        self.scc_paths.insert(cache_key, out.clone());

        out
    }

    /// Recursive DFS through one level of the SCC tree.
    ///
    /// Enumerates structurally possible paths through the SCC to exit points.
    /// No constraint tracking — `check_postfix_segment` prunes repeated
    /// loop-body segments purely by block-id sequence.
    ///
    /// When `postfix_repeat > 0`, allows the same postfix segment to repeat
    /// up to `postfix_repeat` additional times beyond the first occurrence.
    ///
    /// Child SCC paths are pre-enumerated via `find_scc_paths_repeat` and treated as
    /// atomic building blocks (no recursive descent into child SCC internals).
    #[allow(clippy::too_many_arguments)]
    fn dfs_scc_tree(
        &mut self,
        scc: &SccInfo,
        cur: usize,
        path: &mut Vec<usize>,
        segment_counts: &mut FxHashMap<Vec<usize>, usize>,
        postfix_repeat: usize,
        out: &mut Vec<SccPath>,
        seen_paths: &mut FxHashSet<Vec<usize>>,
        depth: usize,
    ) {
        if depth > SCC_MAX_DEPTH {
            return;
        }
        if out.len() >= SCC_MAX_SEEN_PATHS {
            return;
        }
        if path.len() > SCC_MAX_PATH_LEN {
            return;
        }
        if cur != scc.enter && !scc.nodes.contains(&cur) {
            return;
        }

        if cur == scc.enter && path.len() > 1 {
            if !check_postfix_segment(path, scc.enter, segment_counts, postfix_repeat) {
                if (postfix_repeat > 0 || segment_counts.len() > 1)
                    && scc.exits.iter().any(|e| e.exit == cur)
                {
                    self.record_unique_path(path, scc, out, seen_paths);
                }
                return;
            }
        }

        if scc.exits.iter().any(|e| e.exit == cur) {
            self.record_unique_path(path, scc, out, seen_paths);
        }

        let is_child = scc.child_sccs.contains(&cur);

        if is_child {
            let ctx = self.constraint_context(path);
            if !self.visited_sccs.insert(SccKey {
                entry: cur,
                repeat: 0,
                constraint: ctx,
            }) {
                return;
            }

            let child_scc = self.graph.cfg_block(cur).scc.clone();
            let child_paths = self.find_scc_paths_repeat(cur, &child_scc, postfix_repeat);

            for child_path in &child_paths {
                let orig_len = path.len();
                if child_path.blocks.len() > 1 {
                    path.extend(&child_path.blocks[1..]);
                }

                let mut branch_counts = segment_counts.clone();
                for &next in &child_path.exit_successors {
                    path.push(next);
                    self.dfs_scc_tree(
                        scc,
                        next,
                        path,
                        &mut branch_counts,
                        postfix_repeat,
                        out,
                        seen_paths,
                        depth + 1,
                    );
                    path.pop();
                }
                path.truncate(orig_len);
            }
            return;
        }

        let successors: Vec<usize> = self.graph.cfg.block(cur).next.iter().copied().collect();
        let saved_counts = segment_counts.clone();
        for next in successors {
            if next != scc.enter && !scc.nodes.contains(&next) {
                self.record_unique_path(path, scc, out, seen_paths);
                continue;
            }
            let mut branch_counts = saved_counts.clone();
            path.push(next);
            self.dfs_scc_tree(
                scc,
                next,
                path,
                &mut branch_counts,
                postfix_repeat,
                out,
                seen_paths,
                depth + 1,
            );
            path.pop();
        }
    }

    /// Build a [`ConstraintHash`] from the constraint state along `path`.
    fn constraint_context(&self, path: &[usize]) -> ConstraintHash {
        ConstraintHash::from_path(path, self.graph)
    }

    /// Depth-first enumeration of all CFG paths from `current` to a terminator.
    ///
    /// SCC nodes are flattened via `find_scc_paths_repeat`; non-SCC blocks are followed
    /// one by one.  No cycle detection is needed because the post-SCC CFG is a DAG.
    /// Constraints are maintained incrementally — each transition is checked
    /// via `PathGraph::check_transition` before recursing, and infeasible
    /// branches are pruned early.
    fn collect_whole_cfg_paths(
        &mut self,
        current: usize,
        path: &mut Vec<usize>,
        tree: &mut PathTree,
        depth: usize,
        postfix_repeat: usize,
        constraints: &FxHashMap<usize, usize>,
    ) {
        if current >= self.graph.cfg.blocks.len() {
            return;
        }
        if depth > WHOLE_CFG_PATH_DEPTH_LIMIT || tree.len() >= WHOLE_CFG_PATH_LIMIT {
            return;
        }

        let scc_info = self.graph.cfg_block(current).scc.clone();
        let is_scc = current == scc_info.enter && !scc_info.nodes.is_empty();
        if is_scc {
            let scc = self.sort_scc_tree(&scc_info);
            let segments = self.find_scc_paths_repeat(current, &scc, postfix_repeat);

            if segments.is_empty() {
                tree.insert(path);
                return;
            }

            for seg in segments {
                if tree.len() >= WHOLE_CFG_PATH_LIMIT {
                    break;
                }

                let orig_len = path.len();
                let mut seg_constraints = constraints.clone();
                let mut reachable = true;

                if seg.blocks.len() > 1 {
                    for i in 0..seg.blocks.len() - 1 {
                        if !self.graph.check_transition(
                            seg.blocks[i],
                            seg.blocks[i + 1],
                            &mut seg_constraints,
                        ) {
                            reachable = false;
                            break;
                        }
                    }
                    if reachable {
                        path.extend_from_slice(&seg.blocks[1..]);
                    }
                }

                if reachable {
                    if seg.exit_successors.is_empty() {
                        tree.insert(path);
                    } else {
                        for &next in &seg.exit_successors {
                            let mut next_constraints = seg_constraints.clone();
                            let last = *path.last().unwrap();
                            if self
                                .graph
                                .check_transition(last, next, &mut next_constraints)
                            {
                                path.push(next);
                                self.collect_whole_cfg_paths(
                                    next,
                                    path,
                                    tree,
                                    depth + 1,
                                    postfix_repeat,
                                    &next_constraints,
                                );
                                path.pop();
                            }
                        }
                    }
                }

                path.truncate(orig_len);
            }
            return;
        }

        // Non-SCC block: follow CFG successors.
        let successors: Vec<usize> = self.graph.cfg_block(current).next.iter().copied().collect();
        if successors.is_empty() {
            tree.insert(path);
            return;
        }

        for next in successors {
            let mut next_constraints = constraints.clone();
            if self
                .graph
                .check_transition(current, next, &mut next_constraints)
            {
                path.push(next);
                self.collect_whole_cfg_paths(
                    next,
                    path,
                    tree,
                    depth + 1,
                    postfix_repeat,
                    &next_constraints,
                );
                path.pop();
            }
        }
    }

    fn sort_scc_tree(&self, scc: &SccInfo) -> SccInfo {
        self.graph.cfg_block(scc.enter).scc.clone()
    }

    fn record_unique_path(
        &self,
        path: &[usize],
        scc: &SccInfo,
        out: &mut Vec<SccPath>,
        seen_paths: &mut FxHashSet<Vec<usize>>,
    ) {
        if !seen_paths.insert(path.to_vec()) {
            return;
        }
        let exit_successors = self.compute_exit_successors(path, scc);
        out.push(SccPath {
            blocks: path.to_vec(),
            exit_successors,
        });
    }

    fn compute_exit_successors(&self, path: &[usize], scc: &SccInfo) -> Vec<usize> {
        let Some(&last) = path.last() else {
            return vec![];
        };
        scc.exits
            .iter()
            .filter(|e| e.exit == last)
            .map(|e| e.to)
            .filter(|&n| {
                !scc.child_sccs
                    .contains(&self.graph.cfg.block(n).scc.enter())
            })
            .collect()
    }
}

/// Resolve a concrete discriminant value to the corresponding `SwitchInt`
/// successor block index.
fn resolve_switch_target(targets: &SwitchTargets, val: u128) -> usize {
    targets
        .iter()
        .find(|(v, _)| *v == val)
        .map(|(_, bb)| bb.as_usize())
        .unwrap_or_else(|| targets.otherwise().as_usize())
}
