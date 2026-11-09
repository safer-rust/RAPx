use super::PathTree;
use crate::compat::{FxHashMap, FxHashSet};
use crate::def_ids::other_api;
use crate::graphs::{
    cfg::{CfgBlock, ControlFlowGraph},
    scc::{Scc, SccInfo},
};
use crate::helpers::mir_utils;
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, BinOp, Body, Local, Operand, ProjectionElem, Rvalue,
        StatementKind, SwitchTargets, Terminator, TerminatorKind, UnOp, UnwindAction,
    },
    ty::{TyCtxt, TyKind, TypingEnv},
};
use rustc_span::def_id::DefId;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use crate::limit::{
    SCC_MAX_DEPTH, SCC_MAX_PATH_LEN, SCC_MAX_SEEN_PATHS, SCC_PATH_CACHE_LIMIT,
    WHOLE_CFG_PATH_DEPTH_LIMIT,
};

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

/// Per-block facts collected during construction for path reachability
/// analysis: which locals are assigned, and the origin of each local's value.
#[derive(Clone, Debug, Default)]
pub struct BlockFacts {
    pub assigned_locals: Vec<usize>,
    /// Maps a local to the origin of its value.
    pub origin: FxHashMap<usize, LocalOrigin>,
}
/// The right-hand operand of a sum/comparison: a constant or a local.
#[derive(Clone, Copy, Debug)]
pub enum Rhs {
    /// A compile-time constant.
    Const(usize),
    /// A local.
    Local(usize),
}

/// The single MIR expression that defined a local's value.
#[derive(Clone, Debug)]
pub enum Expr {
    /// `dest = lhs + rhs`.
    Add { lhs: usize, rhs: Rhs },
    /// `dest = src % divisor`.
    Rem { src: usize, divisor: usize },
    /// `dest = !src`.
    Not { src: usize },
    /// `dest = lhs & rhs` (a boolean conjunction).
    And { lhs: usize, rhs: usize },
    /// `dest = lhs <op> rhs` (`Lt`/`Le`/`Gt`/`Ge`/`Eq`/`Ne`).
    Cmp { op: BinOp, lhs: usize, rhs: Rhs },
}

/// The origin of a local's value: a constant, a copy of another local, an
/// expression result, or a provably non-null pointer.
#[derive(Clone, Debug)]
pub enum LocalOrigin {
    /// `dest` is the given constant value.
    Const(usize),
    /// `dest` is a copy of another local.
    Copy(usize),
    /// `dest` is an expression result.
    Expr(Expr),
    /// `dest` is a provably non-null pointer.
    NonNull,
}

impl LocalOrigin {
    /// The copied-from local, if this is a copy origin.
    fn as_copy(&self) -> Option<&usize> {
        match self {
            LocalOrigin::Copy(src) => Some(src),
            _ => None,
        }
    }

    /// The constant value, if this is a constant origin.
    fn as_const(&self) -> Option<&usize> {
        match self {
            LocalOrigin::Const(val) => Some(val),
            _ => None,
        }
    }
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

/// Path-sensitive facts (constant values, relational bounds, slice lengths)
/// tracked while enumerating a single path.
#[derive(Clone, Default)]
pub(crate) struct ConstraintSet {
    /// `local -> concrete value` (or `usize::MAX` for the known-nonnull sentinel).
    consts: FxHashMap<usize, usize>,
    /// `lhs -> [(rhs, strict)]`: `lhs < rhs` when `strict`, else `lhs <= rhs`.
    bounds: FxHashMap<usize, Vec<(usize, bool)>>,
    /// `len_local -> (start, end)`: `len_local == end - start`.
    lengths: FxHashMap<usize, (usize, usize)>,
}

/// CFG augmented with per-block facts and discriminant metadata
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
    pub block_info: Vec<BlockFacts>,
    pub disc_info: DiscriminantInfo,
    /// Excludes global origins of MIR locals with multiple assignments.
    pub(crate) conservative_origins: bool,
    /// Global store: maps encoded `(local, field_idx)` to source local from Aggregates.
    pub aggregate_field_sources: FxHashMap<usize, usize>,
    /// Global store: maps `dest` to `src` for pointer-cast chains.
    pub cast_chains: FxHashMap<usize, usize>,
    /// Global store: maps `_dest` to the referent local of `_dest = &*referent`.
    pub reborrow_referents: FxHashMap<usize, usize>,
    /// Global store: maps `_dest` to encoded `(base, field_idx)` from field-projection copies.
    pub field_projection_source: FxHashMap<usize, usize>,
}

/// Scan a function's MIR and collect its per-block constant/discriminant
/// metadata and source maps.
#[allow(clippy::type_complexity)]
fn build_function_info<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body: &Body<'tcx>,
) -> (
    Vec<BlockFacts>,
    DiscriminantInfo,
    FxHashMap<usize, usize>,
    FxHashMap<usize, usize>,
    FxHashMap<usize, usize>,
    FxHashMap<usize, usize>,
) {
    let basicblocks = &body.basic_blocks;
    let mut block_info = Vec::new();
    let mut disc_info = DiscriminantInfo::default();
    let mut aggregate_field_sources: FxHashMap<usize, usize> = FxHashMap::default();
    let mut field_projection_source: FxHashMap<usize, usize> = FxHashMap::default();
    let mut cast_chains: FxHashMap<usize, usize> = FxHashMap::default();
    let mut reborrow_referents: FxHashMap<usize, usize> = FxHashMap::default();

    for i in 0..basicblocks.len() {
        let bb = &basicblocks[BasicBlock::from(i)];
        let mut info = BlockFacts::default();

        for stmt in &bb.statements {
            if let StatementKind::Assign(assign) = &stmt.kind {
                let (place, rvalue) = &**assign;
                let dest = place.local.as_usize();
                // Writing through (*ptr).field doesn't reassign ptr itself,
                // so ptr's constraint should not be cleared.
                let is_deref = place
                    .projection
                    .iter()
                    .any(|p| matches!(p, ProjectionElem::Deref));
                if !is_deref && !info.assigned_locals.contains(&dest) {
                    info.assigned_locals.push(dest);
                }
                match rvalue {
                    Rvalue::Use(Operand::Constant(c), ..) => {
                        let typing_env = TypingEnv::post_analysis(tcx, def_id);
                        let val = match c.const_.ty().kind() {
                            TyKind::Bool => c
                                .const_
                                .try_eval_bool(tcx, typing_env)
                                .map(|b| if b { 1 } else { 0 }),
                            TyKind::Int(_) | TyKind::Uint(_) => c
                                .const_
                                .try_eval_bits(tcx, typing_env)
                                .and_then(|v| usize::try_from(v).ok()),
                            _ => None,
                        };
                        if let Some(val) = val {
                            info.origin.insert(dest, LocalOrigin::Const(val));
                        }
                    }
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) => {
                        let src_local = src.local.as_usize();
                        if let Some(field_proj) = first_field_projection(src) {
                            let encoded = encode_aggregate_field(src_local, field_proj);
                            field_projection_source.insert(dest, encoded);
                        }
                        info.origin.insert(dest, LocalOrigin::Copy(src_local));
                    }
                    Rvalue::Discriminant(rv_place) => {
                        let src_local = rv_place.local.as_usize();
                        disc_info.source_of.insert(dest, src_local);
                        if let std::collections::hash_map::Entry::Vacant(e) =
                            disc_info.variant_count_of.entry(src_local)
                        {
                            let src_ty = body.local_decls[rv_place.local].ty;
                            if let TyKind::Adt(adt_def, _) = src_ty.kind() {
                                let num = adt_def.variants().len();
                                if num > 0 {
                                    e.insert(num);
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
                            info.origin.insert(dest, LocalOrigin::Const(discr));
                            if let std::collections::hash_map::Entry::Vacant(e) =
                                disc_info.variant_count_of.entry(dest)
                            {
                                let dest_ty = body.local_decls[place.local].ty;
                                if let TyKind::Adt(adt_def, _) = dest_ty.kind() {
                                    let num = adt_def.variants().len();
                                    if num > 0 {
                                        e.insert(num);
                                    }
                                }
                            }
                        }
                    }
                    Rvalue::BinaryOp(BinOp::AddWithOverflow, operands) => {
                        let (lhs, rhs): (&Operand<'_>, &Operand<'_>) = (&operands.0, &operands.1);
                        if let Some(lhs_local) = match lhs {
                            Operand::Copy(l) | Operand::Move(l) if l.projection.is_empty() => {
                                Some(l.local.as_usize())
                            }
                            Operand::Copy(l) | Operand::Move(l) => first_field_projection(l)
                                .map(|f| encode_aggregate_field(l.local.as_usize(), f)),
                            _ => None,
                        } {
                            let rhs_kind = match rhs {
                                Operand::Constant(c) => {
                                    let typing_env = TypingEnv::post_analysis(tcx, def_id);
                                    c.const_
                                        .try_eval_bits(tcx, typing_env)
                                        .and_then(|v| usize::try_from(v).ok())
                                        .map(Rhs::Const)
                                }
                                Operand::Copy(r) | Operand::Move(r) if r.projection.is_empty() => {
                                    Some(Rhs::Local(r.local.as_usize()))
                                }
                                _ => None,
                            };
                            if let Some(rhs_kind) = rhs_kind {
                                info.origin.insert(
                                    dest,
                                    LocalOrigin::Expr(Expr::Add {
                                        lhs: lhs_local,
                                        rhs: rhs_kind,
                                    }),
                                );
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
                        let (lhs, rhs): (&Operand<'_>, &Operand<'_>) = (&operands.0, &operands.1);
                        let lhs_local = match lhs {
                            Operand::Copy(l) | Operand::Move(l) if l.projection.is_empty() => {
                                Some(l.local.as_usize())
                            }
                            _ => None,
                        };
                        if let Some(lhs_local) = lhs_local {
                            let rhs_kind = match rhs {
                                Operand::Constant(c) => {
                                    let typing_env = TypingEnv::post_analysis(tcx, def_id);
                                    c.const_
                                        .try_eval_bits(tcx, typing_env)
                                        .and_then(|v| usize::try_from(v).ok())
                                        .map(Rhs::Const)
                                }
                                Operand::Copy(r) | Operand::Move(r) if r.projection.is_empty() => {
                                    Some(Rhs::Local(r.local.as_usize()))
                                }
                                _ => None,
                            };
                            let Some(rhs_kind) = rhs_kind else {
                                continue;
                            };
                            if matches!(op, BinOp::BitAnd) {
                                // `dest = lhs & rhs`: only a boolean conjunction
                                // (and thus resolvable) when `dest` is a bool and
                                // `rhs` is a local.
                                if let Rhs::Local(rhs_local) = rhs_kind
                                    && matches!(
                                        body.local_decls[place.local].ty.kind(),
                                        TyKind::Bool
                                    )
                                {
                                    info.origin.insert(
                                        dest,
                                        LocalOrigin::Expr(Expr::And {
                                            lhs: lhs_local,
                                            rhs: rhs_local,
                                        }),
                                    );
                                }
                            } else {
                                info.origin.insert(
                                    dest,
                                    LocalOrigin::Expr(Expr::Cmp {
                                        op: *op,
                                        lhs: lhs_local,
                                        rhs: rhs_kind,
                                    }),
                                );
                            }
                        }
                    }
                    Rvalue::BinaryOp(BinOp::Rem, operands) => {
                        let (lhs, rhs): (&Operand<'_>, &Operand<'_>) = (&operands.0, &operands.1);
                        if let Some(lhs_local) = match lhs {
                            Operand::Copy(l) | Operand::Move(l) if l.projection.is_empty() => {
                                Some(l.local.as_usize())
                            }
                            _ => None,
                        } {
                            let divisor = match rhs {
                                Operand::Constant(c) => {
                                    let typing_env = TypingEnv::post_analysis(tcx, def_id);
                                    c.const_
                                        .try_eval_bits(tcx, typing_env)
                                        .and_then(|v| usize::try_from(v).ok())
                                }
                                _ => None,
                            };
                            if let Some(divisor) = divisor
                                && divisor != 0
                            {
                                info.origin.insert(
                                    dest,
                                    LocalOrigin::Expr(Expr::Rem {
                                        src: lhs_local,
                                        divisor,
                                    }),
                                );
                            }
                        }
                    }
                    Rvalue::UnaryOp(unop, operand) => {
                        if matches!(unop, UnOp::Not)
                            && let Operand::Copy(src) | Operand::Move(src) = operand
                        {
                            info.origin.insert(
                                dest,
                                LocalOrigin::Expr(Expr::Not {
                                    src: src.local.as_usize(),
                                }),
                            );
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
                    Rvalue::Ref(_, _, referent) => {
                        // `_x = &*_y` reborrows `_y`; link them for length tracking.
                        if referent
                            .projection
                            .iter()
                            .any(|p| matches!(p, ProjectionElem::Deref))
                        {
                            reborrow_referents.insert(dest, referent.local.as_usize());
                        }
                    }
                    _ => {} // close match rvalue
                }
            }
        }

        if let Some(terminator) = &bb.terminator
            && let TerminatorKind::Call {
                destination,
                ref func,
                ..
            } = terminator.kind
            && let Some(did) = mir_utils::dep_callee_def_id(func)
        {
            if other_api::is_known_nonnull(did) {
                info.origin
                    .insert(destination.local.as_usize(), LocalOrigin::NonNull);
            }
            if other_api::is_null_ptr(tcx, did) {
                info.origin
                    .insert(destination.local.as_usize(), LocalOrigin::Const(0));
            }
        }

        block_info.push(info);
    }

    (
        block_info,
        disc_info,
        aggregate_field_sources,
        field_projection_source,
        cast_chains,
        reborrow_referents,
    )
}

impl<'tcx> PathGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> PathGraph<'tcx> {
        let body = tcx.optimized_mir(def_id);
        Self::build_with_body(tcx, def_id, body, false)
    }

    /// Build a path graph from an explicit MIR body (rather than
    /// `optimized_mir(def_id)`). Used to verify a monomorphized body whose
    /// `def_id` is still the generic function.
    pub fn new_with_body(tcx: TyCtxt<'tcx>, def_id: DefId, body: &Body<'tcx>) -> PathGraph<'tcx> {
        Self::build_with_body(tcx, def_id, body, true)
    }

    fn build_with_body(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        body: &Body<'tcx>,
        retain_body: bool,
    ) -> PathGraph<'tcx> {
        let basicblocks = &body.basic_blocks;
        let mut cfg_blocks = Vec::<CfgBlock>::new();

        for i in 0..basicblocks.len() {
            let bb = &basicblocks[BasicBlock::from(i)];
            let mut cfg_block = CfgBlock::new(i, bb.is_cleanup);

            let Some(terminator) = &bb.terminator else {
                cfg_blocks.push(cfg_block);
                continue;
            };

            match terminator.kind.clone() {
                TerminatorKind::Goto { ref target, .. } => {
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
                    #[cfg(not(rapx_ge_99))]
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
        }

        let mut cfg = ControlFlowGraph::new(def_id, tcx, cfg_blocks);
        if retain_body {
            cfg.set_body_override(body.clone());
        }
        let (
            block_info,
            disc_info,
            aggregate_field_sources,
            field_projection_source,
            cast_chains,
            reborrow_referents,
        ) = build_function_info(tcx, def_id, body);

        PathGraph {
            cfg,
            block_info,
            disc_info,
            conservative_origins: false,
            aggregate_field_sources,
            field_projection_source,
            cast_chains,
            reborrow_referents,
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

    /// Get the number of variants for a constraint local (in this function's local
    /// namespace). First checks the pre-populated `variant_count_of` hashmap,
    /// then falls back to the local's declared type (for ADT locals that gained
    /// their type through field projections in nested destructuring patterns
    /// rather than explicit construction).
    fn get_variant_count(&self, local: usize) -> Option<usize> {
        if let Some(&count) = self.disc_info.variant_count_of.get(&local) {
            return Some(count);
        }
        let body = self.cfg.body();
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
    pub(crate) fn check_transition(&self, cur: usize, next: usize, cs: &mut ConstraintSet) -> bool {
        if cur >= self.cfg.blocks.len() || next >= self.cfg.blocks.len() {
            return false;
        }

        if let Some(info) = self.block_info.get(cur) {
            for local in &info.assigned_locals {
                // Clear both the local and its canonical form (a loop counter
                // `i = (_add).0` canonicalizes to `(_add, 0)`).
                cs.bounds.remove(local);
                cs.bounds.remove(&self.canonical_field(*local));
                cs.lengths.remove(local);
                cs.lengths.remove(&self.canonical_field(*local));
                if let Some(&src) = info.origin.get(local).and_then(LocalOrigin::as_copy) {
                    if let Some(val) = self.resolve_local_value(src, cs) {
                        cs.consts.insert(*local, val);
                        continue;
                    }
                    if let Some(&dst_val) = cs.consts.get(local) {
                        cs.consts.insert(src, dst_val);
                        cs.consts.insert(*local, dst_val);
                        continue;
                    }
                }
                if let Some(&val) = info.origin.get(local).and_then(LocalOrigin::as_const) {
                    cs.consts.insert(*local, val);
                    continue;
                }
                cs.consts.remove(local);
            }
            for (local, origin) in &info.origin {
                if matches!(origin, LocalOrigin::NonNull) {
                    cs.consts.insert(*local, usize::MAX);
                }
            }
            for local in &info.assigned_locals {
                self.derive_increment_bound(*local, cs);
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
                cs.bounds.remove(&local);
                cs.lengths.remove(&local);
                if let Some(block_info) = self.block_info.get(cur) {
                    if let Some(&val) = block_info
                        .origin
                        .get(&local)
                        .and_then(LocalOrigin::as_const)
                    {
                        cs.consts.insert(local, val);
                    } else if matches!(block_info.origin.get(&local), Some(LocalOrigin::NonNull)) {
                        cs.consts.insert(local, usize::MAX);
                    } else {
                        cs.consts.remove(&local);
                    }
                } else {
                    cs.consts.remove(&local);
                }
            }
        }

        // Track slice lengths from `slice::get`/`slice::len`/`Try::branch`.
        if let Some(terminator) = self.terminator(cur)
            && let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &terminator.kind
            && let Some(callee) = mir_utils::dep_callee_def_id(func)
        {
            let dest = destination.local.as_usize();
            if self.tcx().def_path_str(callee).ends_with("::branch")
                && let Some(source) = args.first().and_then(|arg| arg.node.place())
            {
                let source_local = source.local.as_usize();
                let source_ty = self.cfg.body().local_decls[source.local].ty;
                if let TyKind::Adt(adt, _) = source_ty.kind()
                    && let Some(value) = cs.consts.get(&source_local).copied()
                {
                    let branch = if self
                        .tcx()
                        .is_diagnostic_item(rustc_span::sym::Option, adt.did())
                    {
                        match value {
                            0 => Some(1),
                            1 => Some(0),
                            _ => None,
                        }
                    } else if self
                        .tcx()
                        .is_diagnostic_item(rustc_span::sym::Result, adt.did())
                    {
                        (value <= 1).then_some(value)
                    } else {
                        None
                    };
                    if let Some(branch) = branch {
                        cs.consts.insert(dest, branch);
                    }
                }
            }
            if crate::def_ids::other_api::is_slice_get(self.tcx(), callee) {
                if let Some(range) = args.get(1)
                    && let Some(range_local) = range.node.place().map(|p| p.local.as_usize())
                {
                    let start = self
                        .aggregate_field_sources
                        .get(&encode_aggregate_field(range_local, 0))
                        .copied();
                    let end = self
                        .aggregate_field_sources
                        .get(&encode_aggregate_field(range_local, 1))
                        .copied();
                    if let (Some(start), Some(end)) = (start, end) {
                        cs.lengths.insert(dest, (start, end));
                    }
                }
            } else if self.tcx().def_path_str(callee).ends_with("::branch") {
                // `Try::branch(option)` -> the `Continue` payload carries the
                // same length as the input `Some` payload.
                if let Some(opt) = args.get(0)
                    && let Some(opt_local) = opt.node.place().map(|p| p.local.as_usize())
                {
                    if let Some(len) = self.resolve_length(opt_local, cs) {
                        cs.lengths.insert(dest, len);
                    }
                }
            }
        }

        // Carry bounds from a field's source to the constructed aggregate field.
        for (&encoded, &src) in &self.aggregate_field_sources {
            let canon = self.canonical_field(src);
            if let Some(src_bounds) = cs.bounds.get(&canon).cloned() {
                let entry = cs.bounds.entry(encoded).or_default();
                for (r, s) in src_bounds {
                    if !entry.iter().any(|&(rr, ss)| rr == r && ss == s) {
                        entry.push((r, s));
                    }
                }
            }
        }

        let successors = &self.cfg.block(cur).next;
        if !successors.contains(&next) && !self.is_unwind_target(cur, next) {
            return false;
        }

        if !self.check_switch_transition(cur, next, cs) {
            return false;
        }

        if !self.check_assert_transition(cur, next, cs) {
            return false;
        }

        true
    }

    fn check_assert_transition(&self, cur: usize, next: usize, cs: &mut ConstraintSet) -> bool {
        let Some(terminator) = self.cfg.terminator(cur) else {
            return true;
        };
        let TerminatorKind::Assert {
            cond,
            expected,
            target,
            ..
        } = &terminator.kind
        else {
            return true;
        };
        if next != target.as_usize() {
            return true;
        }
        // On the assert-passed path the condition holds: if it is a comparison
        // like `x > 0` / `x != 0`, mark `x` as known-nonzero so a downstream
        // `x == 0` branch (e.g. `RawVec::allocate_in`'s zero-capacity path) is
        // pruned.
        self.mark_assert_nonzero(cond, *expected, cs);
        let cond_local = match cond {
            Operand::Copy(p) | Operand::Move(p) => p.local.as_usize(),
            Operand::Constant(c) => {
                let typing_env =
                    rustc_middle::ty::TypingEnv::post_analysis(self.cfg.tcx, self.cfg.def_id);
                return c
                    .const_
                    .try_eval_bool(self.cfg.tcx, typing_env)
                    .unwrap_or(true);
            }
            #[cfg(rapx_ge_95)]
            Operand::RuntimeChecks(_) => return true,
        };
        self.resolve_bool_local(cond_local, cs)
            .is_none_or(|v| v == 1)
    }

    /// Mark `lhs` as non-zero when the assert condition is `lhs > 0` / `!= 0`.
    fn mark_assert_nonzero(&self, cond: &Operand<'_>, expected: bool, cs: &mut ConstraintSet) {
        if !expected {
            return;
        }
        let (Operand::Copy(p) | Operand::Move(p)) = cond else {
            return;
        };
        let cond_local = p.local.as_usize();
        let Some(LocalOrigin::Expr(Expr::Cmp { op, lhs, rhs })) = self
            .block_info
            .iter()
            .find_map(|info| info.origin.get(&cond_local).cloned())
        else {
            return;
        };
        let nonzero = matches!(
            (op, rhs),
            (BinOp::Gt, Rhs::Const(0)) | (BinOp::Ge, Rhs::Const(1)) | (BinOp::Ne, Rhs::Const(0))
        );
        if nonzero {
            cs.consts.insert(lhs, usize::MAX);
        }
    }

    /// Record the relational fact `lhs < rhs` (strict) or `lhs <= rhs` (non-strict).
    fn record_bound(cs: &mut ConstraintSet, lhs: usize, rhs: usize, strict: bool) {
        let entry = cs.bounds.entry(lhs).or_default();
        if !entry.iter().any(|&(r, s)| r == rhs && s == strict) {
            entry.push((rhs, strict));
        }
    }

    /// Is `lhs <= rhs` known (either `lhs < rhs` or `lhs <= rhs` recorded)?
    fn bound_le_known(&self, lhs: usize, rhs: usize, cs: &ConstraintSet) -> bool {
        cs.bounds
            .get(&lhs)
            .is_some_and(|v| v.iter().any(|&(r, _)| r == rhs))
    }

    /// Is `lhs < rhs` known (a strict bound recorded)?
    fn bound_lt_known(&self, lhs: usize, rhs: usize, cs: &ConstraintSet) -> bool {
        cs.bounds
            .get(&lhs)
            .is_some_and(|v| v.iter().any(|&(r, s)| r == rhs && s))
    }

    /// Resolve an order comparison to `Some(true)` / `Some(false)` from the
    /// recorded relational bounds, or `None` when undetermined.
    fn relation_status(&self, op: BinOp, lhs: usize, rhs: Rhs, cs: &ConstraintSet) -> Option<bool> {
        let l = self.canonical_field(lhs);
        let r = match rhs {
            Rhs::Const(v) => v,
            Rhs::Local(l) => self.canonical_field(l),
        };
        match op {
            BinOp::Lt => {
                if self.bound_lt_known(l, r, cs) {
                    return Some(true);
                }
                if self.bound_le_known(r, l, cs) {
                    return Some(false);
                }
                None
            }
            BinOp::Le => {
                if self.bound_le_known(l, r, cs) {
                    return Some(true);
                }
                if self.bound_lt_known(r, l, cs) {
                    return Some(false);
                }
                None
            }
            BinOp::Gt => {
                if self.bound_lt_known(r, l, cs) {
                    return Some(true);
                }
                if self.bound_le_known(l, r, cs) {
                    return Some(false);
                }
                None
            }
            BinOp::Ge => {
                if self.bound_le_known(r, l, cs) {
                    return Some(true);
                }
                if self.bound_lt_known(l, r, cs) {
                    return Some(false);
                }
                None
            }
            _ => None,
        }
    }

    /// Canonicalize a local to a stable key, following field projections and
    /// whole-place copies.
    fn canonical_field(&self, local: usize) -> usize {
        let mut cur = local;
        let mut seen = FxHashSet::default();
        loop {
            if !seen.insert(cur) {
                return cur;
            }
            if let Some(&encoded) = self.field_projection_source.get(&cur) {
                cur = encoded;
                continue;
            }
            let mut next: Option<usize> = None;
            for info in &self.block_info {
                if let Some(&src) = info.origin.get(&cur).and_then(LocalOrigin::as_copy) {
                    next = Some(src);
                    break;
                }
            }
            match next {
                Some(src) => cur = src,
                None => return cur,
            }
        }
    }

    /// Resolve a slice-length fact `(start, end)` for `local`, following copies,
    /// field projections, and reborrows.
    fn resolve_length(&self, local: usize, cs: &ConstraintSet) -> Option<(usize, usize)> {
        let mut stack = vec![local];
        let mut seen = FxHashSet::default();
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur) {
                continue;
            }
            if let Some(&len) = cs.lengths.get(&cur) {
                return Some(len);
            }
            for info in &self.block_info {
                if let Some(&src) = info.origin.get(&cur).and_then(LocalOrigin::as_copy) {
                    stack.push(src);
                }
            }
            if let Some(&encoded) = self.field_projection_source.get(&cur) {
                if let Some((agg, field)) = decode_aggregate_field(encoded)
                    && let Some(&actual) = self
                        .aggregate_field_sources
                        .get(&encode_aggregate_field(agg, field))
                {
                    stack.push(actual);
                }
            }
            if let Some(&ref_src) = self.reborrow_referents.get(&cur) {
                stack.push(ref_src);
            }
        }
        None
    }

    /// Resolve `local` to `(base, index, k)` where `local == base + index + k`;
    /// `index` is `usize::MAX` when there is no secondary variable.
    fn resolve_sum(&self, local: usize) -> Option<(usize, usize, usize)> {
        let mut cur = local;
        let mut seen = FxHashSet::default();
        loop {
            if !seen.insert(cur) {
                return None;
            }
            // A field projection is not an integer sum.
            if self.field_projection_source.contains_key(&cur) {
                return None;
            }
            let mut next: Option<usize> = None;
            for info in &self.block_info {
                if let Some(&src) = info.origin.get(&cur).and_then(LocalOrigin::as_copy) {
                    next = Some(src);
                    break;
                }
            }
            match next {
                Some(src) => cur = src,
                None => break,
            }
        }
        for info in &self.block_info {
            if let Some(LocalOrigin::Expr(Expr::Add { lhs, rhs })) = info.origin.get(&cur) {
                return match rhs {
                    Rhs::Local(r) => {
                        let (r_base, r_k) = self.resolve_rhs_sum(*r);
                        Some((*lhs, r_base, r_k))
                    }
                    Rhs::Const(k) => Some((*lhs, usize::MAX, *k)),
                };
            }
        }
        Some((cur, usize::MAX, 0))
    }

    /// Resolve the `rhs` of an add to `(base, k)` (`rhs == base + k`),
    /// following field projections and copies to the underlying increment.
    fn resolve_rhs_sum(&self, rhs: usize) -> (usize, usize) {
        let mut cur = rhs;
        let mut seen = FxHashSet::default();
        loop {
            if !seen.insert(cur) {
                return (cur, 0);
            }
            if let Some(&encoded) = self.field_projection_source.get(&cur) {
                if let Some((agg, _)) = decode_aggregate_field(encoded) {
                    cur = agg;
                    continue;
                }
            }
            let mut next: Option<usize> = None;
            for info in &self.block_info {
                if let Some(&src) = info.origin.get(&cur).and_then(LocalOrigin::as_copy) {
                    next = Some(src);
                    break;
                }
            }
            match next {
                Some(src) => cur = src,
                None => break,
            }
        }
        for info in &self.block_info {
            if let Some(LocalOrigin::Expr(Expr::Add {
                lhs,
                rhs: Rhs::Const(k),
            })) = info.origin.get(&cur)
            {
                return (*lhs, *k);
            }
        }
        (cur, 0)
    }

    /// Derive `local <= end` from `local = base + index + k`, a bound
    /// `index < len`/`index <= len`, and a length `len == end - base`.
    fn derive_increment_bound(&self, local: usize, cs: &mut ConstraintSet) {
        let Some((base, index, k)) = self.resolve_sum(local) else {
            return;
        };
        if index == usize::MAX {
            return;
        }
        let canonical = self.canonical_field(index);
        let mut bounds: Vec<(usize, bool)> = Vec::new();
        if let Some(b) = cs.bounds.get(&index) {
            bounds.extend_from_slice(b);
        }
        if canonical != index
            && let Some(b) = cs.bounds.get(&canonical)
        {
            bounds.extend_from_slice(b);
        }
        for &(len, strict) in &bounds {
            let Some(&(start, end)) = cs.lengths.get(&len) else {
                continue;
            };
            if self.canonical_field(start) != base {
                continue;
            }
            let out = if strict {
                match k {
                    0 => Some((end, true)),
                    1 => Some((end, false)),
                    _ => None,
                }
            } else if k == 0 {
                Some((end, false))
            } else {
                None
            };
            if let Some((rhs, s)) = out {
                Self::record_bound(cs, base, self.canonical_field(rhs), s);
            }
        }
    }

    fn resolve_simple_bool(&self, local: usize, cs: &ConstraintSet) -> Option<usize> {
        if let Some(&val) = cs.consts.get(&local)
            && val <= 1
        {
            return Some(val);
        }
        for info in &self.block_info {
            if let Some(&val) = info.origin.get(&local).and_then(LocalOrigin::as_const)
                && val <= 1
            {
                return Some(val);
            }
            if let Some(LocalOrigin::Expr(Expr::Cmp { op, lhs, rhs })) =
                info.origin.get(&local).cloned()
                && matches!(op, BinOp::Eq | BinOp::Ne)
            {
                let is_eq = matches!(op, BinOp::Eq);
                if let Rhs::Const(rhs_val) = rhs {
                    if let Some(lhs_val) = self.resolve_local_value(lhs, cs) {
                        return Some(if is_eq {
                            if lhs_val == rhs_val { 1 } else { 0 }
                        } else {
                            if lhs_val != rhs_val { 1 } else { 0 }
                        });
                    }
                } else if let Rhs::Local(rhs_local) = rhs {
                    let lhs_val = self.resolve_local_value(lhs, cs);
                    let rhs_val = self.resolve_local_value(rhs_local, cs);
                    if let Some(lhs_val) = lhs_val {
                        if let Some(rhs_val) = rhs_val {
                            return Some(if is_eq {
                                if lhs_val == rhs_val { 1 } else { 0 }
                            } else {
                                if lhs_val != rhs_val { 1 } else { 0 }
                            });
                        }
                    } else if let Some(rhs_val) = rhs_val {
                        return Some(if is_eq {
                            if lhs == rhs_val { 1 } else { 0 }
                        } else {
                            if lhs != rhs_val { 1 } else { 0 }
                        });
                    }
                }
            }
        }
        None
    }

    fn resolve_bool_local(&self, local: usize, cs: &ConstraintSet) -> Option<usize> {
        let mut stack = vec![(local, false)];
        let mut seen = FxHashSet::default();
        while let Some((cur, negated)) = stack.pop() {
            let key = if negated { cur | (1 << 31) } else { cur };
            if !seen.insert(key) {
                continue;
            }
            if let Some(v) = self.resolve_simple_bool(cur, cs) {
                return Some(if negated { 1 - v } else { v });
            }
            for info in &self.block_info {
                if let Some(&src) = info.origin.get(&cur).and_then(LocalOrigin::as_copy) {
                    stack.push((src, negated));
                }
                if let Some(LocalOrigin::Expr(Expr::Not { src })) = info.origin.get(&cur) {
                    stack.push((*src, !negated));
                }
                if let Some(LocalOrigin::Expr(Expr::And { lhs, rhs })) = info.origin.get(&cur) {
                    let a = self.resolve_simple_bool(*lhs, cs);
                    let b = self.resolve_simple_bool(*rhs, cs);
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
    fn check_switch_transition(&self, cur: usize, next: usize, cs: &mut ConstraintSet) -> bool {
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

                let discr_ty = discr.ty(&self.cfg.body().local_decls, self.cfg.tcx);
                if matches!(
                    discr_ty.kind(),
                    TyKind::Int(rustc_middle::ty::IntTy::I128)
                        | TyKind::Uint(rustc_middle::ty::UintTy::U128)
                ) {
                    return true;
                }

                // Try to evaluate a concrete constant for the discriminant.
                let const_val = match discr {
                    Operand::Constant(c) => c
                        .const_
                        .eval(
                            self.cfg.tcx,
                            TypingEnv::post_analysis(self.cfg.tcx, self.cfg.def_id),
                            rustc_span::DUMMY_SP,
                        )
                        .ok()
                        .and_then(|value| value.try_to_scalar_int())
                        .and_then(|scalar| usize::try_from(scalar.to_bits(scalar.size())).ok()),
                    _ => None,
                };

                // `T::IS_ZST` for a generic `T` is unevaluated; fold it to
                // `false` (non-ZST).  The `IS_ZST` guard in pointer arithmetic
                // (`add`/`sub`/`offset`) only skips redundant arithmetic (a ZST
                // pointee makes the offset a no-op), so the non-ZST path is
                // correct for ZST too and avoids the ZST branch returning `self`
                // with a stale element offset (e.g. `reverse`'s `end.sub(half_len)`
                // would otherwise return `end` unchanged and fail the downstream
                // `from_raw_parts_mut` `InBound`).
                let mut is_zst_guard = false;
                match discr {
                    Operand::Constant(c) => {
                        if let rustc_middle::mir::Const::Unevaluated(uneval, _) = c.const_
                            && mir_utils::is_sized_type_property(self.cfg.tcx, uneval.def, "IS_ZST")
                        {
                            is_zst_guard = true;
                        }
                    }
                    Operand::Copy(p) | Operand::Move(p) => {
                        let body = self.cfg.body();
                        for bbd in body.basic_blocks.iter() {
                            for stmt in bbd.statements.iter() {
                                let rustc_middle::mir::StatementKind::Assign(assign) = &stmt.kind
                                else {
                                    continue;
                                };
                                let (dest, rvalue) = &**assign;
                                if dest != p {
                                    continue;
                                }
                                if let rustc_middle::mir::Rvalue::Use(operand, ..) = rvalue
                                    && let Operand::Constant(constant) = operand
                                    && let rustc_middle::mir::Const::Unevaluated(uneval, _) =
                                        constant.const_
                                    && mir_utils::is_sized_type_property(
                                        self.cfg.tcx,
                                        uneval.def,
                                        "IS_ZST",
                                    )
                                {
                                    is_zst_guard = true;
                                }
                            }
                        }
                    }
                    _ => {}
                }
                if is_zst_guard {
                    // Only the non-ZST (`false`) arm is reachable.
                    let expected = resolve_switch_target(targets, 0);
                    if next != expected {
                        return false;
                    }
                    if let Some(local) = constraint_local {
                        cs.consts.insert(local, 0);
                    }
                    return true;
                }

                if let Some(val) = const_val {
                    // Discriminant is a literal constant — only one target is
                    // reachable.
                    let expected = resolve_switch_target(targets, val as u128);
                    if next != expected {
                        return false;
                    }
                    if let Some(local) = constraint_local {
                        cs.consts.insert(local, val);
                    }
                    return true;
                }

                if let Some(local) = constraint_local
                    && let Some(&known_val) = cs.consts.get(&local)
                {
                    let expected = resolve_switch_target(targets, known_val as u128);
                    if next != expected {
                        return false;
                    }
                    return true;
                }

                // A `switchInt` on `ptr as usize` (lowered `!ptr.is_null()`): the
                // `0` arm is unreachable when the pointer is known non-null.
                if let Some(discr_local) = discr_local
                    && self.local_is_known_nonnull(cs, discr_local)
                    && targets.iter().any(|(v, _)| v == 0)
                {
                    let zero_target = resolve_switch_target(targets, 0);
                    if next == zero_target {
                        return false;
                    }
                    return true;
                }

                // If the discriminant is a comparison like `x > 0` / `x != 0`
                // and this transition takes the branch where the comparison
                // holds (`otherwise`), mark `x` as known-nonzero so a downstream
                // `x == 0` switch branch (e.g. `RawVec::allocate_in`'s
                // zero-capacity path) is pruned.
                if let Some(discr_local) = discr_local
                    && let Some(info) = self.block_info.get(cur)
                    && let Some(LocalOrigin::Expr(Expr::Cmp { op, lhs, rhs })) =
                        info.origin.get(&discr_local).cloned()
                    && matches!(
                        (op, rhs),
                        (BinOp::Gt, Rhs::Const(0))
                            | (BinOp::Ge, Rhs::Const(1))
                            | (BinOp::Ne, Rhs::Const(0))
                    )
                    && next == targets.otherwise().as_usize()
                {
                    cs.consts.insert(lhs, usize::MAX);
                }

                // Try to infer the discriminant from a comparison source
                // (e.g. `_X = Ne(ptr, 0)`) when we know whether `ptr` is null.
                if let Some(discr_local) = discr_local
                    && let Some(info) = self.block_info.get(cur)
                    && let Some(LocalOrigin::Expr(Expr::Cmp { op, lhs, rhs })) =
                        info.origin.get(&discr_local).cloned()
                    && matches!(op, BinOp::Ne | BinOp::Eq)
                {
                    let is_ne = matches!(op, BinOp::Ne);
                    let compares_zero = matches!(rhs, Rhs::Const(0));
                    let pointer_is_nonnull = compares_zero && self.local_is_known_nonnull(cs, lhs);
                    let pointer_is_null = compares_zero && self.local_is_known_null(cs, lhs);
                    if pointer_is_nonnull {
                        let expected_val = if is_ne { 1 } else { 0 };
                        let expected = resolve_switch_target(targets, expected_val);
                        let val = expected_val as usize;
                        cs.consts.insert(discr_local, val);
                        if let Some(local) = constraint_local {
                            cs.consts.insert(local, val);
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
                        cs.consts.insert(discr_local, val);
                        if let Some(local) = constraint_local {
                            cs.consts.insert(local, val);
                        }
                        if next != expected {
                            return false;
                        }
                        return true;
                    }

                    // General Eq/Ne integer comparison: resolve both operands
                    // and prune the infeasible branch when both are known.
                    let is_eq = matches!(op, BinOp::Eq);
                    let lhs_val = self.resolve_local_value(lhs, cs);
                    let rhs_val = match rhs {
                        Rhs::Const(v) => Some(v),
                        Rhs::Local(l) => self.resolve_local_value(l, cs),
                    };
                    if let (Some(lhs_val), Some(rhs_val)) = (lhs_val, rhs_val) {
                        let val = if is_eq {
                            if lhs_val == rhs_val { 1 } else { 0 }
                        } else {
                            if lhs_val != rhs_val { 1 } else { 0 }
                        };
                        let expected = resolve_switch_target(targets, val as u128);
                        if let Some(local) = constraint_local {
                            cs.consts.insert(local, val);
                        }
                        if next != expected {
                            return false;
                        }
                        return true;
                    }
                }

                // Try to resolve a boolean comparison with concrete-value
                // reasoning (handles Lt/Le/Gt/Ge with fully known operands).
                // Only filter when the discriminant resolves to a definite value
                // from a comparison with BOTH operands as known constants
                // (not derived via add increments, which may be imprecise across
                // SCC boundaries).
                if let Some(discr_local) = discr_local
                    && let Some(info) = self.block_info.get(cur)
                    && let Some(LocalOrigin::Expr(Expr::Cmp { op, lhs, rhs })) =
                        info.origin.get(&discr_local).cloned()
                    && matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
                {
                    // Resolve LHS directly from constants (no increment chains)
                    let lhs_val = self.resolve_local_value_direct(lhs, cs);
                    let rhs_val = match rhs {
                        Rhs::Const(v) => Some(v),
                        Rhs::Local(l) => self.resolve_local_value_direct(l, cs),
                    };
                    if let (Some(lhs), Some(rhs)) = (lhs_val, rhs_val) {
                        let val = match op {
                            BinOp::Lt => {
                                if lhs < rhs {
                                    1
                                } else {
                                    0
                                }
                            }
                            BinOp::Le => {
                                if lhs <= rhs {
                                    1
                                } else {
                                    0
                                }
                            }
                            BinOp::Gt => {
                                if lhs > rhs {
                                    1
                                } else {
                                    0
                                }
                            }
                            BinOp::Ge => {
                                if lhs >= rhs {
                                    1
                                } else {
                                    0
                                }
                            }
                            _ => unreachable!(),
                        };
                        let expected = resolve_switch_target(targets, val as u128);
                        if let Some(local) = constraint_local {
                            cs.consts.insert(local, val);
                        }
                        if next != expected {
                            return false;
                        }
                        return true;
                    }
                }

                // Record and consult relational bounds (`lhs < rhs` /
                // `lhs <= rhs`) for order comparisons over symbolic operands.
                // An inlined `while i < bytes.len()` loop guard establishes
                // `i < bytes.len()` on the body branch, which later prunes an
                // infeasible `i >= bytes.len()` branch.
                if let Some(discr_local) = discr_local
                    && let Some(info) = self.block_info.get(cur)
                    && let Some(LocalOrigin::Expr(Expr::Cmp { op, lhs, rhs })) =
                        info.origin.get(&discr_local).cloned()
                    && matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
                {
                    let taken_true = next == resolve_switch_target(targets, 1);
                    if let Rhs::Local(rhs_local) = rhs {
                        // Canonicalize to `a < b` (strict) / `a <= b` and record
                        // the branch actually taken (its negation on the false arm).
                        let (a, b, strict) = match op {
                            BinOp::Lt => (lhs, rhs_local, true),
                            BinOp::Le => (lhs, rhs_local, false),
                            BinOp::Gt => (rhs_local, lhs, true),
                            BinOp::Ge => (rhs_local, lhs, false),
                            _ => unreachable!(),
                        };
                        if taken_true {
                            Self::record_bound(
                                cs,
                                self.canonical_field(a),
                                self.canonical_field(b),
                                strict,
                            );
                        } else {
                            Self::record_bound(
                                cs,
                                self.canonical_field(b),
                                self.canonical_field(a),
                                !strict,
                            );
                        }
                    }
                    if let Some(holds) = self.relation_status(op, lhs, rhs, cs) {
                        let expected = resolve_switch_target(targets, holds as u128);
                        if let Some(local) = constraint_local {
                            cs.consts.insert(local, holds as usize);
                        }
                        if next != expected {
                            return false;
                        }
                        return true;
                    }
                }

                // No prior constraint — conservatively allow any valid target
                // and record the newly learned constraint from the taken branch.
                if next == targets.otherwise().as_usize()
                    && let Some(local) = constraint_local
                    && let Some(num_variants) = self.get_variant_count(local)
                {
                    let all_covered =
                        (0..num_variants).all(|v| targets.iter().any(|(tv, _)| tv == v as u128));
                    if all_covered {
                        return false;
                    }
                }

                self.learn_constraint_with_backprop(cur, constraint_local, targets, next, cs);

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
        cs: &mut ConstraintSet,
    ) {
        let Some(local) = constraint_local else {
            return;
        };
        let Some((val, _)) = targets.iter().find(|(_, bb)| bb.as_usize() == next) else {
            if let Some(inferred) = self.infer_otherwise_value(targets, local) {
                cs.consts.insert(local, inferred);
                self.backprop_constraint(cur, local, inferred, cs);
            }
            return;
        };
        let val = val as usize;
        cs.consts.insert(local, val);
        self.backprop_constraint(cur, local, val, cs);
    }

    fn backprop_constraint(&self, cur: usize, local: usize, val: usize, cs: &mut ConstraintSet) {
        let Some(info) = self.block_info.get(cur) else {
            return;
        };
        let mut current = local;
        while let Some(&src) = info.origin.get(&current).and_then(LocalOrigin::as_copy) {
            if current == src {
                break;
            }
            cs.consts.insert(src, val);
            current = src;
        }
    }

    /// Only use a global origin when the MIR local has a single definition.
    fn unique_origin(&self, local: usize) -> Option<&LocalOrigin> {
        let mut origin = None;
        for info in &self.block_info {
            for &assigned in &info.assigned_locals {
                if assigned == local {
                    if origin.is_some() {
                        return None;
                    }
                    origin = info.origin.get(&local);
                    if origin.is_none() {
                        return None;
                    }
                }
            }
        }
        origin
    }

    fn candidate_origins(&self, local: usize) -> impl Iterator<Item = &LocalOrigin> {
        let limit = if self.conservative_origins {
            usize::from(self.unique_origin(local).is_some())
        } else {
            usize::MAX
        };
        self.block_info
            .iter()
            .filter_map(move |info| info.origin.get(&local))
            .take(limit)
    }

    /// Recursively resolve a local's value through constraint copies,
    /// cast chains, field projections, and aggregate sources (global maps).
    /// Like `resolve_local_value` but does NOT follow increment chains.
    /// Used in conservative path filtering where we need high confidence.
    fn resolve_local_value_direct(&self, local: usize, cs: &ConstraintSet) -> Option<usize> {
        let mut stack = vec![local];
        let mut seen = FxHashSet::default();
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur) {
                continue;
            }
            if let Some(&val) = cs.consts.get(&cur)
                && val != usize::MAX
            {
                return Some(val);
            }
            for origin in self.candidate_origins(cur) {
                if let Some(&src) = origin.as_copy() {
                    stack.push(src);
                }
                if let Some(&val) = origin.as_const() {
                    return Some(val);
                }
            }
            if (!self.conservative_origins || self.unique_origin(cur).is_some())
                && let Some(&cast_src) = self.cast_chains.get(&cur)
            {
                stack.push(cast_src);
            }
        }
        None
    }

    fn resolve_local_value(&self, local: usize, cs: &ConstraintSet) -> Option<usize> {
        let mut stack = vec![(local, 0isize)];
        let mut seen = FxHashSet::default();
        while let Some((cur, offset)) = stack.pop() {
            if !seen.insert(cur) {
                continue;
            }
            if let Some(&val) = cs.consts.get(&cur) {
                if val == usize::MAX {
                    // Sentinel for known-nonnull; not a concrete integer value.
                } else if offset >= 0 {
                    return Some(val + offset as usize);
                } else {
                    return val.checked_sub((-offset) as usize);
                }
            }
            // Follow constraint copies in any block (per-block metadata).
            for origin in self.candidate_origins(cur) {
                if let Some(&src) = origin.as_copy() {
                    stack.push((src, offset));
                }
                if let Some(&val) = origin.as_const() {
                    if offset >= 0 {
                        return Some(val + offset as usize);
                    } else {
                        return val.checked_sub((-offset) as usize);
                    }
                }
                if let LocalOrigin::Expr(Expr::Add {
                    lhs,
                    rhs: Rhs::Const(incr_amt),
                }) = origin
                {
                    stack.push((*lhs, offset + *incr_amt as isize));
                }
                if let LocalOrigin::Expr(Expr::Rem {
                    src: rem_src,
                    divisor: rem_div,
                }) = origin
                    && let Some(src_val) = self.resolve_local_value(*rem_src, cs)
                {
                    let rem = src_val % *rem_div;
                    let result = if offset >= 0 {
                        Some(rem + offset as usize)
                    } else {
                        rem.checked_sub((-offset) as usize)
                    };
                    if let Some(v) = result {
                        return Some(v);
                    }
                }
            }
            // Follow global cast chains.
            if (!self.conservative_origins || self.unique_origin(cur).is_some())
                && let Some(&cast_src) = self.cast_chains.get(&cur)
            {
                stack.push((cast_src, offset));
            }
            // Follow field projection -> aggregate source.
            if (!self.conservative_origins || self.unique_origin(cur).is_some())
                && let Some(&encoded) = self.field_projection_source.get(&cur)
                && let Some((agg_local, field_idx)) = decode_aggregate_field(encoded)
            {
                let key = encode_aggregate_field(agg_local, field_idx);
                if let Some(&source) = self.aggregate_field_sources.get(&key) {
                    stack.push((source, offset));
                }
            }
        }
        None
    }

    /// For the "otherwise" branch of a `SwitchInt`, try to infer the single
    /// concrete value that the discriminant must have (because all other
    /// possible values are covered by explicit targets).
    fn infer_otherwise_value(&self, targets: &SwitchTargets, discr_local: usize) -> Option<usize> {
        let body = self.cfg.body();
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
    fn local_is_known_nonnull(&self, cs: &ConstraintSet, local: usize) -> bool {
        let mut stack = vec![local];
        let mut seen = FxHashSet::default();
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur) {
                continue;
            }
            if let Some(&val) = cs.consts.get(&cur)
                && val > 0
            {
                return true;
            }
            for info in &self.block_info {
                if let Some(&src) = info.origin.get(&cur).and_then(LocalOrigin::as_copy) {
                    stack.push(src);
                }
            }
            if let Some(&cast_src) = self.cast_chains.get(&cur) {
                stack.push(cast_src);
            }
        }
        false
    }

    /// Return true if `local` is known to be a null pointer.
    fn local_is_known_null(&self, cs: &ConstraintSet, local: usize) -> bool {
        let mut stack = vec![local];
        let mut seen = FxHashSet::default();
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur) {
                continue;
            }
            if let Some(&val) = cs.consts.get(&cur)
                && val == 0
            {
                return true;
            }
            for info in &self.block_info {
                if let Some(&src) = info.origin.get(&cur).and_then(LocalOrigin::as_copy) {
                    stack.push(src);
                }
            }
            if let Some(&cast_src) = self.cast_chains.get(&cur) {
                stack.push(cast_src);
            }
        }
        false
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
/// bindings from each block's [`BlockFacts`], sorting them, and
/// hashing the result.  Used by [`PathEnumerator::visited_sccs`] to
/// skip redundant re-entries into the same SCC with the same state.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct ConstraintHash(u64);

impl ConstraintHash {
    fn from_path(path: &[usize], graph: &PathGraph<'_>) -> Self {
        let mut hasher = DefaultHasher::new();
        let mut constraints: ConstraintSet = ConstraintSet::default();

        for &block in path.iter() {
            if let Some(info) = graph.block_info.get(block) {
                for local in &info.assigned_locals {
                    if let Some(&src) = info.origin.get(local).and_then(LocalOrigin::as_copy) {
                        if let Some(&src_val) = constraints.consts.get(&src) {
                            constraints.consts.insert(*local, src_val);
                            continue;
                        }
                        if let Some(&dst_val) = constraints.consts.get(local) {
                            constraints.consts.insert(src, dst_val);
                            constraints.consts.insert(*local, dst_val);
                            continue;
                        }
                    }
                    if let Some(&val) = info.origin.get(local).and_then(LocalOrigin::as_const) {
                        constraints.consts.insert(*local, val);
                        continue;
                    }
                    constraints.consts.remove(local);
                }
            }
        }

        let mut entries: Vec<(usize, usize)> = constraints.consts.into_iter().collect();
        entries.sort();
        entries.hash(&mut hasher);
        ConstraintHash(hasher.finish())
    }
}

/// Builds a [`PathTree`] by depth-first enumeration of whole-CFG paths.
///
/// The enumerator holds a `&PathGraph` (which must have `find_scc()` called
/// beforehand) and two caches:
///
/// The **constraint hash** used by `visited_sccs` is a
/// [`ConstraintHash`]: it walks the current path prefix, accumulates
/// `(local → constant_value)` bindings from each block's
/// [`BlockFacts`], sorts them, and hashes the result.  Different
/// constraint states (e.g. a loop variable changing from `true` to
/// `false`) produce different hashes.
///
/// 1. `scc_paths` — maps `(entry, repeat)` to a list of acyclic paths through
///    that SCC.  Reused across repeated enumerations of the same function
///    with different repeat counts.
///
/// 2. `visited_sccs` — set of `(entry, constraint)` entries already explored.
///    When the same SCC is reached with the same constraint state, its
///    sub-paths are identical, so the re-entry is skipped.
///
/// Enumeration filters single-function paths with
/// [`PathGraph::check_transition`]. The symbolic VM checks feasibility after
/// verification composes paths across calls.
pub struct PathEnumerator<'g, 'tcx> {
    graph: &'g PathGraph<'tcx>,
    scc_paths: FxHashMap<(usize, usize), Rc<Vec<SccPath>>>,
    visited_sccs: FxHashSet<(usize, ConstraintHash)>,
    coverage_targets: FxHashSet<usize>,
    covered_prefixes: FxHashSet<Vec<usize>>,
}

impl<'g, 'tcx> PathEnumerator<'g, 'tcx> {
    pub fn new(graph: &'g PathGraph<'tcx>) -> Self {
        PathEnumerator {
            graph,
            scc_paths: FxHashMap::default(),
            visited_sccs: FxHashSet::default(),
            coverage_targets: FxHashSet::default(),
            covered_prefixes: FxHashSet::default(),
        }
    }

    pub fn with_coverage_targets(mut self, targets: impl IntoIterator<Item = usize>) -> Self {
        self.coverage_targets.extend(targets);
        self
    }

    fn coverage_limit_reached(&self, tree: &PathTree) -> bool {
        let limit = crate::limit::path_limit();
        if self.coverage_targets.is_empty() {
            tree.len() >= limit
        } else {
            self.covered_prefixes.len() >= limit.saturating_mul(self.coverage_targets.len())
                || tree.len() >= limit.saturating_mul(128)
        }
    }

    fn record_path(&mut self, tree: &mut PathTree, path: &[usize]) {
        if tree.insert(path) {
            for (index, block) in path.iter().enumerate() {
                if self.coverage_targets.contains(block) {
                    self.covered_prefixes.insert(path[..=index].to_vec());
                }
            }
        }
    }

    /// Enumerate whole-CFG paths, optionally filtering infeasible transitions.
    ///
    /// SCC regions are flattened into a bounded set of acyclic paths.
    pub fn enumerate_paths(&mut self) -> PathTree {
        self.enumerate_paths_repeat(0)
    }

    /// Enumerate whole-CFG paths allowing each SCC postfix segment to repeat
    /// up to `postfix_repeat` additional times. `postfix_repeat = 0` gives
    /// the same result as `enumerate_paths`.
    ///
    /// Enumeration stops once [`crate::limit::path_limit`] paths are
    /// collected and the tree is marked truncated.
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
            &ConstraintSet::default(),
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
    ) -> Rc<Vec<SccPath>> {
        let cache_key = (scc.enter, postfix_repeat);
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
            &ConstraintSet::default(),
            postfix_repeat,
            &mut out,
            &mut seen,
            0,
        );
        out.sort_by_key(|path| path.blocks.len());

        if self.scc_paths.len() >= SCC_PATH_CACHE_LIMIT {
            self.scc_paths.clear();
        }
        let out = Rc::new(out);
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
        constraints: &ConstraintSet,
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

        if cur == scc.enter
            && path.len() > 1
            && !check_postfix_segment(path, scc.enter, segment_counts, postfix_repeat)
        {
            if (postfix_repeat > 0 || segment_counts.len() > 1)
                && scc.exits.iter().any(|e| e.exit == cur)
            {
                self.record_unique_path(path, scc, out, seen_paths);
            }
            return;
        }

        if scc.exits.iter().any(|e| e.exit == cur) {
            self.record_unique_path(path, scc, out, seen_paths);
        }

        let is_child = scc.child_sccs.contains(&cur);

        if is_child {
            let ctx = self.constraint_context(path);
            if !self.visited_sccs.insert((cur, ctx)) {
                return;
            }

            let child_scc = self.graph.cfg_block(cur).scc.clone();
            let child_paths = self.find_scc_paths_repeat(cur, &child_scc, postfix_repeat);

            for child_path in child_paths.iter() {
                let orig_len = path.len();
                let mut child_constraints = constraints.clone();
                let mut reachable = true;
                for pair in child_path.blocks.windows(2) {
                    if !self
                        .graph
                        .check_transition(pair[0], pair[1], &mut child_constraints)
                    {
                        reachable = false;
                        break;
                    }
                }
                if !reachable {
                    continue;
                }
                if child_path.blocks.len() > 1 {
                    path.extend(&child_path.blocks[1..]);
                }

                let mut branch_counts = segment_counts.clone();
                for &next in &child_path.exit_successors {
                    let mut next_constraints = child_constraints.clone();
                    if !self.graph.check_transition(
                        *path.last().unwrap(),
                        next,
                        &mut next_constraints,
                    ) {
                        continue;
                    }
                    path.push(next);
                    self.dfs_scc_tree(
                        scc,
                        next,
                        path,
                        &mut branch_counts,
                        &next_constraints,
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
            let mut next_constraints = constraints.clone();
            if !self
                .graph
                .check_transition(cur, next, &mut next_constraints)
            {
                continue;
            }
            let mut branch_counts = saved_counts.clone();
            path.push(next);
            self.dfs_scc_tree(
                scc,
                next,
                path,
                &mut branch_counts,
                &next_constraints,
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

    fn collect_whole_cfg_paths(
        &mut self,
        current: usize,
        path: &mut Vec<usize>,
        tree: &mut PathTree,
        depth: usize,
        postfix_repeat: usize,
        cs: &ConstraintSet,
    ) {
        if current >= self.graph.cfg.blocks.len() {
            return;
        }
        if depth > WHOLE_CFG_PATH_DEPTH_LIMIT || self.coverage_limit_reached(tree) {
            tree.mark_truncated();
            return;
        }

        let scc_info = self.graph.cfg_block(current).scc.clone();
        let is_scc = current == scc_info.enter && !scc_info.nodes.is_empty();
        if is_scc {
            let scc = self.sort_scc_tree(&scc_info);
            let segments = self.find_scc_paths_repeat(current, &scc, postfix_repeat);

            if segments.is_empty() {
                self.record_path(tree, path);
                return;
            }

            for seg in segments.iter() {
                if self.coverage_limit_reached(tree) {
                    tree.mark_truncated();
                    break;
                }

                let segment_depth = seg.blocks.len().saturating_sub(1);
                if depth.saturating_add(segment_depth) > WHOLE_CFG_PATH_DEPTH_LIMIT {
                    tree.mark_truncated();
                    continue;
                }

                let orig_len = path.len();
                let mut seg_constraints = cs.clone();
                let mut reachable = true;
                if seg.blocks.len() > 1 {
                    for pair in seg.blocks.windows(2) {
                        if !self
                            .graph
                            .check_transition(pair[0], pair[1], &mut seg_constraints)
                        {
                            reachable = false;
                            break;
                        }
                    }
                    if reachable {
                        path.extend_from_slice(&seg.blocks[1..]);
                    }
                }
                if !reachable {
                    continue;
                }

                if seg.exit_successors.is_empty() {
                    self.record_path(tree, path);
                } else {
                    for &next in &seg.exit_successors {
                        let mut next_constraints = seg_constraints.clone();
                        if !self.graph.check_transition(
                            *path.last().unwrap(),
                            next,
                            &mut next_constraints,
                        ) {
                            continue;
                        }
                        path.push(next);
                        self.collect_whole_cfg_paths(
                            next,
                            path,
                            tree,
                            depth + segment_depth + 1,
                            postfix_repeat,
                            &next_constraints,
                        );
                        path.pop();
                    }
                }

                path.truncate(orig_len);
            }
            return;
        }

        let successors: Vec<usize> = self.graph.cfg_block(current).next.iter().copied().collect();
        if successors.is_empty() {
            self.record_path(tree, path);
            return;
        }

        for next in successors {
            let mut next_constraints = cs.clone();
            if !self
                .graph
                .check_transition(current, next, &mut next_constraints)
            {
                continue;
            }
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
