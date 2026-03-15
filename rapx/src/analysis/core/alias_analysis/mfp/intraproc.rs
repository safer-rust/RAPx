use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        Body, CallReturnPlaces, Location, Operand, Place, Rvalue, Statement, StatementKind,
        Terminator, TerminatorEdges, TerminatorKind,
    },
    ty::{self, Ty, TyCtxt, TypingEnv},
};
use rustc_mir_dataflow::{Analysis, JoinSemiLattice, fmt::DebugWithContext};
use std::cell::RefCell;
use std::rc::Rc;

use super::super::{FnAliasMap, FnAliasPairs};
use super::transfer;
use crate::analysis::core::alias_analysis::default::types::is_not_drop;

/// Apply a function summary to the current state
fn apply_function_summary<'tcx>(
    state: &mut AliasDomain,
    destination: Place<'tcx>,
    args: &[Operand<'tcx>],
    summary: &FnAliasPairs,
    place_info: &PlaceInfo<'tcx>,
) {
    // Convert destination to PlaceId
    let dest_id = transfer::mir_place_to_place_id(destination);

    // Build a mapping from callee's argument indices to caller's PlaceIds
    // Index 0 is return value, indices 1+ are arguments
    let mut actual_places = vec![dest_id.clone()];
    for arg in args {
        if let Some(arg_id) = transfer::operand_to_place_id(arg) {
            actual_places.push(arg_id);
        } else {
            // If argument is not a place (e.g., constant), use a dummy
            actual_places.push(PlaceId::Local(usize::MAX));
        }
    }

    // Apply each alias pair from the summary
    for alias_pair in summary.aliases() {
        let left_idx = alias_pair.left_local();
        let right_idx = alias_pair.right_local();

        // Check bounds
        if left_idx >= actual_places.len() || right_idx >= actual_places.len() {
            continue;
        }

        // Skip if either place is a dummy (constant argument)
        // Dummy places use usize::MAX as a sentinel value
        if actual_places[left_idx] == PlaceId::Local(usize::MAX)
            || actual_places[right_idx] == PlaceId::Local(usize::MAX)
        {
            continue;
        }

        // Get actual places with field projections
        let mut left_place = actual_places[left_idx].clone();
        for &field_idx in alias_pair.lhs_fields() {
            left_place = left_place.project_field(field_idx);
        }

        let mut right_place = actual_places[right_idx].clone();
        for &field_idx in alias_pair.rhs_fields() {
            right_place = right_place.project_field(field_idx);
        }

        // Get indices and union
        if let (Some(left_place_idx), Some(right_place_idx)) = (
            place_info.get_index(&left_place),
            place_info.get_index(&right_place),
        ) {
            let left_may_drop = place_info.may_drop(left_place_idx);
            let right_may_drop = place_info.may_drop(right_place_idx);
            if left_may_drop && right_may_drop {
                state.union(left_place_idx, right_place_idx);
            }
        }
    }
}

/// Conservative fallback for library functions without MIR
/// Assumes return value may alias with any may_drop argument
fn apply_conservative_alias_for_call<'tcx>(
    state: &mut AliasDomain,
    destination: Place<'tcx>,
    args: &[rustc_span::source_map::Spanned<rustc_middle::mir::Operand<'tcx>>],
    place_info: &PlaceInfo<'tcx>,
) {
    // Get destination place
    let dest_id = transfer::mir_place_to_place_id(destination);
    let dest_idx = match place_info.get_index(&dest_id) {
        Some(idx) => idx,
        None => {
            return;
        }
    };

    // Only apply if destination may_drop
    if !place_info.may_drop(dest_idx) {
        return;
    }

    // Union with all may_drop arguments
    for (_i, arg) in args.iter().enumerate() {
        if let Some(arg_id) = transfer::operand_to_place_id(&arg.node) {
            if let Some(arg_idx) = place_info.get_index(&arg_id) {
                if place_info.may_drop(arg_idx) {
                    // Create conservative alias
                    state.union(dest_idx, arg_idx);

                    // Sync fields for more precision
                    transfer::sync_fields(state, &dest_id, &arg_id, place_info);
                }
            }
        }
    }
}

/// Place identifier supporting field-sensitive analysis
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PlaceId {
    /// A local variable (e.g., _1)
    Local(usize),
    /// A field projection (e.g., _1.0)
    Field {
        base: Box<PlaceId>,
        field_idx: usize,
    },
}

impl PlaceId {
    /// Get the root local of this place
    pub fn root_local(&self) -> usize {
        match self {
            PlaceId::Local(idx) => *idx,
            PlaceId::Field { base, .. } => base.root_local(),
        }
    }

    /// Create a field projection
    pub fn project_field(&self, field_idx: usize) -> PlaceId {
        PlaceId::Field {
            base: Box::new(self.clone()),
            field_idx,
        }
    }

    /// Check if this place has the given place as a prefix
    /// e.g., _1.0.1 has prefix _1, _1.0.1 has prefix _1.0, but not _2
    pub fn has_prefix(&self, prefix: &PlaceId) -> bool {
        if self == prefix {
            return true;
        }

        match self {
            PlaceId::Local(_) => false,
            PlaceId::Field { base, .. } => base.has_prefix(prefix),
        }
    }
}

/// Information about all places in a function
#[derive(Clone)]
pub struct PlaceInfo<'tcx> {
    /// Mapping from PlaceId to index
    place_to_index: FxHashMap<PlaceId, usize>,
    /// Mapping from index to PlaceId
    index_to_place: Vec<PlaceId>,
    /// Mapping from PlaceId to MIR Place (when available)
    place_to_mir: FxHashMap<PlaceId, Place<'tcx>>,
    /// Whether each place may need drop
    may_drop: Vec<bool>,
    /// Whether each place needs drop
    need_drop: Vec<bool>,
    /// Total number of places
    num_places: usize,
}

impl<'tcx> PlaceInfo<'tcx> {
    /// Create a new PlaceInfo with initial capacity
    pub fn new() -> Self {
        PlaceInfo {
            place_to_index: FxHashMap::default(),
            index_to_place: Vec::new(),
            place_to_mir: FxHashMap::default(),
            may_drop: Vec::new(),
            need_drop: Vec::new(),
            num_places: 0,
        }
    }

    /// Build PlaceInfo from MIR body
    pub fn build(tcx: TyCtxt<'tcx>, def_id: DefId, body: &'tcx Body<'tcx>) -> Self {
        let mut info = Self::new();
        let ty_env = TypingEnv::post_analysis(tcx, def_id);

        // Register all locals first
        for (local, local_decl) in body.local_decls.iter_enumerated() {
            let ty = local_decl.ty;
            let need_drop = ty.needs_drop(tcx, ty_env);
            let may_drop = !is_not_drop(tcx, ty);

            let place_id = PlaceId::Local(local.as_usize());
            info.register_place(place_id.clone(), may_drop, need_drop);

            // Create fields for this type recursively
            info.create_fields_for_type(tcx, ty, place_id, 0, 0, ty_env);
        }

        info
    }

    /// Recursively create field PlaceIds for a type
    fn create_fields_for_type(
        &mut self,
        tcx: TyCtxt<'tcx>,
        ty: Ty<'tcx>,
        base_place: PlaceId,
        field_depth: usize,
        deref_depth: usize,
        ty_env: TypingEnv<'tcx>,
    ) {
        // Limit recursion depth to avoid infinite loops
        const MAX_FIELD_DEPTH: usize = 5;
        const MAX_DEREF_DEPTH: usize = 3;
        if field_depth >= MAX_FIELD_DEPTH || deref_depth >= MAX_DEREF_DEPTH {
            return;
        }

        match ty.kind() {
            // For references, recursively create fields for the inner type
            // This allows handling patterns like (*_1).0 where _1 is &T
            ty::Ref(_, inner_ty, _) => {
                self.create_fields_for_type(
                    tcx,
                    *inner_ty,
                    base_place,
                    field_depth,
                    deref_depth + 1,
                    ty_env,
                );
            }
            // For raw pointers, also create fields for the inner type
            ty::RawPtr(inner_ty, _) => {
                self.create_fields_for_type(
                    tcx,
                    *inner_ty,
                    base_place,
                    field_depth,
                    deref_depth + 1,
                    ty_env,
                );
            }
            // For ADTs (structs/enums), create fields
            ty::Adt(adt_def, substs) => {
                for (field_idx, field) in adt_def.all_fields().enumerate() {
                    let field_ty = field.ty(tcx, substs);
                    let field_place = base_place.project_field(field_idx);

                    // Check if field may/need drop
                    // Use the ty_env from the function context to avoid param-env mismatch
                    let need_drop = field_ty.needs_drop(tcx, ty_env);

                    // Special handling: when deref_depth > 0, we are creating fields for
                    // a type accessed through a reference/pointer (e.g., (*_1).0 where _1 is &T).
                    // In this case, even if the field type itself doesn't need drop (e.g., i32),
                    // we should still track it for alias analysis because it represents memory
                    // accessed through a reference.
                    let may_drop = if deref_depth > 0 {
                        true
                    } else {
                        !is_not_drop(tcx, field_ty)
                    };

                    self.register_place(field_place.clone(), may_drop, need_drop);

                    // Recursively create nested fields
                    self.create_fields_for_type(
                        tcx,
                        field_ty,
                        field_place,
                        field_depth + 1,
                        deref_depth,
                        ty_env,
                    );
                }
            }
            // For tuples, create fields
            ty::Tuple(fields) => {
                for (field_idx, field_ty) in fields.iter().enumerate() {
                    let field_place = base_place.project_field(field_idx);

                    // For tuples, we conservatively check drop requirements
                    // Note: Tuple fields don't have a specific DefId, so we use a simpler check

                    // Special handling: when deref_depth > 0, we are creating fields for
                    // a type accessed through a reference/pointer. Even if the field type
                    // doesn't need drop, we should track it for alias analysis.
                    let may_drop = if deref_depth > 0 {
                        true
                    } else {
                        !is_not_drop(tcx, field_ty)
                    };

                    // For need_drop, use the ty_env from the function context
                    let need_drop = field_ty.needs_drop(tcx, ty_env);

                    self.register_place(field_place.clone(), may_drop, need_drop);

                    // Recursively create nested fields
                    self.create_fields_for_type(
                        tcx,
                        field_ty,
                        field_place,
                        field_depth + 1,
                        deref_depth,
                        ty_env,
                    );
                }
            }
            _ => {
                // Other types don't have explicit fields we track
            }
        }
    }

    /// Register a new place and return its index
    pub fn register_place(&mut self, place_id: PlaceId, may_drop: bool, need_drop: bool) -> usize {
        if let Some(&idx) = self.place_to_index.get(&place_id) {
            return idx;
        }

        let idx = self.num_places;
        self.place_to_index.insert(place_id.clone(), idx);
        self.index_to_place.push(place_id);
        self.may_drop.push(may_drop);
        self.need_drop.push(need_drop);
        self.num_places += 1;
        idx
    }

    /// Get the index of a place
    pub fn get_index(&self, place_id: &PlaceId) -> Option<usize> {
        self.place_to_index.get(place_id).copied()
    }

    /// Get the PlaceId for an index
    pub fn get_place(&self, idx: usize) -> Option<&PlaceId> {
        self.index_to_place.get(idx)
    }

    /// Check if a place may drop
    pub fn may_drop(&self, idx: usize) -> bool {
        self.may_drop.get(idx).copied().unwrap_or(false)
    }

    /// Check if a place needs drop
    pub fn need_drop(&self, idx: usize) -> bool {
        self.need_drop.get(idx).copied().unwrap_or(false)
    }

    /// Get total number of places
    pub fn num_places(&self) -> usize {
        self.num_places
    }

    /// Associate a MIR place with a PlaceId
    pub fn associate_mir_place(&mut self, place_id: PlaceId, mir_place: Place<'tcx>) {
        self.place_to_mir.insert(place_id, mir_place);
    }
}

/// Alias domain using Union-Find data structure
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AliasDomain {
    /// Parent array for Union-Find
    parent: Vec<usize>,
    /// Rank for path compression
    rank: Vec<usize>,
}

impl AliasDomain {
    /// Create a new domain with n places
    pub fn new(num_places: usize) -> Self {
        AliasDomain {
            parent: (0..num_places).collect(),
            rank: vec![0; num_places],
        }
    }

    /// Find the representative of a place (with path compression)
    pub fn find(&mut self, idx: usize) -> usize {
        if self.parent[idx] != idx {
            self.parent[idx] = self.find(self.parent[idx]);
        }
        self.parent[idx]
    }

    /// Union two places (returns true if they were not already aliased)
    pub fn union(&mut self, idx1: usize, idx2: usize) -> bool {
        let root1 = self.find(idx1);
        let root2 = self.find(idx2);

        if root1 == root2 {
            return false;
        }

        // Union by rank
        if self.rank[root1] < self.rank[root2] {
            self.parent[root1] = root2;
        } else if self.rank[root1] > self.rank[root2] {
            self.parent[root2] = root1;
        } else {
            self.parent[root2] = root1;
            self.rank[root1] += 1;
        }

        true
    }

    /// Check if two places are aliased
    pub fn are_aliased(&mut self, idx1: usize, idx2: usize) -> bool {
        self.find(idx1) == self.find(idx2)
    }

    /// Remove all aliases for a place (used in kill phase)
    /// This correctly handles the case where idx is the root of a connected component
    pub fn remove_aliases(&mut self, idx: usize) {
        // Find the root of the connected component containing idx
        let root = self.find(idx);

        // Collect all nodes in the same connected component
        let mut component_nodes = Vec::new();
        for i in 0..self.parent.len() {
            if self.find(i) == root {
                component_nodes.push(i);
            }
        }

        // Remove idx from the component
        component_nodes.retain(|&i| i != idx);

        // Isolate idx
        self.parent[idx] = idx;
        self.rank[idx] = 0;

        // Rebuild the remaining component if it's not empty
        if !component_nodes.is_empty() {
            // Reset all nodes in the remaining component
            for &i in &component_nodes {
                self.parent[i] = i;
                self.rank[i] = 0;
            }

            // Re-union them together (excluding idx)
            let first = component_nodes[0];
            for &i in &component_nodes[1..] {
                self.union(first, i);
            }
        }
    }

    /// Remove all aliases for a place and all its field projections
    /// This ensures that when lv is killed, all lv.* are also killed
    pub fn remove_aliases_with_prefix(&mut self, place_id: &PlaceId, place_info: &PlaceInfo) {
        // Collect all place indices that have place_id as a prefix
        let mut indices_to_remove = Vec::new();

        for idx in 0..self.parent.len() {
            if let Some(pid) = place_info.get_place(idx) {
                if pid.has_prefix(place_id) {
                    indices_to_remove.push(idx);
                }
            }
        }

        // Remove aliases for all collected indices
        for idx in indices_to_remove {
            self.remove_aliases(idx);
        }
    }

    /// Get all alias pairs (for debugging/summary extraction)
    pub fn get_all_alias_pairs(&self) -> Vec<(usize, usize)> {
        let mut pairs = Vec::new();
        let mut domain_clone = self.clone();

        for i in 0..self.parent.len() {
            for j in (i + 1)..self.parent.len() {
                if domain_clone.are_aliased(i, j) {
                    pairs.push((i, j));
                }
            }
        }

        pairs
    }
}

impl JoinSemiLattice for AliasDomain {
    fn join(&mut self, other: &Self) -> bool {
        // Safety check: both domains must have the same size
        // This ensures they represent the same place space
        assert_eq!(
            self.parent.len(),
            other.parent.len(),
            "AliasDomain::join: size mismatch (self: {}, other: {})",
            self.parent.len(),
            other.parent.len()
        );

        let mut changed = false;

        // Get all alias pairs from other and union them in self
        let pairs = other.get_all_alias_pairs();
        for (i, j) in pairs {
            if self.union(i, j) {
                changed = true;
            }
        }

        changed
    }
}

impl DebugWithContext<FnAliasAnalyzer<'_>> for AliasDomain {}

/// Intraprocedural alias analyzer
pub struct FnAliasAnalyzer<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    _body: &'tcx Body<'tcx>,
    _def_id: DefId,
    place_info: PlaceInfo<'tcx>,
    /// Function summaries for interprocedural analysis
    fn_summaries: Rc<RefCell<FnAliasMap>>,
    /// (Debug) Number of BBs we have iterated through
    pub bb_iter_cnt: RefCell<usize>,
}

impl<'tcx> FnAliasAnalyzer<'tcx> {
    /// Create a new analyzer for a function
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        body: &'tcx Body<'tcx>,
        fn_summaries: Rc<RefCell<FnAliasMap>>,
    ) -> Self {
        // Build place info by analyzing the body
        let place_info = PlaceInfo::build(tcx, def_id, body);
        FnAliasAnalyzer {
            tcx,
            _body: body,
            _def_id: def_id,
            place_info,
            fn_summaries,
            bb_iter_cnt: RefCell::new(0),
        }
    }

    /// Get the place info
    pub fn place_info(&self) -> &PlaceInfo<'tcx> {
        &self.place_info
    }
}

// Implement Analysis for FnAliasAnalyzer
impl<'tcx> Analysis<'tcx> for FnAliasAnalyzer<'tcx> {
    type Domain = AliasDomain;

    const NAME: &'static str = "FnAliasAnalyzer";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        // Bottom is no aliases
        AliasDomain::new(self.place_info.num_places())
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, _state: &mut Self::Domain) {
        // Entry state: no initial aliases between parameters
    }

    fn apply_primary_statement_effect(
        &self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        _location: Location,
    ) {
        match &statement.kind {
            StatementKind::Assign(box (lv, rvalue)) => {
                match rvalue {
                    // Use(operand): lv = operand
                    Rvalue::Use(operand) => {
                        transfer::transfer_assign(state, *lv, operand, &self.place_info);
                    }
                    // Ref: lv = &rv or lv = &raw rv
                    Rvalue::Ref(_, _, rv) | Rvalue::RawPtr(_, rv) => {
                        transfer::transfer_ref(state, *lv, *rv, &self.place_info);
                    }
                    // CopyForDeref: similar to ref
                    Rvalue::CopyForDeref(rv) => {
                        transfer::transfer_ref(state, *lv, *rv, &self.place_info);
                    }
                    // Cast: lv = operand as T
                    Rvalue::Cast(_, operand, _) => {
                        transfer::transfer_assign(state, *lv, operand, &self.place_info);
                    }
                    // Aggregate: lv = (operands...)
                    Rvalue::Aggregate(_, operands) => {
                        let operand_slice: Vec<_> = operands.iter().map(|op| op.clone()).collect();
                        transfer::transfer_aggregate(state, *lv, &operand_slice, &self.place_info);
                    }
                    // ShallowInitBox: lv = ShallowInitBox(operand, T)
                    Rvalue::ShallowInitBox(operand, _) => {
                        transfer::transfer_assign(state, *lv, operand, &self.place_info);
                    }
                    // Other rvalues don't create aliases
                    _ => {}
                }
            }
            // Other statement kinds don't affect alias analysis
            _ => {}
        }
    }

    fn apply_primary_terminator_effect<'mir>(
        &self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        _location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        // (Debug)
        {
            *self.bb_iter_cnt.borrow_mut() += 1;
        }
        match &terminator.kind {
            // Call: apply both kill and gen effects
            // Note: Ideally gen effect should be in apply_call_return_effect, but that method
            // is not being called by rustc's dataflow framework in current version.
            // Therefore, we handle both effects here, following MOP's approach.
            TerminatorKind::Call {
                target,
                destination,
                args,
                func,
                ..
            } => {
                // Step 1: Apply kill effect for the destination
                let operand_slice: Vec<_> = args
                    .iter()
                    .map(|spanned_arg| spanned_arg.node.clone())
                    .collect();
                transfer::transfer_call(state, *destination, &operand_slice, &self.place_info);

                // Step 2: Apply gen effect - function summary or fallback
                if let Operand::Constant(c) = func {
                    if let ty::FnDef(callee_def_id, _) = c.ty().kind() {
                        // Try to get the function summary
                        let fn_summaries = self.fn_summaries.borrow();
                        if let Some(summary) = fn_summaries.get(callee_def_id) {
                            // Apply the function summary
                            apply_function_summary(
                                state,
                                *destination,
                                &operand_slice,
                                summary,
                                &self.place_info,
                            );
                        } else {
                            // No summary available (e.g., library function without MIR)
                            // Drop the borrow before calling the fallback function
                            drop(fn_summaries);

                            // Apply conservative fallback: assume return value may alias with any may_drop argument
                            apply_conservative_alias_for_call(
                                state,
                                *destination,
                                args,
                                &self.place_info,
                            );
                        }
                    } else {
                        // FnPtr? Closure?
                        // rap_warn!(
                        //     "[MFP-alias] Ignoring call to {:?} because it's not a FnDef",
                        //     c
                        // );
                    }
                }

                // Step 3: Return control flow edges
                if let Some(target_bb) = target {
                    TerminatorEdges::Single(*target_bb)
                } else {
                    TerminatorEdges::None
                }
            }

            // Drop: doesn't affect alias relationships
            TerminatorKind::Drop { target, .. } => TerminatorEdges::Single(*target),

            // SwitchInt: return all possible edges
            TerminatorKind::SwitchInt { discr, targets } => {
                TerminatorEdges::SwitchInt { discr, targets }
            }

            // Assert: return normal edge
            TerminatorKind::Assert { target, .. } => TerminatorEdges::Single(*target),

            // Goto: return target
            TerminatorKind::Goto { target } => TerminatorEdges::Single(*target),

            // Return: no successors
            TerminatorKind::Return => TerminatorEdges::None,

            // All other terminators: assume no successors for safety
            _ => TerminatorEdges::None,
        }
    }

    fn apply_call_return_effect(
        &self,
        _state: &mut Self::Domain,
        _block: rustc_middle::mir::BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        // Note: This method is part of the rustc Analysis trait but is not being called
        // by the dataflow framework in current rustc version when using iterate_to_fixpoint.
        // The call return effect (gen effect) is instead handled directly in
        // apply_primary_terminator_effect to ensure it is actually executed.
        // This is consistent with how MOP analysis handles function calls.
    }
}
