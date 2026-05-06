//! Dominated graph state model for Senryx MIR analysis.
//!
//! The graph stores MIR locals, synthetic memory objects, field-sensitive nodes,
//! points-to relationships, contract fact sets, and operational
//! trace states (OTS). Checkers query this graph to decide whether an unsafe
//! call's safety contracts are satisfied on the current path.

use crate::analysis::{
    senryx::{
        contract::{AlignState, ContractExpr, ContractFactSet, PropertyContract},
        symbolic_analysis::{AnaOperand, SymbolicDef},
    },
    utils::fn_info::{display_hashmap, get_pointee, is_ptr, is_ref, is_slice},
};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::BinOp;
use rustc_middle::mir::Local;
use rustc_middle::ty::TyKind;
use rustc_middle::ty::{Ty, TyCtxt};
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

/// A collection of state properties for a memory location.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct States<'tcx> {
    pub nonnull: bool,
    pub allocator_consistency: bool,
    pub init: bool,
    pub align: AlignState<'tcx>,
    pub valid_string: bool,
    pub valid_cstr: bool,
}

impl<'tcx> States<'tcx> {
    /// Create a new States instance with default values.
    pub fn new(ty: Ty<'tcx>) -> Self {
        Self {
            nonnull: true,
            allocator_consistency: true,
            init: true,
            align: AlignState::Aligned(ty),
            valid_string: true,
            valid_cstr: true,
        }
    }

    /// Create a new States instance with all fields set to false/unknown.
    pub fn new_unknown() -> Self {
        Self {
            nonnull: false,
            allocator_consistency: false,
            init: false,
            align: AlignState::Unknown,
            valid_string: false,
            valid_cstr: false,
        }
    }

    /// Merge the states of this instance with another.
    pub fn merge_states(&mut self, other: &States<'tcx>) {
        self.nonnull &= other.nonnull;
        self.allocator_consistency &= other.allocator_consistency;
        self.init &= other.init;
        self.align = self.align.merge(&other.align);
        self.valid_string &= other.valid_string;
        self.valid_cstr &= other.valid_cstr;
    }
}

/// A node in the intermediate result graph.
#[derive(Debug, Clone)]
pub struct InterResultNode<'tcx> {
    pub point_to: Option<Box<InterResultNode<'tcx>>>,
    pub fields: HashMap<usize, InterResultNode<'tcx>>,
    pub ty: Option<Ty<'tcx>>,
    pub states: States<'tcx>,
    pub const_value: usize,
}

impl<'tcx> InterResultNode<'tcx> {
    /// Create a new InterResultNode with default values.
    pub fn new_default(ty: Option<Ty<'tcx>>) -> Self {
        Self {
            point_to: None,
            fields: HashMap::new(),
            ty,
            states: States::new(ty.unwrap()),
            const_value: 0, // To be modified
        }
    }

    /// Construct an InterResultNode from a VariableNode.
    pub fn construct_from_var_node(chain: DominatedGraph<'tcx>, var_id: usize) -> Self {
        let var_node = chain.get_var_node(var_id).unwrap();
        let point_node = if var_node.points_to.is_none() {
            None
        } else {
            Some(Box::new(Self::construct_from_var_node(
                chain.clone(),
                var_node.points_to.unwrap(),
            )))
        };
        let fields = var_node
            .field
            .iter()
            .map(|(k, v)| (*k, Self::construct_from_var_node(chain.clone(), *v)))
            .collect();
        Self {
            point_to: point_node,
            fields,
            ty: var_node.ty.clone(),
            states: var_node.ots.clone(),
            const_value: var_node.const_value,
        }
    }

    /// Merge the current node with another node.
    pub fn merge(&mut self, other: InterResultNode<'tcx>) {
        if self.ty != other.ty {
            return;
        }
        // merge current node's states
        self.states.merge_states(&other.states);

        // merge node it points to
        match (&mut self.point_to, other.point_to) {
            (Some(self_ptr), Some(other_ptr)) => self_ptr.merge(*other_ptr),
            (None, Some(other_ptr)) => {
                self.point_to = Some(other_ptr.clone());
            }
            _ => {}
        }
        // merge the fields nodess
        for (field_id, other_node) in &other.fields {
            match self.fields.get_mut(field_id) {
                Some(self_node) => self_node.merge(other_node.clone()),
                None => {
                    self.fields.insert(*field_id, other_node.clone());
                }
            }
        }
        // TODO: merge into a range
        self.const_value = std::cmp::max(self.const_value, other.const_value);
    }
}

/// A summary of a function's behavior.
#[derive(Clone, Debug)]
pub struct FunctionSummary<'tcx> {
    pub return_def: Option<SymbolicDef<'tcx>>,
}

impl<'tcx> FunctionSummary<'tcx> {
    /// Create a new FunctionSummary.
    pub fn new(def: Option<SymbolicDef<'tcx>>) -> Self {
        Self { return_def: def }
    }
}

/// A node in the dominated graph.
#[derive(Debug, Clone)]
pub struct VariableNode<'tcx> {
    pub id: usize,
    pub alias_set: HashSet<usize>,
    pub points_to: Option<usize>,
    pub pointed_by: HashSet<usize>,
    pub field: HashMap<usize, usize>,
    pub ty: Option<Ty<'tcx>>,
    pub is_dropped: bool,
    pub ots: States<'tcx>,
    pub const_value: usize,
    pub facts: ContractFactSet<'tcx>,
    pub offset_from: Option<SymbolicDef<'tcx>>,
}

impl<'tcx> VariableNode<'tcx> {
    /// Create a new VariableNode.
    pub fn new(
        id: usize,
        points_to: Option<usize>,
        pointed_by: HashSet<usize>,
        ty: Option<Ty<'tcx>>,
        ots: States<'tcx>,
    ) -> Self {
        VariableNode {
            id,
            alias_set: HashSet::from([id]),
            points_to,
            pointed_by,
            field: HashMap::new(),
            ty,
            is_dropped: false,
            ots,
            const_value: 0,
            facts: ContractFactSet::new_default(),
            offset_from: None,
        }
    }

    /// Create a new VariableNode with default values.
    pub fn new_default(id: usize, ty: Option<Ty<'tcx>>) -> Self {
        VariableNode {
            id,
            alias_set: HashSet::from([id]),
            points_to: None,
            pointed_by: HashSet::new(),
            field: HashMap::new(),
            ty,
            is_dropped: false,
            ots: States::new(ty.unwrap()),
            const_value: 0,
            facts: ContractFactSet::new_default(),
            offset_from: None,
        }
    }

    /// Create a new VariableNode with specific states.
    pub fn new_with_states(id: usize, ty: Option<Ty<'tcx>>, ots: States<'tcx>) -> Self {
        VariableNode {
            id,
            alias_set: HashSet::from([id]),
            points_to: None,
            pointed_by: HashSet::new(),
            field: HashMap::new(),
            ty,
            is_dropped: false,
            ots,
            const_value: 0,
            facts: ContractFactSet::new_default(),
            offset_from: None,
        }
    }
}

/// A dominated graph.
#[derive(Clone)]
pub struct DominatedGraph<'tcx> {
    /// The type context.
    pub tcx: TyCtxt<'tcx>,
    /// The definition ID of the function.
    pub def_id: DefId,
    /// The number of local variables.
    pub local_len: usize,
    /// The variables in the graph. Map from local variable index to VariableNode.
    pub variables: HashMap<usize, VariableNode<'tcx>>,
}

impl<'tcx> DominatedGraph<'tcx> {
    /// Construct a graph for `def_id` and initialize one node for each MIR local.
    ///
    /// Pointer and reference arguments are completed later by `init_arg`, where
    /// they are connected to synthetic object nodes and caller contracts.
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        let body = tcx.optimized_mir(def_id);
        let locals = body.local_decls.clone();
        let mut var_map: HashMap<usize, VariableNode<'_>> = HashMap::new();
        for (idx, local) in locals.iter().enumerate() {
            let local_ty = local.ty;
            let mut node = VariableNode::new_default(idx, Some(local_ty));
            if local_ty.to_string().contains("MaybeUninit") {
                node.ots.init = false;
            }
            var_map.insert(idx, node);
        }
        Self {
            tcx,
            def_id,
            local_len: locals.len(),
            variables: var_map,
        }
    }

    /// Initialize the self node with an intermediate result.
    pub fn init_self_with_inter(&mut self, inter_result: InterResultNode<'tcx>) {
        let self_node = self.get_var_node(1).unwrap().clone();
        if self_node.ty.unwrap().is_ref() {
            let obj_node = self.get_var_node(self.get_point_to_id(1)).unwrap();
            self.dfs_insert_inter_results(inter_result, obj_node.id);
        } else {
            self.dfs_insert_inter_results(inter_result, self_node.id);
        }
    }

    /// Insert intermediate results into the graph.
    pub fn dfs_insert_inter_results(&mut self, inter_result: InterResultNode<'tcx>, local: usize) {
        let new_id = self.generate_node_id();
        let node = self.get_var_node_mut(local).unwrap();
        // node.ty = inter_result.ty;
        node.ots = inter_result.states;
        node.const_value = inter_result.const_value;
        if inter_result.point_to.is_some() {
            let new_node = inter_result.point_to.unwrap();
            node.points_to = Some(new_id);
            self.insert_node(
                new_id,
                new_node.ty.clone(),
                local,
                None,
                new_node.states.clone(),
            );
            self.dfs_insert_inter_results(*new_node, new_id);
        }
        for (field_idx, field_inter) in inter_result.fields {
            let field_node_id = self.insert_field_node(local, field_idx, field_inter.ty.clone());
            self.dfs_insert_inter_results(field_inter, field_node_id);
        }
    }

    /// Initialize the arguments of the function.
    pub fn init_arg(&mut self) {
        // init arg nodes' point to nodes.
        let body = self.tcx.optimized_mir(self.def_id);
        let locals = body.local_decls.clone();
        let fn_sig = self.tcx.fn_sig(self.def_id).skip_binder();
        let param_len = fn_sig.inputs().skip_binder().len();
        for idx in 1..param_len + 1 {
            let local_ty = locals[Local::from(idx)].ty;
            self.generate_ptr_with_obj_node(local_ty, idx);
        }
        // init args' contract facts
        let fact_results = crate::analysis::utils::fn_info::generate_contract_from_annotation(
            self.tcx,
            self.def_id,
        );
        for (base, fields, contract) in fact_results {
            if fields.len() == 0 {
                self.insert_fact_for_arg(base, contract);
            } else {
                let mut cur_base = base;
                let mut field_node = base;
                for field in fields {
                    field_node = self.insert_field_node(cur_base, field.0, Some(field.1));
                    // check if field's type is ptr or ref: yes -> create shadow var
                    self.generate_ptr_with_obj_node(field.1, field_node);
                    cur_base = field_node;
                }
                self.insert_fact_for_arg(field_node, contract);
            }
        }
    }

    /// Insert a contract fact into an argument node.
    fn insert_fact_for_arg(&mut self, local: usize, contract: PropertyContract<'tcx>) {
        let node = self.get_var_node_mut(local).unwrap();
        node.facts.add_contract(contract);
    }

    /// When generate obj node, this function will add InBound Sp automatically.
    pub fn generate_ptr_with_obj_node(&mut self, local_ty: Ty<'tcx>, idx: usize) -> usize {
        let new_id = self.generate_node_id();
        if is_ptr(local_ty) {
            // modify ptr node pointed
            self.get_var_node_mut(idx).unwrap().points_to = Some(new_id);
            self.get_var_node_mut(idx).unwrap().ots = States::new_unknown();
            // insert pointed object node
            self.insert_node(
                new_id,
                Some(get_pointee(local_ty)),
                idx,
                None,
                States::new_unknown(),
            );
            self.add_bound_for_obj(new_id, local_ty);
        } else if is_ref(local_ty) {
            // modify ptr node pointed
            self.get_var_node_mut(idx).unwrap().points_to = Some(new_id);
            // insert ref object node
            self.insert_node(
                new_id,
                Some(get_pointee(local_ty)),
                idx,
                None,
                States::new(get_pointee(local_ty)),
            );
            self.add_bound_for_obj(new_id, local_ty);
        }
        new_id
    }

    /// Add a bound for an object node.
    fn add_bound_for_obj(&mut self, new_id: usize, local_ty: Ty<'tcx>) {
        let new_node = self.get_var_node_mut(new_id).unwrap();
        let new_node_ty = get_pointee(local_ty);
        let contract = if is_slice(new_node_ty).is_some() {
            let inner_ty = is_slice(new_node_ty).unwrap();
            PropertyContract::new_obj_boundary(inner_ty, ContractExpr::new_unknown())
        } else {
            PropertyContract::new_obj_boundary(new_node_ty, ContractExpr::new_value(1))
        };
        new_node.facts.add_contract(contract);
    }

    /// if current node is ptr or ref, then return the new node pointed by it.
    pub fn check_ptr(&mut self, arg: usize) -> usize {
        if self.get_var_node_mut(arg).unwrap().ty.is_none() {
            display_hashmap(&self.variables, 1);
        };
        let node_ty = self.get_var_node_mut(arg).unwrap().ty.unwrap();
        if is_ptr(node_ty) || is_ref(node_ty) {
            return self.generate_ptr_with_obj_node(node_ty, arg);
        }
        arg
    }

    /// Get the type of a local variable by its place.
    pub fn get_local_ty_by_place(&self, arg: usize) -> Option<Ty<'tcx>> {
        let body = self.tcx.optimized_mir(self.def_id);
        let locals = body.local_decls.clone();
        if arg < locals.len() {
            return Some(locals[Local::from(arg)].ty);
        } else {
            // If the arg is a field of some place, we search the whole map for it.
            return self.get_var_node(arg).unwrap().ty;
        }
    }

    /// Get the type of an object through a chain of pointers.
    pub fn get_obj_ty_through_chain(&self, arg: usize) -> Option<Ty<'tcx>> {
        let var = self.get_var_node(arg).unwrap();
        // If the var is ptr or ref, then find its pointed obj.
        if let Some(pointed_idx) = var.points_to {
            self.get_obj_ty_through_chain(pointed_idx)
        } else {
            var.ty
        }
    }

    /// Get the ID of the node pointed to by a pointer or reference.
    pub fn get_point_to_id(&self, arg: usize) -> usize {
        let var = self.get_var_node(arg).unwrap();
        if let Some(pointed_idx) = var.points_to {
            pointed_idx
        } else {
            arg
        }
    }

    /// Check if a node ID corresponds to a local variable.
    pub fn is_local(&self, node_id: usize) -> bool {
        self.local_len > node_id
    }
}

// This implementation has the auxiliary functions of DominatedGraph,
// including c/r/u/d nodes and printing chains' structure.
impl<'tcx> DominatedGraph<'tcx> {
    /// Return the next synthetic node id for field or pointee object nodes.
    pub fn generate_node_id(&self) -> usize {
        if self.variables.len() == 0 || *self.variables.keys().max().unwrap() < self.local_len {
            return self.local_len;
        }
        *self.variables.keys().max().unwrap() + 1
    }

    /// Get or create the synthetic node for `local.field_idx`.
    pub fn get_field_node_id(
        &mut self,
        local: usize,
        field_idx: usize,
        ty: Option<Ty<'tcx>>,
    ) -> usize {
        let node = self.get_var_node(local).unwrap();
        if let Some(alias_local) = node.field.get(&field_idx) {
            *alias_local
        } else {
            self.insert_field_node(local, field_idx, ty)
        }
    }

    /// Insert a field node under `local` and return the generated node id.
    pub fn insert_field_node(
        &mut self,
        local: usize,
        field_idx: usize,
        ty: Option<Ty<'tcx>>,
    ) -> usize {
        let new_id = self.generate_node_id();
        self.variables
            .insert(new_id, VariableNode::new_default(new_id, ty));
        let mut_node = self.get_var_node_mut(local).unwrap();
        mut_node.field.insert(field_idx, new_id);
        return new_id;
    }

    /// Find the variable ID in DG corresponding to a sequence of fields.
    pub fn find_var_id_with_fields_seq(&mut self, local: usize, fields: &Vec<usize>) -> usize {
        let mut cur = local;
        for field in fields.clone() {
            let mut cur_node = self.get_var_node(cur).unwrap();
            if let TyKind::Ref(_, _, _) = cur_node.ty.unwrap().kind() {
                let point_to = self.get_point_to_id(cur);
                cur_node = self.get_var_node(point_to).unwrap();
            }
            // If there exist a field node, then get it as cur node
            if cur_node.field.get(&field).is_some() {
                cur = *cur_node.field.get(&field).unwrap();
                continue;
            }
            // Otherwise, insert a new field node.
            match cur_node.ty.unwrap().kind() {
                TyKind::Adt(adt_def, substs) => {
                    if adt_def.is_struct() {
                        for (idx, field_def) in adt_def.all_fields().enumerate() {
                            if idx == field {
                                cur = self.get_field_node_id(
                                    cur,
                                    field,
                                    Some(field_def.ty(self.tcx, substs)),
                                );
                            }
                        }
                    }
                }
                // TODO: maybe unsafe here for setting ty as None!
                _ => {
                    rap_warn!("ty {:?}, field: {:?}", cur_node.ty.unwrap(), field);
                    rap_warn!(
                        "set field type as None! --- src: Dominated Graph / find_var_id_with_fields_seq"
                    );
                    cur = self.get_field_node_id(cur, field, None);
                }
            }
        }
        return cur;
    }

    /// Establishes a points-to relationship: lv -> rv.
    /// - Updates graph topology.
    /// - If `lv` is a Reference type, marks it as Aligned (Trusted Source).
    pub fn point(&mut self, lv: usize, rv: usize) {
        // rap_debug!("Graph Point: _{} -> _{}", lv, rv);

        // 1. Update Topology: rv.pointed_by.insert(lv)
        if let Some(rv_node) = self.get_var_node_mut(rv) {
            rv_node.pointed_by.insert(lv);
        } else {
            rap_debug!("Graph Point Error: Target node _{} not found", rv);
            return;
        }

        // 2. Update Topology & State: lv.points_to = rv
        // We need to retrieve 'old_points_to' to clean up later
        let old_points_to = if let Some(lv_node) = self.get_var_node_mut(lv) {
            let old = lv_node.points_to;
            lv_node.points_to = Some(rv);

            // --- Update AlignState based on Type ---
            // Logic: If lv is a Reference (&T), it implies the pointer is constructed
            // from a valid, aligned Rust reference. We mark it as Aligned(T, abi_align).
            if let Some(lv_ty) = lv_node.ty
                && is_ref(lv_ty)
            {
                let pointee_ty = get_pointee(lv_ty);
                lv_node.ots.align = AlignState::Aligned(pointee_ty);

                rap_debug!(
                    "Graph Point: Refined Ref _{} ({:?}) to Aligned via point()",
                    lv,
                    pointee_ty
                );
            }

            old
        } else {
            None
        };

        // 3. Clean up: Remove lv from old_points_to's pointed_by set
        if let Some(to) = old_points_to {
            // Only remove if we are changing pointing target (and not pointing to the same thing)
            if to != rv {
                if let Some(ori_to_node) = self.get_var_node_mut(to) {
                    ori_to_node.pointed_by.remove(&lv);
                }
            }
        }
    }

    /// Get the ID of a variable node.
    pub fn get_var_nod_id(&self, local_id: usize) -> usize {
        self.get_var_node(local_id).unwrap().id
    }

    /// Get a variable node by its local ID.
    pub fn get_map_idx_node(&self, local_id: usize) -> &VariableNode<'tcx> {
        self.variables.get(&local_id).unwrap()
    }

    /// Get a variable node by its local ID.
    pub fn get_var_node(&self, local_id: usize) -> Option<&VariableNode<'tcx>> {
        for (_idx, var_node) in &self.variables {
            if var_node.alias_set.contains(&local_id) {
                return Some(var_node);
            }
        }
        rap_warn!("def id:{:?}, local_id: {local_id}", self.def_id);
        display_hashmap(&self.variables, 1);
        None
    }

    /// Get a mutable reference to a variable node by its local ID.
    pub fn get_var_node_mut(&mut self, local_id: usize) -> Option<&mut VariableNode<'tcx>> {
        let va = self.variables.clone();
        for (_idx, var_node) in &mut self.variables {
            if var_node.alias_set.contains(&local_id) {
                return Some(var_node);
            }
        }
        rap_warn!("def id:{:?}, local_id: {local_id}", self.def_id);
        display_hashmap(&va, 1);
        None
    }

    /// Merge nodes for move assignments (`lv = move rv`).
    ///
    /// After the merge, `lv` becomes an alias of `rv` and incoming pointers that
    /// used to target `lv` are redirected to `rv`.
    pub fn merge(&mut self, lv: usize, rv: usize) {
        let lv_node = self.get_var_node_mut(lv).unwrap().clone();
        if lv_node.alias_set.contains(&rv) {
            return;
        }
        for lv_pointed_by in lv_node.pointed_by.clone() {
            self.point(lv_pointed_by, rv);
        }
        let lv_node = self.get_var_node_mut(lv).unwrap();
        lv_node.alias_set.remove(&lv);
        let lv_ty = lv_node.ty;
        let rv_node = self.get_var_node_mut(rv).unwrap();
        rv_node.alias_set.insert(lv);
        if rv_node.ty.is_none() {
            rv_node.ty = lv_ty;
        }
    }

    /// Copy node state for copy assignments (`lv = copy rv`).
    ///
    /// This preserves value/state facts from `rv` on `lv` and points `lv` at
    /// the same modeled object when `rv` is a pointer/reference.
    pub fn copy_node(&mut self, lv: usize, rv: usize) {
        let rv_node = self.get_var_node_mut(rv).unwrap().clone();
        let lv_node = self.get_var_node_mut(lv).unwrap();
        lv_node.ots = rv_node.ots;
        lv_node.facts = rv_node.facts;
        lv_node.is_dropped = rv_node.is_dropped;
        lv_node.offset_from = rv_node.offset_from;
        let lv_id = lv_node.id;
        if rv_node.points_to.is_some() {
            self.point(lv_id, rv_node.points_to.unwrap());
        }
    }

    /// Insert intermediate results into the graph.
    fn insert_node(
        &mut self,
        dv: usize,
        ty: Option<Ty<'tcx>>,
        parent_id: usize,
        child_id: Option<usize>,
        state: States<'tcx>,
    ) {
        self.variables.insert(
            dv,
            VariableNode::new(dv, child_id, HashSet::from([parent_id]), ty, state),
        );
    }

    /// Set the drop flag for a node.
    pub fn set_drop(&mut self, idx: usize) -> bool {
        if let Some(ori_node) = self.get_var_node_mut(idx) {
            if ori_node.is_dropped == true {
                // rap_warn!("Double free detected!"); // todo: update reports
                return false;
            }
            ori_node.is_dropped = true;
        }
        true
    }

    /// Update the constant value of a node.
    pub fn update_value(&mut self, arg: usize, value: usize) {
        let node = self.get_var_node_mut(arg).unwrap();
        node.const_value = value;
        node.ots.init = true;
    }

    /// Insert a partial-order predicate between two nodes.
    pub fn insert_partial_order(&mut self, p1: usize, p2: usize, op: &BinOp) {
        let contract = PropertyContract::new_partial_order(p1, p2, *op);
        let p1_node = self.get_var_node_mut(p1).unwrap();
        p1_node.facts.add_contract(contract.clone());
        let p2_node = self.get_var_node_mut(p2).unwrap();
        p2_node.facts.add_contract(contract);
    }
}

/// Debug implementation for DominatedGraph.
impl<'tcx> DominatedGraph<'tcx> {
    /// Generate a DOT graph representation of the dominated graph.
    pub fn to_dot_graph(&self) -> String {
        let mut dot = String::new();
        writeln!(dot, "digraph DominatedGraph {{").unwrap();

        writeln!(
            dot,
            "    graph [compound=true, splines=polyline, nodesep=0.5, ranksep=0.5];"
        )
        .unwrap();
        writeln!(dot, "    node [shape=plain, fontname=\"Courier\"];").unwrap();
        writeln!(dot, "    edge [fontname=\"Courier\"];").unwrap();

        let mut isolated_nodes = Vec::new();
        let mut connected_nodes = Vec::new();

        let mut keys: Vec<&usize> = self.variables.keys().collect();
        keys.sort();

        for id in keys {
            if let Some(node) = self.variables.get(id) {
                let is_isolated =
                    node.points_to.is_none() && node.field.is_empty() && node.pointed_by.is_empty();

                if is_isolated {
                    isolated_nodes.push(*id);
                } else {
                    connected_nodes.push(*id);
                }
            }
        }

        if !isolated_nodes.is_empty() {
            writeln!(dot, "    subgraph cluster_isolated {{").unwrap();
            writeln!(dot, "        label = \"Isolated Variables (Grid Layout)\";").unwrap();
            writeln!(dot, "        style = dashed;").unwrap();
            writeln!(dot, "        color = grey;").unwrap();

            let total_iso = isolated_nodes.len();
            let cols = (total_iso as f64).sqrt().ceil() as usize;

            for id in &isolated_nodes {
                if let Some(node) = self.variables.get(id) {
                    let node_label = self.generate_node_label(node);
                    writeln!(dot, "        {} [label=<{}>];", id, node_label).unwrap();
                }
            }

            for chunk in isolated_nodes.chunks(cols) {
                write!(dot, "        {{ rank=same;").unwrap();
                for id in chunk {
                    write!(dot, " {};", id).unwrap();
                }
                writeln!(dot, " }}").unwrap();
            }

            for i in 0..isolated_nodes.chunks(cols).len() {
                let current_row_idx = i * cols;
                let next_row_idx = (i + 1) * cols;

                if next_row_idx < total_iso {
                    let curr_id = isolated_nodes[current_row_idx];
                    let next_id = isolated_nodes[next_row_idx];
                    writeln!(
                        dot,
                        "        {} -> {} [style=invis, weight=100];",
                        curr_id, next_id
                    )
                    .unwrap();
                }
            }

            writeln!(dot, "    }}").unwrap();
        }

        if !connected_nodes.is_empty() {
            writeln!(dot, "    subgraph cluster_connected {{").unwrap();
            writeln!(dot, "        label = \"Reference Graph\";").unwrap();
            writeln!(dot, "        color = black;").unwrap();

            for id in &connected_nodes {
                if let Some(node) = self.variables.get(id) {
                    let node_label = self.generate_node_label(node);
                    writeln!(dot, "        {} [label=<{}>];", id, node_label).unwrap();
                }
            }
            writeln!(dot, "    }}").unwrap();
        }

        // draw edges
        writeln!(dot, "").unwrap();
        for id in &connected_nodes {
            if let Some(node) = self.variables.get(id) {
                if let Some(target) = node.points_to {
                    writeln!(
                        dot,
                        "    {} -> {} [label=\"ptr\", color=\"blue\", fontcolor=\"blue\"];",
                        id, target
                    )
                    .unwrap();
                }

                let mut field_indices: Vec<&usize> = node.field.keys().collect();
                field_indices.sort();
                for field_idx in field_indices {
                    let target_id = node.field.get(field_idx).unwrap();
                    writeln!(
                        dot,
                        "    {} -> {} [label=\".{}\", style=\"dashed\"];",
                        id, target_id, field_idx
                    )
                    .unwrap();
                }
            }
        }

        writeln!(dot, "}}").unwrap();
        dot
    }

    /// Generate a label for a node in the DOT graph.
    fn generate_node_label(&self, node: &VariableNode<'tcx>) -> String {
        let ty_str = match node.ty {
            Some(t) => format!("{:?}", t),
            None => "None".to_string(),
        };
        let safe_ty = html_escape(&ty_str);

        format!(
            r#"<table border="0" cellborder="1" cellspacing="0" cellpadding="4">
                <tr><td colspan="2"><b>ID: {}</b></td></tr>
                <tr><td align="left">Type:</td><td align="left">{}</td></tr>
                <tr><td align="left">Const:</td><td align="left">{}</td></tr>
               </table>"#,
            node.id, safe_ty, node.const_value,
        )
    }

    /// Debug helper: Visualize the graph structure and states in a table format
    pub fn display_dominated_graph(&self) {
        const TABLE_WIDTH: usize = 145; // Keep enough room for the Offset column.
        println!(
            "\n{:=^width$}",
            " Dominated Graph Report ",
            width = TABLE_WIDTH
        );

        let mut sorted_ids: Vec<&usize> = self.variables.keys().collect();
        sorted_ids.sort();

        if sorted_ids.is_empty() {
            println!("  [Empty Graph]");
            println!("{:=^width$}\n", "", width = TABLE_WIDTH);
            return;
        }

        // Define table headers and separator
        // ID: 6, Type: 25, Pt-To: 8, Fields: 15, Offset: 25, States: 40
        let sep = format!(
            "+{:-^6}+{:-^25}+{:-^8}+{:-^15}+{:-^25}+{:-^40}+",
            "", "", "", "", "", ""
        );
        println!("{}", sep);
        println!(
            "| {:^6} | {:^25} | {:^8} | {:^15} | {:^25} | {:^40} |",
            "ID", "Type", "Pt-To", "Fields", "Offset", "States"
        );
        println!("{}", sep);

        for id in sorted_ids {
            let node = &self.variables[id];

            // 1. Format Type: Convert Ty to string and handle None
            let ty_str = node
                .ty
                .map(|t| format!("{:?}", t))
                .unwrap_or_else(|| "None".to_string());

            // 2. Format Points-To: Show target node ID if exists
            let pt_str = node
                .points_to
                .map(|p| format!("_{}", p))
                .unwrap_or_else(|| "-".to_string());

            // 3. Format Fields: Show "field_idx -> node_id" mapping
            let fields_str = if node.field.is_empty() {
                "-".to_string()
            } else {
                let mut fs: Vec<String> = node
                    .field
                    .iter()
                    .map(|(k, v)| format!(".{}->_{}", k, v))
                    .collect();
                fs.sort(); // Keep deterministic order
                fs.join(", ")
            };

            // 4. Format Offset: Show offset source info nicely
            let offset_str = if let Some(def) = &node.offset_from {
                match def {
                    // PtrOffset: "_base +/- index"
                    SymbolicDef::PtrOffset(op, base, idx, _) => {
                        let op_str = match op {
                            BinOp::Add => "+",
                            BinOp::Sub => "-",
                            _ => "?",
                        };
                        let idx_str = match idx {
                            AnaOperand::Local(l) => format!("_{}", l),
                            AnaOperand::Const(c) => format!("{}", c),
                        };
                        format!("_{} {} {}", base, op_str, idx_str)
                    }
                    SymbolicDef::Binary(BinOp::Offset, base, idx) => {
                        let idx_str = match idx {
                            AnaOperand::Local(l) => format!("_{}", l),
                            AnaOperand::Const(c) => format!("{}", c),
                        };
                        format!("_{} + {}", base, idx_str)
                    }
                    _ => format!("{:?}", def),
                }
            } else {
                "-".to_string()
            };

            // 5. Format States: concise flags for Init, NonNull, Align, etc.
            let mut states_vec = Vec::new();
            // 5.1 Extract alignment info
            match &node.ots.align {
                AlignState::Aligned(ty) => {
                    let node_ty = node.ty.unwrap();
                    if is_ptr(node_ty) || is_ref(node_ty) {
                        states_vec.push(format!("Align({:?})", ty));
                    }
                }
                AlignState::Unaligned(ty) => states_vec.push(format!("Unalign({:?})", ty)),
                AlignState::Unknown => states_vec.push("Unknown".to_string()),
            }
            let states_str = if states_vec.is_empty() {
                "-".to_string()
            } else {
                states_vec.join(", ")
            };

            // Print the row with truncation to keep table alignment
            println!(
                "| {:<6} | {:<25} | {:<8} | {:<15} | {:<25} | {:<40} |",
                id,
                self.safe_truncate_str(&ty_str, 25),
                pt_str,
                self.safe_truncate_str(&fields_str, 15),
                self.safe_truncate_str(&offset_str, 25),
                self.safe_truncate_str(&states_str, 40)
            );
        }

        println!("{}", sep);
        println!("{:=^width$}\n", " End Graph ", width = TABLE_WIDTH);
    }

    // Helper: Truncate strings to maintain table layout
    fn safe_truncate_str(&self, s: &str, max_width: usize) -> String {
        if s.chars().count() <= max_width {
            return s.to_string();
        }
        let truncated: String = s.chars().take(max_width - 2).collect();
        format!("{}..", truncated)
    }
}

/// Escape HTML characters in a string.
fn html_escape(input: &str) -> String {
    input
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace("\"", "&quot;")
}

impl<'tcx> DominatedGraph<'tcx> {
    /// Public method called by BodyVisitor to update graph topology
    /// when a PtrOffset definition is applied.
    pub fn update_from_offset_def(
        &mut self,
        // Parameters for the offset definition
        target_local: usize,
        // Base local variable being offset
        base_local: usize,
        // The symbolic definition of the offset
        offset_def: SymbolicDef<'tcx>,
    ) {
        // 1. Update Pointing: target points to whatever base points to
        // Because offset pointer usually stays within the same object allocation
        let base_point_to = self.get_point_to_id(base_local);
        self.point(target_local, base_point_to);

        // 2. Record the offset relationship on the node
        // This is crucial for backtracking the base pointer during checks
        if let Some(node) = self.get_var_node_mut(target_local) {
            node.offset_from = Some(offset_def);

            rap_debug!(
                "Graph Update: _{} is offset of _{} (via update_from_offset_def)",
                target_local,
                base_local
            );
        }
    }
}
