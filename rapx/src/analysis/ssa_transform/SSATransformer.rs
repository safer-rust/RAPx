#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]

use rustc_data_structures::graph::dominators::Dominators;
use rustc_data_structures::graph::{Predecessors, dominators};
use rustc_driver::args;
use rustc_hir::def_id::DefId;
use rustc_hir::def_id::{CRATE_DEF_INDEX, CrateNum, DefIndex, LOCAL_CRATE, LocalDefId};
use rustc_middle::mir::*;
use rustc_middle::{
    mir::{Body, Local, Location, visit::Visitor},
    ty::TyCtxt,
};
use rustc_span::symbol::Symbol;
use std::collections::{HashMap, HashSet};
pub struct PhiPlaceholder;
pub struct SSATransformer<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub body: Body<'tcx>,
    pub cfg: HashMap<BasicBlock, Vec<BasicBlock>>,
    pub dominators: Dominators<BasicBlock>,
    pub dom_tree: HashMap<BasicBlock, Vec<BasicBlock>>,
    pub df: HashMap<BasicBlock, HashSet<BasicBlock>>,
    pub local_assign_blocks: HashMap<Local, HashSet<BasicBlock>>,
    pub reaching_def: HashMap<Local, Option<Local>>,
    pub local_index: usize,
    pub local_defination_block: HashMap<Local, BasicBlock>,
    pub skipped: HashSet<usize>,
    pub phi_index: HashMap<Location, usize>,
    pub phi_def_id: DefId,
    pub essa_def_id: DefId,
    pub ref_local_map: HashMap<Local, Local>,
    pub places_map: HashMap<Place<'tcx>, HashSet<Place<'tcx>>>,
    pub ssa_locals_map: HashMap<Place<'tcx>, HashSet<Place<'tcx>>>,
}

impl<'tcx> SSATransformer<'tcx> {
    fn find_phi_placeholder(tcx: TyCtxt<'_>, crate_name: &str) -> Option<DefId> {
        let sym_crate = Symbol::intern(crate_name);
        let krate = tcx
            .crates(())
            .iter()
            .find(|&&c| tcx.crate_name(c) == sym_crate)?;
        let root_def_id = DefId {
            krate: *krate,
            index: CRATE_DEF_INDEX,
        };
        // print!("Phid\n");

        for item in tcx.module_children(root_def_id) {
            // println!("Module child: {:?}", item.ident.name.as_str());

            if item.ident.name.as_str() == "PhiPlaceholder" {
                if let Some(def_id) = item.res.opt_def_id() {
                    return Some(def_id);
                }
            }
        }
        // print!("Phid\n");
        return Some(root_def_id);
    }
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        ssa_def_id: DefId,
        essa_def_id: DefId,
        arg_count: usize,
    ) -> Self {
        let cfg: HashMap<BasicBlock, Vec<BasicBlock>> = Self::extract_cfg_from_predecessors(&body);

        let dominators: Dominators<BasicBlock> = body.basic_blocks.dominators().clone();

        let dom_tree: HashMap<BasicBlock, Vec<BasicBlock>> = Self::construct_dominance_tree(&body);

        let df: HashMap<BasicBlock, HashSet<BasicBlock>> =
            Self::compute_dominance_frontier(&body, &dom_tree);

        let local_assign_blocks: HashMap<Local, HashSet<BasicBlock>> =
            Self::map_locals_to_assign_blocks(&body);
        let local_defination_block: HashMap<Local, BasicBlock> =
            Self::map_locals_to_definition_block(&body);
        let len = body.local_decls.len() as usize;
        let mut skipped = HashSet::new();
        if len > 0 {
            skipped.extend(arg_count + 1..len + 1);
            // skipped.insert(0); // Skip the return place
        }

        SSATransformer {
            tcx,
            body: body.clone(),
            cfg,
            dominators,
            dom_tree,
            df,
            local_assign_blocks,
            reaching_def: HashMap::default(),
            local_index: len,
            local_defination_block: local_defination_block,
            skipped: skipped,
            phi_index: HashMap::default(),
            phi_def_id: ssa_def_id,
            essa_def_id: essa_def_id,
            ref_local_map: HashMap::default(),
            places_map: HashMap::default(),
            ssa_locals_map: HashMap::default(),
        }
    }

    pub fn return_body_ref(&self) -> &Body<'tcx> {
        &self.body
    }

    fn map_locals_to_definition_block(body: &Body) -> HashMap<Local, BasicBlock> {
        let mut local_to_block_map: HashMap<Local, BasicBlock> = HashMap::new();

        for (bb, block_data) in body.basic_blocks.iter_enumerated() {
            for statement in &block_data.statements {
                match &statement.kind {
                    StatementKind::Assign(box (place, _)) => {
                        if let Some(local) = place.as_local() {
                            if local.as_u32() == 0 {
                                continue; // Skip the return place
                            }
                            local_to_block_map.entry(local).or_insert(bb);
                        }
                    }
                    _ => {}
                }
            }
            if let Some(terminator) = &block_data.terminator {
                match &terminator.kind {
                    TerminatorKind::Call { destination, .. } => {
                        if let Some(local) = destination.as_local() {
                            if local.as_u32() == 0 {
                                continue; // Skip the return place
                            }
                            local_to_block_map.entry(local).or_insert(bb);
                        }
                    }
                    _ => {}
                }
            }
        }

        local_to_block_map
    }
    pub fn depth_first_search_preorder(
        dom_tree: &HashMap<BasicBlock, Vec<BasicBlock>>,
        root: BasicBlock,
    ) -> Vec<BasicBlock> {
        let mut visited: HashSet<BasicBlock> = HashSet::new();
        let mut preorder = Vec::new();

        fn dfs(
            node: BasicBlock,
            dom_tree: &HashMap<BasicBlock, Vec<BasicBlock>>,
            visited: &mut HashSet<BasicBlock>,
            preorder: &mut Vec<BasicBlock>,
        ) {
            if visited.insert(node) {
                preorder.push(node);

                if let Some(children) = dom_tree.get(&node) {
                    for &child in children {
                        dfs(child, dom_tree, visited, preorder);
                    }
                }
            }
        }

        dfs(root, dom_tree, &mut visited, &mut preorder);
        preorder
    }
    pub fn depth_first_search_postorder(
        dom_tree: &HashMap<BasicBlock, Vec<BasicBlock>>,
        root: &BasicBlock,
    ) -> Vec<BasicBlock> {
        let mut visited: HashSet<BasicBlock> = HashSet::new();
        let mut postorder = Vec::new();

        fn dfs(
            node: BasicBlock,
            dom_tree: &HashMap<BasicBlock, Vec<BasicBlock>>,
            visited: &mut HashSet<BasicBlock>,
            postorder: &mut Vec<BasicBlock>,
        ) {
            if visited.insert(node) {
                if let Some(children) = dom_tree.get(&node) {
                    for &child in children {
                        dfs(child, dom_tree, visited, postorder);
                    }
                }
                postorder.push(node);
            }
        }

        dfs(*root, dom_tree, &mut visited, &mut postorder);
        postorder
    }

    fn map_locals_to_assign_blocks(body: &Body) -> HashMap<Local, HashSet<BasicBlock>> {
        let mut local_to_blocks: HashMap<Local, HashSet<BasicBlock>> = HashMap::new();

        for (bb, data) in body.basic_blocks.iter_enumerated() {
            for stmt in &data.statements {
                if let StatementKind::Assign(box (place, _)) = &stmt.kind {
                    let local = place.local;
                    if local.as_u32() == 0 {
                        continue; // Skip the return place
                    }
                    local_to_blocks
                        .entry(local)
                        .or_insert_with(HashSet::new)
                        .insert(bb);
                }
            }
        }
        for arg in body.args_iter() {
            local_to_blocks
                .entry(arg)
                .or_insert_with(HashSet::new)
                .insert(BasicBlock::from_u32(0)); // Assuming arg block is 0
        }
        local_to_blocks
    }
    fn construct_dominance_tree(body: &Body<'_>) -> HashMap<BasicBlock, Vec<BasicBlock>> {
        let mut dom_tree: HashMap<BasicBlock, Vec<BasicBlock>> = HashMap::new();
        let dominators = body.basic_blocks.dominators();
        for (block, _) in body.basic_blocks.iter_enumerated() {
            if let Some(idom) = dominators.immediate_dominator(block) {
                dom_tree.entry(idom).or_default().push(block);
            }
        }

        dom_tree
    }
    fn compute_dominance_frontier(
        body: &Body<'_>,
        dom_tree: &HashMap<BasicBlock, Vec<BasicBlock>>,
    ) -> HashMap<BasicBlock, HashSet<BasicBlock>> {
        let mut dominance_frontier: HashMap<BasicBlock, HashSet<BasicBlock>> = HashMap::new();
        let dominators = body.basic_blocks.dominators();
        let predecessors = body.basic_blocks.predecessors();
        for (block, _) in body.basic_blocks.iter_enumerated() {
            dominance_frontier.entry(block).or_default();
        }

        for (block, _) in body.basic_blocks.iter_enumerated() {
            if predecessors[block].len() > 1 {
                let preds = body.basic_blocks.predecessors()[block].clone();

                for &pred in &preds {
                    let mut runner = pred;
                    while runner != dominators.immediate_dominator(block).unwrap() {
                        dominance_frontier.entry(runner).or_default().insert(block);
                        runner = dominators.immediate_dominator(runner).unwrap();
                    }
                }
            }
        }

        dominance_frontier
    }
    fn extract_cfg_from_predecessors(body: &Body<'_>) -> HashMap<BasicBlock, Vec<BasicBlock>> {
        let mut cfg: HashMap<BasicBlock, Vec<BasicBlock>> = HashMap::new();

        for (block, _) in body.basic_blocks.iter_enumerated() {
            for &predecessor in body.basic_blocks.predecessors()[block].iter() {
                cfg.entry(predecessor).or_default().push(block);
            }
        }

        cfg
    }
    fn print_dominance_tree(
        dom_tree: &HashMap<BasicBlock, Vec<BasicBlock>>,
        current: BasicBlock,
        depth: usize,
    ) {
        if let Some(children) = dom_tree.get(&current) {
            for &child in children {
                Self::print_dominance_tree(dom_tree, child, depth + 1);
            }
        }
    }

    pub fn is_phi_statement(&self, statement: &Statement<'tcx>) -> bool {
        if let StatementKind::Assign(box (_, rvalue)) = &statement.kind {
            if let Rvalue::Aggregate(box aggregate_kind, _) = rvalue {
                if let AggregateKind::Adt(def_id, ..) = aggregate_kind {
                    return *def_id == self.phi_def_id;
                }
            }
        }
        false
    }

    pub fn is_essa_statement(&self, statement: &Statement<'tcx>) -> bool {
        if let StatementKind::Assign(box (_, rvalue)) = &statement.kind {
            if let Rvalue::Aggregate(box aggregate_kind, _) = rvalue {
                if let AggregateKind::Adt(def_id, ..) = aggregate_kind {
                    return *def_id == self.essa_def_id;
                }
            }
        }
        false
    }
    pub fn get_essa_source_block(&self, statement: &Statement<'tcx>) -> Option<BasicBlock> {
        if !self.is_essa_statement(statement) {
            return None;
        }

        if let StatementKind::Assign(box (_, Rvalue::Aggregate(_, operands))) = &statement.kind {
            if let Some(last_op) = operands.into_iter().last() {
                if let Operand::Constant(box ConstOperand { const_: c, .. }) = last_op {
                    if let Some(val) = self.try_const_to_usize(c) {
                        return Some(BasicBlock::from_usize(val as usize));
                    }
                }
            }
        }
        None
    }

    fn try_const_to_usize(&self, c: &Const<'tcx>) -> Option<u64> {
        if let Some(scalar_int) = c.try_to_scalar_int() {
            let size = scalar_int.size();
            if let Ok(bits) = scalar_int.try_to_bits(size) {
                return Some(bits as u64);
            }
        }
        None
    }
}
