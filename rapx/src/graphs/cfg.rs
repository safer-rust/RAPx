use crate::graphs::scc::{Scc, SccExit, SccInfo};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::{mir::Terminator, ty::TyCtxt};
use rustc_span::def_id::DefId;

/// Reusable CFG block structure shared by analyses built over MIR.
///
/// Each `CfgBlock` corresponds to a MIR basic block and stores:
/// - its block index,
/// - whether it is a cleanup block,
/// - its outgoing CFG edges,
/// - the terminator instruction,
/// - locals assigned in this block,
/// - and SCC metadata for loop/cycle-aware traversal.
#[derive(Debug, Clone)]
pub struct CfgBlock<'tcx> {
    /// Index of this block in the CFG block list.
    pub index: usize,
    /// Whether this block belongs to MIR cleanup/unwind control flow.
    pub is_cleanup: bool,
    /// Outgoing successor block indices.
    pub next: FxHashSet<usize>,
    /// MIR terminator associated with this block.
    pub terminator: Option<Terminator<'tcx>>,
    /// Locals assigned in this block.
    ///
    /// This is used during SCC/path processing to invalidate stale
    /// path constraints after assignments.
    pub assigned_locals: FxHashSet<usize>,
    /// SCC information for this block.
    ///
    /// For non-root blocks inside an SCC, `enter` points to the SCC root.
    /// For SCC roots, this field also stores member nodes, exits, and back edges.
    pub scc: SccInfo,
}

impl<'tcx> CfgBlock<'tcx> {
    /// Create a new CFG block with default analysis metadata.
    pub fn new(index: usize, is_cleanup: bool) -> Self {
        Self {
            index,
            is_cleanup,
            next: FxHashSet::default(),
            terminator: None,
            assigned_locals: FxHashSet::default(),
            scc: SccInfo::new(index),
        }
    }

    /// Add a successor edge from this block to `index`.
    pub fn add_next(&mut self, index: usize) {
        self.next.insert(index);
    }
}

/// Control-flow graph metadata independent from any particular analysis facts.
///
/// This structure owns the MIR-level CFG plus path-sensitive metadata used
/// during traversal and SCC-aware analysis.
#[derive(Clone)]
pub struct ControlFlowGraph<'tcx> {
    /// Definition being analyzed.
    pub def_id: DefId,
    /// Type context from the Rust compiler.
    pub tcx: TyCtxt<'tcx>,
    /// All CFG blocks for the current body.
    pub blocks: Vec<CfgBlock<'tcx>>,
    /// Path-sensitive constants tracked during traversal.
    ///
    /// The key/value meaning depends on the caller's analysis convention.
    pub constants: FxHashMap<usize, usize>,
    /// Path-sensitive discriminant source mapping tracked during traversal.
    ///
    /// This is typically used to preserve branch/switch-related facts.
    pub discriminants: FxHashMap<usize, usize>,
    /// Number of times the graph or a traversal routine has been visited.
    pub visit_times: usize,
}

impl<'tcx> ControlFlowGraph<'tcx> {
    /// Construct a control-flow graph wrapper from prebuilt blocks.
    pub fn new(def_id: DefId, tcx: TyCtxt<'tcx>, blocks: Vec<CfgBlock<'tcx>>) -> Self {
        Self {
            def_id,
            tcx,
            blocks,
            constants: FxHashMap::default(),
            discriminants: FxHashMap::default(),
            visit_times: 0,
        }
    }

    /// Get an immutable reference to a block by index.
    pub fn block(&self, index: usize) -> &CfgBlock<'tcx> {
        &self.blocks[index]
    }

    /// Get a mutable reference to a block by index.
    pub fn block_mut(&mut self, index: usize) -> &mut CfgBlock<'tcx> {
        &mut self.blocks[index]
    }

    /// Populate and return a hierarchical SCC tree rooted at `scc.enter`.
    pub fn sort_scc_tree(&mut self, scc: &SccInfo) -> SccInfo {
        self.populate_child_sccs(scc.enter);
        self.block(scc.enter).scc.clone()
    }

    /// Recursively discover nested child SCCs for the SCC rooted at `enter`.
    ///
    /// A child SCC is identified when a node inside the current SCC belongs to
    /// another non-trivial SCC with a different `enter`.
    fn populate_child_sccs(&mut self, enter: usize) {
        let nodes: Vec<usize> = self.block(enter).scc.nodes.iter().cloned().collect();
        let mut child_enters = Vec::new();
        let mut seen = FxHashSet::default();

        for node in nodes {
            if let Some(block) = self.blocks.get(node) {
                let node_enter = block.scc.enter;
                let non_trivial = !block.scc.nodes.is_empty();

                // Record distinct non-trivial child SCC roots only once.
                if node_enter != enter && non_trivial && seen.insert(node_enter) {
                    child_enters.push(node_enter);
                }
            }
        }

        self.block_mut(enter).scc.child_sccs = child_enters;

        // Recursively populate SCC children to build the SCC tree.
        for &child_enter in &self.block(enter).scc.child_sccs.clone() {
            self.populate_child_sccs(child_enter);
        }
    }

    /// Get the current visit counter.
    pub fn visit_times(&self) -> usize {
        self.visit_times
    }

    /// Increment and return the visit counter.
    pub fn increment_visit_times(&mut self) -> usize {
        self.visit_times += 1;
        self.visit_times
    }
}

/// Record exits from the SCC root to blocks outside the SCC.
fn record_root_exits<'tcx>(
    graph: &mut ControlFlowGraph<'tcx>,
    root: usize,
    scc_components: &[usize],
) {
    let nexts = graph.block(root).next.clone();
    for next in nexts {
        if !scc_components.contains(&next) {
            graph.block_mut(root).scc.exits.insert(SccExit::new(root, next));
        }
    }
}

/// Record membership, exit edges, and back edges for all non-root SCC members.
fn record_member_nodes<'tcx>(
    graph: &mut ControlFlowGraph<'tcx>,
    root: usize,
    scc_components: &[usize],
) {
    for &node in &scc_components[1..] {
        // Record membership under the root SCC.
        graph.block_mut(root).scc.nodes.insert(node);
        // Make each member point to the SCC root.
        graph.block_mut(node).scc.enter = root;

        let nexts = graph.block(node).next.clone();
        for next in nexts {
            // Any edge leaving the SCC is an SCC exit.
            if !scc_components.contains(&next) {
                graph.block_mut(root).scc.exits.insert(SccExit::new(node, next));
            }
            // Any edge back to the root is tracked as a back edge source.
            if next == root {
                graph.block_mut(root).scc.backnodes.insert(node);
            }
        }
    }
}

/// Re-run SCC discovery with a temporarily reduced graph to discover nested SCCs.
///
/// Isolates the SCC rooted at `root` by:
/// 1. Redirecting block 0 to point only to `root`.
/// 2. Removing back edges from backnodes to `root`.
/// 3. Cutting all outgoing edges from SCC exit targets.
///
/// After re-running SCC discovery, all edges are restored.
fn rerun_scc_in_isolation<'tcx>(
    graph: &mut ControlFlowGraph<'tcx>,
    root: usize,
    scc_components: &[usize],
) {
    let scc_exits = graph.block(root).scc.exits.clone();
    let backnodes = graph.block(root).scc.backnodes.clone();
    let mut backups: Vec<(usize, FxHashSet<usize>)> = Vec::new();

    // Temporarily redirect entry block 0 to this SCC root only.
    // This helps isolate SCC structure for the recursive `find_scc()` call.
    let block0 = graph.block_mut(0);
    backups.push((0, block0.next.clone()));
    block0.next.clear();
    block0.next.insert(root);

    // Temporarily remove back edges from SCC backnodes to the root.
    for &node in &scc_components[1..] {
        if backnodes.contains(&node) {
            let block = graph.block_mut(node);
            backups.push((node, block.next.clone()));
            block.next.remove(&root);
        }
    }

    // Temporarily cut all outgoing edges from SCC exit targets.
    for exit in &scc_exits {
        let block_to = graph.block_mut(exit.to);
        backups.push((exit.to, block_to.next.clone()));
        block_to.next.clear();
    }

    // Re-run SCC discovery on the transformed graph.
    graph.find_scc();

    // Restore all modified edges.
    for (idx, saved_next) in backups {
        graph.block_mut(idx).next = saved_next;
    }
}

/// Handle a newly discovered SCC: mark the root, collect membership and edge metadata,
/// then re-run SCC discovery on an isolated subgraph to populate nested SCC structure.
fn scc_handler<'tcx>(
    graph: &mut ControlFlowGraph<'tcx>,
    root: usize,
    scc_components: &[usize],
) {
    rap_debug!(
        "Scc found: root = {}, components = {:?}",
        root,
        scc_components
    );

    // The SCC root always points to itself.
    graph.block_mut(root).scc.enter = root;

    // A single-node SCC is trivial; nothing else needs to be recorded.
    if scc_components.len() <= 1 {
        return;
    }

    record_root_exits(graph, root, scc_components);
    record_member_nodes(graph, root, scc_components);

    rap_debug!("Scc Info: {:?}", graph.block(root).scc);
    rerun_scc_in_isolation(graph, root, scc_components);
}

impl<'tcx> Scc for ControlFlowGraph<'tcx> {
    /// Callback invoked when an SCC is discovered.
    fn on_scc_found(&mut self, root: usize, scc_components: &[usize]) {
        scc_handler(self, root, scc_components);
    }

    /// Return the outgoing successors of a node.
    fn get_next(&mut self, root: usize) -> FxHashSet<usize> {
        self.block(root).next.clone()
    }

    /// Return the total number of CFG blocks.
    fn get_size(&mut self) -> usize {
        self.blocks.len()
    }
}
