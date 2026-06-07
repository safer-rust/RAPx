//! Shared strongly-connected-component utilities.
//!
//! This module provides the small Tarjan SCC abstraction used by RAP analyses
//! and by the verification path extractor. The trait is intentionally graph
//! agnostic: clients provide successor queries and receive each discovered SCC
//! through `on_scc_found`.

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::BasicBlock;
use std::cmp;

/// An outgoing edge from an SCC body to a block outside the SCC.
#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct SccExit {
    /// Legacy alias for `from` used by existing analyses.
    pub exit: usize,
    /// Source node inside the SCC body.
    pub from: usize,
    /// Destination node outside the SCC body.
    pub to: usize,
}

impl SccExit {
    /// Create an SCC exit edge from `from` to `to`.
    pub fn new(from: usize, to: usize) -> Self {
        SccExit {
            exit: from,
            from,
            to,
        }
    }
}

/// Per-header SCC metadata used by loop-aware analyses.
#[derive(Debug, Clone)]
pub struct SccInfo {
    /// Legacy SCC root field used across existing analyses.
    pub enter: usize,
    /// Legacy SCC member set excluding `enter`.
    pub nodes: FxHashSet<usize>,
    /// Legacy SCC back-edge source set.
    pub backnodes: FxHashSet<usize>,
    /// Representative entry block of the SCC.
    pub representative: usize,
    /// All blocks in the SCC, including `representative`.
    pub blocks: Vec<usize>,
    /// Edges leaving the SCC.
    pub exits: FxHashSet<SccExit>,
    /// Edges inside the SCC region that go back to an earlier block or the representative.
    pub backedges: Vec<(usize, usize)>,
    /// Representative nodes of nested child SCCs.
    pub child_sccs: Vec<usize>,
}

impl SccInfo {
    /// Create empty SCC metadata for `representative`.
    pub fn new(representative: usize) -> Self {
        SccInfo {
            enter: representative,
            nodes: FxHashSet::default(),
            backnodes: FxHashSet::default(),
            representative,
            blocks: vec![representative],
            exits: FxHashSet::default(),
            backedges: Vec::new(),
            child_sccs: Vec::new(),
        }
    }

    /// Returns `true` when this SCC contains only its representative and has no self-loop.
    pub fn is_trivial(&self) -> bool {
        self.blocks.len() <= 1 && self.backedges.is_empty()
    }

    /// Compatibility accessor for older callers.
    pub fn enter(&self) -> usize {
        self.enter
    }
}

/// A cyclic SCC region specialized for MIR basic blocks.
#[derive(Clone, Debug)]
pub struct SccRegion {
    /// Stable representative block used as the key for this SCC region.
    pub representative: BasicBlock,
    /// Blocks that belong to the SCC region.
    pub blocks: Vec<BasicBlock>,
    /// Edges that leave the SCC region.
    pub exits: Vec<SccRegionExit>,
    /// Edges inside the SCC region that go back to an earlier block or the representative.
    pub backedges: Vec<(BasicBlock, BasicBlock)>,
}

/// An edge that leaves a detected MIR SCC region.
#[derive(Clone, Debug)]
pub struct SccRegionExit {
    /// Source block inside the SCC region.
    pub from: BasicBlock,
    /// Destination block outside the SCC region.
    pub to: BasicBlock,
}

/// Detect cyclic SCC regions in a MIR CFG successor graph.
pub fn find_scc_regions(
    successors: &[Vec<BasicBlock>],
) -> (Vec<SccRegion>, FxHashMap<BasicBlock, BasicBlock>) {
    let successors_usize: Vec<Vec<usize>> = successors
        .iter()
        .map(|nexts| nexts.iter().map(|bb| bb.as_usize()).collect())
        .collect();
    let components = collect_scc_components(&successors_usize);

    let mut scc_regions = Vec::new();
    let mut block_to_scc = FxHashMap::default();
    for mut component in components {
        component.sort_unstable();
        let has_self_edge = component.len() == 1
            && successors[component[0]]
                .iter()
                .any(|succ| succ.as_usize() == component[0]);
        if component.len() <= 1 && !has_self_edge {
            continue;
        }

        let representative = BasicBlock::from_usize(component[0]);
        let block_set: FxHashSet<usize> = component.iter().copied().collect();
        let mut exits = Vec::new();
        let mut backedges = Vec::new();

        for &block_idx in &component {
            let block = BasicBlock::from_usize(block_idx);
            for &succ in &successors[block_idx] {
                let succ_idx = succ.as_usize();
                if block_set.contains(&succ_idx) {
                    if succ_idx <= block_idx || succ == representative {
                        backedges.push((block, succ));
                    }
                } else {
                    exits.push(SccRegionExit {
                        from: block,
                        to: succ,
                    });
                }
            }
        }

        for &block_idx in &component {
            block_to_scc.insert(BasicBlock::from_usize(block_idx), representative);
        }

        scc_regions.push(SccRegion {
            representative,
            blocks: component.into_iter().map(BasicBlock::from_usize).collect(),
            exits,
            backedges,
        });
    }

    (scc_regions, block_to_scc)
}

/// Collect all SCC components from a successor graph.
pub fn collect_scc_components(successors: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut collector = SccComponentCollector::new(successors.to_vec());
    collector.find_scc();
    collector.components
}

struct SccComponentCollector {
    successors: Vec<Vec<usize>>,
    components: Vec<Vec<usize>>,
}

impl SccComponentCollector {
    fn new(successors: Vec<Vec<usize>>) -> Self {
        Self {
            successors,
            components: Vec::new(),
        }
    }
}

/// Tarjan SCC callback trait.
pub trait Scc {
    /// Run SCC discovery from CFG entry block 0.
    fn find_scc(&mut self) {
        if self.get_size() == 0 {
            return;
        }
        self.find_scc_from(0);
    }

    /// Run SCC discovery from a specific start node.
    fn find_scc_from(&mut self, start: usize) {
        if start >= self.get_size() {
            return;
        }
        let mut stack = Vec::new();
        let mut instack = FxHashSet::<usize>::default();
        let mut dfn = vec![0; self.get_size()];
        let mut low = vec![0; self.get_size()];
        let mut time = 1;
        self.tarjan(
            start,
            &mut stack,
            &mut instack,
            &mut dfn,
            &mut low,
            &mut time,
        );
    }

    /// Callback invoked for each discovered SCC.
    fn on_scc_found(&mut self, root: usize, scc_components: &[usize]);

    /// Return outgoing successors of `root`.
    fn get_next(&mut self, root: usize) -> FxHashSet<usize>;

    /// Return the number of graph nodes.
    fn get_size(&mut self) -> usize;

    /// Recursive Tarjan traversal.
    fn tarjan(
        &mut self,
        index: usize,
        stack: &mut Vec<usize>,
        instack: &mut FxHashSet<usize>,
        dfn: &mut Vec<usize>,
        low: &mut Vec<usize>,
        time: &mut usize,
    ) {
        dfn[index] = *time;
        low[index] = *time;
        *time += 1;
        stack.push(index);
        instack.insert(index);

        let size = self.get_size();
        let nexts = self.get_next(index);
        for next in nexts {
            if next >= size {
                continue;
            }
            if dfn[next] == 0 {
                self.tarjan(next, stack, instack, dfn, low, time);
                low[index] = cmp::min(low[index], low[next]);
            } else if instack.contains(&next) {
                low[index] = cmp::min(low[index], dfn[next]);
            }
        }

        if dfn[index] == low[index] {
            let mut component = vec![index];
            while let Some(top) = stack.pop() {
                instack.remove(&top);
                if top == index {
                    break;
                }
                component.push(top);
            }
            self.on_scc_found(index, &component);
        }
    }
}

impl Scc for SccComponentCollector {
    fn on_scc_found(&mut self, _root: usize, scc_components: &[usize]) {
        self.components.push(scc_components.to_vec());
    }

    fn get_next(&mut self, root: usize) -> FxHashSet<usize> {
        self.successors
            .get(root)
            .into_iter()
            .flat_map(|successors| successors.iter().copied())
            .collect()
    }

    fn get_size(&mut self) -> usize {
        self.successors.len()
    }
}
