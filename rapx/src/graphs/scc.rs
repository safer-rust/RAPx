//! Shared strongly-connected-component utilities.
//!
//! This module provides the small Tarjan SCC abstraction used by RAP analyses
//! and by the verification path extractor. The trait is intentionally graph
//! agnostic: clients provide successor queries and receive each discovered SCC
//! through `on_scc_found`.

use rustc_data_structures::fx::FxHashSet;
use std::cmp;

/// An outgoing edge from an SCC body to a block outside the SCC.
#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct SccExit {
    pub exit: usize,
    pub to: usize,
}

impl SccExit {
    /// Create an SCC exit edge from `exit` to `to`.
    pub fn new(exit: usize, to: usize) -> Self {
        SccExit { exit, to }
    }
}

/// Per-header SCC metadata used by loop-aware analyses.
#[derive(Debug, Clone)]
pub struct SccInfo {
    /// Representative entry block of the SCC.
    pub enter: usize,
    /// Other blocks in the SCC, excluding `enter`.
    pub nodes: FxHashSet<usize>,
    /// Edges leaving the SCC.
    pub exits: FxHashSet<SccExit>,
    /// Blocks with back edges to the SCC representative.
    pub backnodes: FxHashSet<usize>,
    /// Representative `enter` nodes of nested child SCCs.
    pub child_sccs: Vec<usize>,
}

impl SccInfo {
    /// Create empty SCC metadata for `enter`.
    pub fn new(enter: usize) -> Self {
        SccInfo {
            enter,
            nodes: FxHashSet::default(),
            exits: FxHashSet::default(),
            backnodes: FxHashSet::default(),
            child_sccs: Vec::new(),
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
