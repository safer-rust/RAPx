pub mod default;
pub mod graph;

use crate::utils::source::get_fn_name_byid;
use rustc_hir::def_id::DefId;
use std::fmt::{self, Display};

use crate::compat::FxHashMap;
use graph::PathGraph;

/// Format a path slice with cleanup-block annotations.
///
/// Cleanup blocks (MIR unwind/drop paths) are marked with a `*` suffix.
/// Example: `[0, 1, 2*, 3]` where block 2 is a cleanup block.
pub fn format_path_annotated(path: &[usize], graph: &PathGraph<'_>) -> String {
    let blocks: Vec<String> = path
        .iter()
        .map(|&b| {
            if graph.is_cleanup_block(b) {
                format!("{}*", b)
            } else {
                b.to_string()
            }
        })
        .collect();
    format!("[{}]", blocks.join(", "))
}

/// A prefix-tree (trie) of whole-CFG paths sharing common prefixes.
///
/// Paths are sequences of MIR block indices.  The trie compresses shared
/// prefixes — if two paths `[0,1,2,5]` and `[0,1,2,6]` are both inserted,
/// blocks 0→1→2 are stored once and branch at block 2.
///
/// Each node is a [`PathNode`]; a node with `is_path_end == true` marks the
/// end of a complete path that exists in the tree.  The `len` field tracks
/// the number of complete paths stored.
///
/// # Invariants
/// - All paths inserted into a given tree start with the same root block
///   (by construction, block 0 — the CFG entry).
/// - A path is only stored if it passed reachability filtering
///   (see [`PathGraph::check_transition`]).
#[derive(Debug, Clone)]
pub struct PathTree {
    root: Option<PathNode>,
    len: usize,
}

/// A node in a [`PathTree`] trie.
///
/// `block` is the MIR block index for this node.  `children` holds
/// successor blocks that appear after `block` in at least one stored
/// path.  `is_path_end` is `true` when some path terminates at this
/// node (i.e. this block is a CFG terminator for that path).
#[derive(Debug, Clone)]
pub struct PathNode {
    pub block: usize,
    pub children: Vec<PathNode>,
    pub is_path_end: bool,
}

impl PathNode {
    fn from_path(path: &[usize]) -> Self {
        let mut node = PathNode {
            block: path[0],
            children: Vec::new(),
            is_path_end: path.len() == 1,
        };
        if path.len() > 1 {
            node.children.push(PathNode::from_path(&path[1..]));
        }
        node
    }
}

impl PathTree {
    pub fn new() -> Self {
        PathTree { root: None, len: 0 }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn root(&self) -> Option<&PathNode> {
        self.root.as_ref()
    }

    /// Insert a path into the tree. Returns `true` if the path was
    /// newly added (not already present as a terminal path).
    pub fn insert(&mut self, path: &[usize]) -> bool {
        if path.is_empty() {
            return false;
        }

        match &mut self.root {
            None => {
                self.root = Some(PathNode::from_path(path));
                self.len = 1;
                true
            }
            Some(root) => {
                if root.block != path[0] {
                    return false;
                }
                if Self::insert_into(root, &path[1..]) {
                    self.len += 1;
                    true
                } else {
                    false
                }
            }
        }
    }

    fn insert_into(node: &mut PathNode, suffix: &[usize]) -> bool {
        if suffix.is_empty() {
            if node.is_path_end {
                return false;
            }
            node.is_path_end = true;
            return true;
        }

        let target = suffix[0];
        for child in &mut node.children {
            if child.block == target {
                return Self::insert_into(child, &suffix[1..]);
            }
        }

        node.children.push(PathNode::from_path(suffix));
        true
    }

    /// Check whether the given path exists as a complete path in the tree.
    pub fn contains(&self, path: &[usize]) -> bool {
        let mut node = match self.root.as_ref() {
            Some(n) => n,
            None => return false,
        };
        if node.block != path[0] {
            return false;
        }
        for &block in &path[1..] {
            node = match node.children.iter().find(|c| c.block == block) {
                Some(n) => n,
                None => return false,
            };
        }
        node.is_path_end
    }

    /// Enumerate all paths as owned `Vec<usize>`.
    pub fn iter(&self) -> PathTreeIter<'_> {
        PathTreeIter {
            stack: self
                .root
                .as_ref()
                .map(|r| vec![(r, vec![r.block])])
                .unwrap_or_default(),
        }
    }

    /// Collect all paths into a flat `Vec<Vec<usize>>`.
    pub fn to_vecs(&self) -> Vec<Vec<usize>> {
        self.iter().collect()
    }

    /// Walk the tree and call `f` with each unique prefix that ends at
    /// `target_block`. The walk stops at `target_block` (does not recurse
    /// into its children), so the callback receives the path from the root
    /// up to and including `target_block`.
    ///
    /// Returns `Ok(())` if the walk completed, or `Err(())` if `f` returned
    /// `false` to request early termination.
    pub fn walk_prefixes<F>(&self, target_block: usize, f: &mut F) -> Result<(), ()>
    where
        F: FnMut(&[usize]) -> bool,
    {
        let Some(root) = self.root.as_ref() else {
            return Ok(());
        };
        let mut path = Vec::new();
        Self::walk_prefixes_impl(root, &mut path, target_block, false, f)
    }

    /// Like [`walk_prefixes`] but continues past the target block into
    /// children, finding ALL occurrences (e.g. multiple iterations of the
    /// same checkpoint block in a loop).
    pub fn walk_all_prefixes<F>(&self, target_block: usize, f: &mut F) -> Result<(), ()>
    where
        F: FnMut(&[usize]) -> bool,
    {
        let Some(root) = self.root.as_ref() else {
            return Ok(());
        };
        let mut path = Vec::new();
        Self::walk_prefixes_impl(root, &mut path, target_block, true, f)
    }

    fn walk_prefixes_impl<F>(
        node: &PathNode,
        path: &mut Vec<usize>,
        target_block: usize,
        continue_past_target: bool,
        f: &mut F,
    ) -> Result<(), ()>
    where
        F: FnMut(&[usize]) -> bool,
    {
        path.push(node.block);
        if node.block == target_block {
            let cont = f(path);
            if !cont {
                path.pop();
                return Err(());
            }
            if !continue_past_target {
                path.pop();
                return Ok(());
            }
        }
        for child in &node.children {
            Self::walk_prefixes_impl(child, path, target_block, continue_past_target, f)?;
        }
        path.pop();
        Ok(())
    }
}

impl Default for PathTree {
    fn default() -> Self {
        Self::new()
    }
}

/// DFS iterator over all complete paths in a [`PathTree`].
///
/// Yields each path as an owned `Vec<usize>`.  Internal nodes (where
/// `is_path_end == false`) are skipped; only terminal path nodes are
/// emitted.
pub struct PathTreeIter<'a> {
    stack: Vec<(&'a PathNode, Vec<usize>)>,
}

impl<'a> Iterator for PathTreeIter<'a> {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (node, path) = self.stack.pop()?;
            for child in node.children.iter().rev() {
                let mut child_path = path.clone();
                child_path.push(child.block);
                self.stack.push((child, child_path));
            }
            if node.is_path_end {
                return Some(path);
            }
        }
    }
}

/// Display wrapper that prints all paths for every function, annotated
/// with cleanup-block markers via [`format_path_annotated`].
pub struct PathMapWrapper<'a, 'tcx>(
    pub FxHashMap<DefId, PathTree>,
    pub &'a FxHashMap<DefId, PathGraph<'tcx>>,
);

impl Display for PathMapWrapper<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Print path analysis results ===")?;
        for (def_id, paths) in &self.0 {
            let fn_name = get_fn_name_byid(def_id);
            if fn_name.contains("__raw_ptr_deref_dummy") {
                continue;
            }
            writeln!(f, "Function: {:?}:", fn_name)?;
            let graph = self.1.get(def_id);
            for path in paths.iter() {
                if let Some(g) = graph {
                    writeln!(f, "  Path {}", format_path_annotated(&path, g))?;
                } else {
                    writeln!(f, "  Path {:?}", path)?;
                }
            }
        }
        Ok(())
    }
}
