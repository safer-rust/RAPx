//! Per-function alias *derivation* forest, used only for field-path resolution.
//!
//! Every pointer-bearing local is a node; an edge `parent ← child` records that
//! the child was derived from the parent (reborrow, raw-pointer cast, field
//! read), each edge carrying the field path (`self.node.ptr` → `[node, ptr]`).
//! [`AliasTree::resolve_local_to_root`] walks the forest to the root local,
//! concatenating field paths, which the escape/encapsulation analysis uses to
//! find *which* struct field a view came from.
//!
//! The view-vs-view (shared-XOR-mutable) aliasing check no longer lives here —
//! it is flow-sensitive and walks the VM's current locals + allocation `parent`
//! chain (`flow_xor_violation` in `vm/alias.rs`), so this static forest is not
//! consulted for live-value grouping.

use crate::helpers::mir_utils;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Local, Operand, Rvalue, StatementKind};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

/// A node identifier (index into [`AliasTree::nodes`]).
pub(crate) type TagId = usize;

/// A single node in the alias forest.
#[derive(Clone, Debug)]
pub(crate) struct AliasNode {
    pub parent: Option<TagId>,
    /// Field projections (`ProjectionElem::Field` indices) from the parent's
    /// referent down to this pointer (e.g. `self.node.ptr` → `[node, ptr]`).
    /// Empty for whole-local pointers. Used by [`AliasTree::resolve_to_root`] to
    /// reconstruct the nested-field origin.
    pub fields: Vec<usize>,
    pub local: Local,
}

/// The per-function alias derivation forest.
#[derive(Clone, Debug)]
pub(crate) struct AliasTree {
    pub nodes: Vec<AliasNode>,
    /// The tag that `local` currently names (its most recent binding).
    tag_of_local: FxHashMap<Local, TagId>,
}

impl AliasTree {
    /// Build the derivation forest for `def_id` by scanning its MIR.
    ///
    /// Parameters and owned results are roots; every `target =
    /// <ref/cast/raw/copy> source` statement adds an edge from `source`'s tag to
    /// a new (or shared) tag for `target`. `StorageDead`/moves are *not* applied
    /// here — the forest is a static, block-order approximation used only for
    /// field-path resolution.
    pub(crate) fn build<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        let body = tcx.optimized_mir(def_id);
        let mut tree = AliasTree {
            nodes: Vec::new(),
            tag_of_local: FxHashMap::default(),
        };

        for local_index in 1..=body.arg_count {
            let local = Local::from_usize(local_index);
            let ty = body.local_decls[local].ty;
            if classify(ty).is_some() {
                tree.add(None, Vec::new(), local);
            }
        }

        for block in body.basic_blocks.iter() {
            for statement in &block.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let (target, rvalue) = assign.as_ref();
                match rvalue {
                    // Copy/move of a *whole* pointer is the same tag, not a new
                    // node. A copy through a field projection (`_2 = (*self).next`)
                    // is a *derivation* (reads the raw field), so it falls through
                    // to the derivation arm below.
                    Rvalue::Use(Operand::Copy(place), ..)
                    | Rvalue::Use(Operand::Move(place), ..)
                    | Rvalue::CopyForDeref(place)
                        if field_projection(place).is_empty() =>
                    {
                        if let Some(tag) = tree.tag_of_local.get(&place.local).copied() {
                            tree.tag_of_local.insert(target.local, tag);
                        }
                    }
                    // True derivation: reborrow (`&mut x`), raw-pointer creation
                    // (`addr_of!(x)`), cast (`&mut → *mut`, `*mut → *const`) and
                    // field read (`(*self).next`).
                    _ => {
                        if let Some(place) = mir_utils::rvalue_source_place(rvalue)
                            && let Some(parent) = tree.tag_of_local.get(&place.local).copied()
                        {
                            let ty = body.local_decls[target.local].ty;
                            if classify(ty).is_some() {
                                tree.add(Some(parent), field_projection(place), target.local);
                            }
                        }
                    }
                }
            }

            // Call destinations: `p = v.as_mut_ptr()` / `into_raw` /
            // `from_raw_parts` — the returned pointer derives from the first
            // argument (the receiver/pointer). An *owned* result (`Box::new`,
            // `Vec::new`, `Box::from_raw`) is a fresh owner, so it becomes a root
            // regardless of whether its first argument is a place.
            if let rustc_middle::mir::TerminatorKind::Call {
                args, destination, ..
            } = &block.terminator().kind
            {
                let dest_local = destination.local;
                let dest_ty = body.local_decls[dest_local].ty;
                if let Some(is_owned) = classify(dest_ty) {
                    if is_owned {
                        tree.add(None, Vec::new(), dest_local);
                    } else if let Some(first_arg) = args.first()
                        && let Some(place) = first_arg.node.place()
                        && let Some(parent) = tree.tag_of_local.get(&place.local).copied()
                    {
                        tree.add(Some(parent), field_projection(&place), dest_local);
                    }
                }
            }
        }

        tree
    }

    fn add(&mut self, parent: Option<TagId>, fields: Vec<usize>, local: Local) -> TagId {
        let tag = self.nodes.len();
        self.nodes.push(AliasNode {
            parent,
            fields,
            local,
        });
        self.tag_of_local.insert(local, tag);
        tag
    }

    /// The tag bound to `local`, if any.
    pub(crate) fn tag_of(&self, local: Local) -> Option<TagId> {
        self.tag_of_local.get(&local).copied()
    }

    /// Walk `tag`'s parent edges to the root, concatenating the `fields` of each
    /// hop. Returns the root local and the full field path (`self.node.ptr` →
    /// `(self, [node, ptr])`).
    fn resolve_to_root(&self, tag: TagId) -> (Local, Vec<usize>) {
        let mut cur = tag;
        let mut fields: Vec<usize> = Vec::new();
        let mut guard = 0;
        loop {
            let node = &self.nodes[cur];
            let mut combined = node.fields.clone();
            combined.extend(fields.iter().copied());
            fields = combined;
            match node.parent {
                Some(parent) => cur = parent,
                None => return (node.local, fields),
            }
            guard += 1;
            if guard > self.nodes.len() {
                return (self.nodes[cur].local, fields);
            }
        }
    }

    /// Resolve a local to its root `(root_local, field_path)` via the tree. An
    /// unmapped local resolves to itself with an empty field path.
    pub(crate) fn resolve_local_to_root(&self, local: Local) -> (usize, Vec<usize>) {
        match self.tag_of(local) {
            Some(tag) => {
                let (root, fields) = self.resolve_to_root(tag);
                (root.as_usize(), fields)
            }
            None => (local.as_usize(), Vec::new()),
        }
    }
}

/// The `Field` projection indices of `place`, in order (`Deref`/index/etc. are
/// skipped), matching `PlaceKey::fields`.
fn field_projection(place: &rustc_middle::mir::Place<'_>) -> Vec<usize> {
    place
        .projection
        .iter()
        .filter_map(|p| match p {
            rustc_middle::mir::ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
            _ => None,
        })
        .collect()
}

/// Whether `ty` is pointer-bearing (`Ref`/`RawPtr`/`Adt`), returning whether it
/// is an *owned* container (`Box`/`Vec`/… — a forest root) when it is.
fn classify(ty: Ty<'_>) -> Option<bool> {
    match ty.kind() {
        TyKind::Ref(_, _, _) | TyKind::RawPtr(_, _) => Some(false),
        TyKind::Adt(_, _) => Some(true),
        _ => None,
    }
}
