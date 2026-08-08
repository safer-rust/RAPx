use std::collections::VecDeque;

use crate::compat::{FxHashMap, FxHashSet};
use crate::helpers::def_use::{PlaceBaseKey, PlaceKey};

use super::slot::{AbstractLoc, Slot};

use crate::analysis::alias::default::types::ValueKind;

pub const MAX_VALUES_PER_PATH: usize = 1000;

/// Unified points-to and value-flow graph.
///
/// Maintains two directed relationship types between slots:
///
/// * **points_to**: the slot holds a pointer/reference *into* another slot.
///   Created by `&_x`, `&raw _x`, etc.
/// * **value_flow**: the slot's *value* is a copy of another slot's value.
///   Created by `_a = _b` (Copy/Move), `_a = _b as *const T` (Cast), etc.
///
/// Alias queries (`may_alias`) combine:
/// * **Alias partition**: value-equivalence through assignments (union-find)
/// * **Points-to intersection**: pointer-level aliasing through references
#[derive(Clone, Debug)]
pub struct PtsGraph {
    points_to: Vec<FxHashSet<AbstractLoc>>,
    value_flow: Vec<FxHashSet<usize>>,
    slots: Vec<Slot>,
    slot_index: FxHashMap<Slot, usize>,
    may_drop: Vec<bool>,
    need_drop: Vec<bool>,
    /// Type classification per slot (RawPtr, Ref, Adt, etc.).
    slot_kind: Vec<ValueKind>,

    /// Alias partition: which slots are value-equivalent (union-find).
    /// `alias_parent[i]` is the representative of i's partition,
    /// or `i` itself if i is the root. `None` means uninitialized (singleton).
    alias_parent: Vec<usize>,
}

impl PtsGraph {
    pub fn new() -> Self {
        PtsGraph {
            points_to: Vec::new(),
            value_flow: Vec::new(),
            slots: Vec::new(),
            slot_index: FxHashMap::default(),
            may_drop: Vec::new(),
            need_drop: Vec::new(),
            slot_kind: Vec::new(),
            alias_parent: Vec::new(),
        }
    }

    pub fn slot_count(&self) -> usize {
        self.slots.len()
    }

    pub fn get_slot(&self, idx: usize) -> Option<&Slot> {
        self.slots.get(idx)
    }

    pub fn get_slot_idx(&self, slot: &Slot) -> Option<usize> {
        self.slot_index.get(slot).copied()
    }

    pub fn may_drop(&self, idx: usize) -> bool {
        self.may_drop.get(idx).copied().unwrap_or(false)
    }

    pub fn need_drop(&self, idx: usize) -> bool {
        self.need_drop.get(idx).copied().unwrap_or(false)
    }

    // ── Slot registration ──────────────────────────────────────────

    pub fn ensure_slot(&mut self, slot: Slot, may_drop: bool, need_drop: bool) -> usize {
        if let Some(&idx) = self.slot_index.get(&slot) {
            return idx;
        }
        if self.slots.len() >= MAX_VALUES_PER_PATH {
            return 0;
        }
        let idx = self.slots.len();
        self.slots.push(slot.clone());
        self.slot_index.insert(slot, idx);
        self.points_to.push(FxHashSet::default());
        self.value_flow.push(FxHashSet::default());
        self.may_drop.push(may_drop);
        self.need_drop.push(need_drop);
        self.slot_kind.push(ValueKind::Adt);
        self.alias_parent.push(idx); // singleton: points to itself
        idx
    }

    pub fn set_slot_kind(&mut self, idx: usize, kind: ValueKind) {
        if idx < self.slot_kind.len() {
            self.slot_kind[idx] = kind;
        }
    }

    pub fn slot_kind(&self, idx: usize) -> ValueKind {
        self.slot_kind.get(idx).copied().unwrap_or(ValueKind::Adt)
    }

    pub fn slot_is_ptr(&self, idx: usize) -> bool {
        matches!(self.slot_kind(idx), ValueKind::RawPtr | ValueKind::Ref)
    }

    pub fn slot_is_ref_count(&self, idx: usize) -> bool {
        matches!(self.slot_kind(idx), ValueKind::SpecialPtr)
    }

    // ── Value-flow updates ─────────────────────────────────────────

    /// Return the direct pointee targets for a slot (non-transitive).
    pub fn direct_pointees(&self, idx: usize) -> impl Iterator<Item = &AbstractLoc> {
        self.points_to[idx].iter()
    }

    /// Record that `dest` points to `target`.
    /// Strong update: clears old points-to info for `dest`.
    pub fn assign_pointee(&mut self, dest_idx: usize, target: AbstractLoc) {
        self.points_to[dest_idx].clear();
        self.points_to[dest_idx].insert(target);
    }

    /// Record that `dest` has the same VALUE as `src` (Copy/Move/Cast).
    /// This is a strong update:
    /// - Remove `dest` from its old alias partition (other members stay)
    /// - Put `dest` into `src`'s alias partition
    /// - Also propagate to field slots.
    pub fn assign_value(&mut self, dest_idx: usize, src_idx: usize) {
        self.value_flow[dest_idx].clear();
        self.value_flow[dest_idx].insert(src_idx);

        // ── Alias partition: strong update ──
        self.alias_move_to_partition(dest_idx, src_idx);

        // ── Field-level propagation ──
        if dest_idx < self.slots.len() && src_idx < self.slots.len() {
            let dest_slot = self.slots[dest_idx].clone();
            let src_slot = self.slots[src_idx].clone();

            // Propagate to sub-fields: for every slot that extends dest
            // (same local, additional field projections), find the
            // corresponding slot that extends src and connect them.
            let dest_prefix = &dest_slot.fields;
            let mut field_pairs: Vec<(usize, usize)> = Vec::new();
            for (cand, cand_s) in self.slots.iter().enumerate() {
                if cand_s.local != dest_slot.local {
                    continue;
                }
                if cand_s.fields.len() <= dest_prefix.len() {
                    continue;
                }
                if cand_s.fields[..dest_prefix.len()] != *dest_prefix {
                    continue;
                }
                // cand_s is a sub-field of dest (e.g., dest=_0.0, cand=_0.0.0)
                let suffix = &cand_s.fields[dest_prefix.len()..];
                let mut src_sub_slot = Slot::new(src_slot.local);
                src_sub_slot.fields = src_slot.fields.clone();
                src_sub_slot.fields.extend_from_slice(suffix);
                if let Some(&src_sub_idx) = self.slot_index.get(&src_sub_slot) {
                    field_pairs.push((cand, src_sub_idx));
                }
            }
            for (dest_cand, src_field_idx) in field_pairs {
                self.value_flow[dest_cand].clear();
                self.value_flow[dest_cand].insert(src_field_idx);
                self.alias_move_to_partition(dest_cand, src_field_idx);
            }
        }
    }

    /// Merge equivalence: the two slots may hold the same pointer.
    /// Both inherit the union of each other's points-to set.
    /// This is used for inter-procedural aliasing and branch join points.
    /// Also propagates to father slots so SafeDrop can detect aliasing
    /// through the base local (e.g. `_v.0` alias `ptr` → `_v` alias `s`).
    pub fn merge_equivalence(&mut self, a_idx: usize, b_idx: usize) {
        if a_idx == b_idx {
            return;
        }
        // Merge points-to sets
        let a_pts: Vec<_> = self.points_to[a_idx].iter().cloned().collect();
        for loc in a_pts {
            self.points_to[b_idx].insert(loc);
        }
        let b_pts: Vec<_> = self.points_to[b_idx].iter().cloned().collect();
        for loc in b_pts {
            self.points_to[a_idx].insert(loc);
        }

        // Merge alias partitions
        self.alias_union(a_idx, b_idx);

        // Propagate one level upward so SafeDrop's value-level queries
        // can find field-level aliases (e.g. _b2.0 aliases p → _b2 aliases p).
        self.propagate_to_father(a_idx, b_idx);
    }

    fn propagate_to_father(&mut self, a_idx: usize, b_idx: usize) {
        let fa = self.father_of(a_idx);
        let fb = self.father_of(b_idx);
        let ra = fa.unwrap_or(a_idx);
        let rb = fb.unwrap_or(b_idx);
        if self.alias_find(ra) != self.alias_find(rb) {
            self.alias_union(ra, rb);
        }
    }

    fn father_of(&self, idx: usize) -> Option<usize> {
        let slot = &self.slots[idx];
        if slot.fields.is_empty() {
            return None;
        }
        let father_slot = Slot {
            local: slot.local,
            fields: slot.fields[..slot.fields.len() - 1].to_vec(),
        };
        self.slot_index.get(&father_slot).copied()
    }

    /// Conservative merge for unknown-function calls: all pointer-typed
    /// args may alias each other and the return value.
    pub fn conservative_call_merge(&mut self, arg_slots: &[usize]) {
        let mut pointer_args: Vec<usize> = Vec::new();
        for &idx in arg_slots {
            if !self.points_to[idx].is_empty() {
                pointer_args.push(idx);
            } else if self.may_drop(idx) {
                pointer_args.push(idx);
            }
        }
        for i in 0..pointer_args.len() {
            for j in (i + 1)..pointer_args.len() {
                self.merge_equivalence(pointer_args[i], pointer_args[j]);
            }
        }
    }

    // ── Queries ────────────────────────────────────────────────────

    /// Transitive points-to set: follow value_flow + points_to until
    /// fixpoint.  Returns all AbstractLoc reachable from `start_idx`.
    pub fn pts(&self, start_idx: usize) -> FxHashSet<AbstractLoc> {
        let mut result = FxHashSet::default();
        let mut visited = FxHashSet::default();
        let mut queue = VecDeque::new();
        queue.push_back(Start::Pointee(start_idx));
        visited.insert(Visit::Pointee(start_idx));

        while let Some(current) = queue.pop_front() {
            match current {
                Start::Pointee(idx) => {
                    for loc in &self.points_to[idx] {
                        if !matches!(loc, AbstractLoc::Null) {
                            result.insert(loc.clone());
                        }
                    }
                    for &src in &self.value_flow[idx] {
                        if visited.insert(Visit::Pointee(src)) {
                            queue.push_back(Start::Pointee(src));
                        }
                    }
                }
            }
        }
        result
    }

    /// May-alias check: do the pointed-to memories of `a` and `b` overlap?
    /// Combines:
    /// 1. Alias partition check (value-equivalence via assignments)
    /// 2. Points-to intersection (pointer-level aliasing)
    pub fn may_alias(&self, a_idx: usize, b_idx: usize) -> bool {
        // Check alias partition (value-equivalence)
        if self.alias_find(a_idx) == self.alias_find(b_idx) {
            return true;
        }
        // Check points-to intersection
        let pta = self.pts(a_idx);
        if pta.is_empty() {
            return false;
        }
        let ptb = self.pts(b_idx);
        pta.intersection(&ptb).next().is_some()
    }

    // ── Inter-procedural ───────────────────────────────────────────

    /// Apply callee's FnAliasPairs to the graph at a call site.
    /// `callee_arg_slots`: [ret_dest_idx, arg₀_idx, arg₁_idx, ...]
    pub fn apply_callee_summary(
        &mut self,
        callee_pairs: &crate::analysis::alias::FnAliasPairs,
        callee_arg_slots: &[usize],
    ) {
        for alias in callee_pairs.aliases() {
            let left_idx = alias.left_local();
            let right_idx = alias.right_local();

            if left_idx >= callee_arg_slots.len() || right_idx >= callee_arg_slots.len() {
                continue;
            }

            let mut lv = callee_arg_slots[left_idx];
            let mut rv = callee_arg_slots[right_idx];

            for &field_idx in alias.lhs_fields() {
                let field_slot = self.slots[lv].project(field_idx);
                if let Some(idx) = self.slot_index.get(&field_slot) {
                    lv = *idx;
                } else {
                    let idx = self.ensure_slot(field_slot, self.may_drop[lv], self.need_drop[lv]);
                    lv = idx;
                }
            }
            for &field_idx in alias.rhs_fields() {
                let field_slot = self.slots[rv].project(field_idx);
                if let Some(idx) = self.slot_index.get(&field_slot) {
                    rv = *idx;
                } else {
                    let idx = self.ensure_slot(field_slot, self.may_drop[rv], self.need_drop[rv]);
                    rv = idx;
                }
            }

            if self.may_drop(lv) && self.may_drop(rv) {
                self.merge_equivalence(lv, rv);
            }
        }
    }

    // ── FnAliasPairs extraction ────────────────────────────────────

    /// Compute field-sensitive alias pairs among args (1..=arg_count) + return
    /// value (0).  For each pair, checks `may_alias()` and if true, emits an
    /// `AliasPair` with the truncated single-level field paths.
    pub fn fn_alias_pairs(&self, arg_count: usize) -> crate::analysis::alias::FnAliasPairs {
        let mut pairs = crate::analysis::alias::FnAliasPairs::new(arg_count);

        let local_ids: Vec<usize> = (0..=arg_count).collect();

        // Map each local -> its base slot index (the slot with empty fields).
        let mut local_to_base_slot: FxHashMap<usize, usize> = FxHashMap::default();
        for (slot_idx, s) in self.slots.iter().enumerate() {
            if s.fields.is_empty() && s.local <= arg_count {
                local_to_base_slot.entry(s.local).or_insert(slot_idx);
            }
        }

        // Base-level alias check.
        for i in 0..local_ids.len() {
            for j in (i + 1)..local_ids.len() {
                let li = local_ids[i];
                let lj = local_ids[j];
                let Some(&slot_i) = local_to_base_slot.get(&li) else {
                    continue;
                };
                let Some(&slot_j) = local_to_base_slot.get(&lj) else {
                    continue;
                };
                if self.may_alias(slot_i, slot_j) {
                    let mut pair = crate::analysis::alias::AliasPair::new(li, lj);
                    pair.lhs_fields = vec![];
                    pair.rhs_fields = vec![];
                    pairs.add_alias(pair);
                }
            }
        }

        // Field-level alias checks.
        let field_slots: Vec<(usize, Vec<usize>)> = self
            .slots
            .iter()
            .enumerate()
            .filter_map(|(idx, slot)| {
                if !slot.fields.is_empty() && slot.local <= arg_count {
                    Some((idx, slot.fields.clone()))
                } else {
                    None
                }
            })
            .collect();

        for (idx_a, fields_a) in &field_slots {
            let slot_a = &self.slots[*idx_a];
            // Field ↔ Field
            for (idx_b, fields_b) in &field_slots {
                if idx_a == idx_b {
                    continue;
                }
                let slot_b = &self.slots[*idx_b];
                if slot_a.local == slot_b.local {
                    continue;
                }
                if self.may_alias(*idx_a, *idx_b) {
                    let mut pair =
                        crate::analysis::alias::AliasPair::new(slot_a.local, slot_b.local);
                    pair.lhs_fields = fields_a.clone();
                    pair.rhs_fields = fields_b.clone();
                    pairs.add_alias(pair);
                }
            }
            // Field ↔ Base (cross-level)
            for &base_local in &local_ids {
                if slot_a.local == base_local {
                    continue;
                }
                let Some(&base_slot_idx) = local_to_base_slot.get(&base_local) else {
                    continue;
                };
                if self.may_alias(*idx_a, base_slot_idx) {
                    let mut pair = crate::analysis::alias::AliasPair::new(slot_a.local, base_local);
                    pair.lhs_fields = fields_a.clone();
                    pair.rhs_fields = vec![];
                    pairs.add_alias(pair);
                }
            }
        }

        // Compress field paths: truncate each side to its first element,
        // matching the old MoP alias analysis behavior.
        pairs.compress_fields();

        pairs.sort_alias_index();
        pairs
    }

    // ── Alias partition (Union-Find for value-equivalence) ──────────

    /// Find the representative of `idx`'s alias partition.
    fn alias_find(&self, idx: usize) -> usize {
        if idx >= self.alias_parent.len() {
            return idx;
        }
        let mut cur = idx;
        while self.alias_parent[cur] != cur {
            cur = self.alias_parent[cur];
        }
        cur
    }

    /// Union two alias partitions.
    fn alias_union(&mut self, a: usize, b: usize) {
        let ra = self.alias_find(a);
        let rb = self.alias_find(b);
        if ra != rb {
            self.alias_parent[ra] = rb;
        }
    }

    /// Move `slot_idx` from its current partition to `target_idx`'s partition.
    /// This implements the strong-update semantics of MoP's `assign_alias`:
    /// the moved slot leaves its old partition behind.
    fn alias_move_to_partition(&mut self, slot_idx: usize, target_idx: usize) {
        if slot_idx >= self.alias_parent.len() {
            return;
        }
        // Point slot_idx directly to target's root
        let target_root = self.alias_find(target_idx);
        self.alias_parent[slot_idx] = target_root;
    }

    /// Strong-update: put all slots in `slot_idx`'s partition into their
    /// own singleton partitions, breaking all alias-equivalence for the
    /// entire partition. Used when a call produces a fresh value that
    /// must not retain any old alias relationships.
    pub fn reset_partition(&mut self, slot_idx: usize) {
        if slot_idx >= self.alias_parent.len() {
            return;
        }
        let root = self.alias_find(slot_idx);
        for i in 0..self.alias_parent.len() {
            if self.alias_find(i) == root {
                self.alias_parent[i] = i;
            }
        }
    }

    // ── PlaceKey-oriented adapter methods ──────────────────────────

    /// Record that `pointer` place was derived from `source` place.
    /// Strong-update semantics: clears old points-to info for the pointer.
    pub fn insert_place_edge(&mut self, pointer: &PlaceKey, source: &PlaceKey) {
        let ptr_slot = Self::place_key_to_slot(pointer);
        let src_slot = Self::place_key_to_slot(source);
        let ptr_idx = self.ensure_slot(ptr_slot, false, false);
        self.ensure_slot(src_slot.clone(), false, false);
        self.assign_pointee(ptr_idx, AbstractLoc::Slot(src_slot));
    }

    /// Single-step points-to lookup (non-transitive) with overlap semantics.
    /// When the exact place has no edge, falls back through field-stripping.
    pub fn get_place_source(&self, place: &PlaceKey) -> Option<PlaceKey> {
        let mut slot = Self::place_key_to_slot(place);
        loop {
            if let Some(idx) = self.slot_index.get(&slot) {
                if let Some(first_loc) = self.points_to.get(*idx).and_then(|set| set.iter().next())
                {
                    if let AbstractLoc::Slot(target) = first_loc {
                        return Some(Self::slot_to_place_key(target));
                    }
                }
            }
            if slot.fields.is_empty() {
                return None;
            }
            slot.fields.pop();
        }
    }

    /// Transitive points-to resolution with overlap semantics and loop
    /// detection.
    pub fn resolve_place(&self, place: &PlaceKey) -> PlaceKey {
        let mut cur = place.clone();
        let mut seen: Vec<PlaceKey> = vec![cur.clone()];
        loop {
            let Some(next) = self.get_place_source(&cur) else {
                break;
            };
            if seen.iter().any(|p| p == &next) {
                break;
            }
            seen.push(next.clone());
            cur = next.clone();
        }
        cur
    }

    /// Return all PlaceKey-based points-to edges.
    pub fn place_edges(&self) -> Vec<(PlaceKey, PlaceKey)> {
        let mut edges = Vec::new();
        for (idx, targets) in self.points_to.iter().enumerate() {
            let Some(slot) = self.slots.get(idx) else {
                continue;
            };
            let pointer = Self::slot_to_place_key(slot);
            for target in targets {
                if let AbstractLoc::Slot(target_slot) = target {
                    let source = Self::slot_to_place_key(target_slot);
                    edges.push((pointer.clone(), source));
                }
            }
        }
        edges
    }

    fn place_key_to_slot(pk: &PlaceKey) -> Slot {
        let local = pk.local().map(|l| l.as_usize()).unwrap_or(0);
        Slot {
            local,
            fields: pk.fields.clone(),
        }
    }

    fn slot_to_place_key(slot: &Slot) -> PlaceKey {
        PlaceKey {
            base: PlaceBaseKey::Local(slot.local),
            fields: slot.fields.clone(),
        }
    }
}

impl Default for PtsGraph {
    fn default() -> Self {
        Self::new()
    }
}

// ── Internal helpers for transitive search ─────────────────────────

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
enum Start {
    Pointee(usize),
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
enum Visit {
    Pointee(usize),
}
