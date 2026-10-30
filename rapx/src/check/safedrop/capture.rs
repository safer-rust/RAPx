//! Conversion of live compiler/analysis state to owned SafeDrop evidence.

use std::{collections::BTreeSet, num::NonZeroU32};

use rustc_middle::mir::{BasicBlock, Local};
use rustc_span::{FileName, Span};

use crate::{analysis::alias::default::graph::AliasGraph, utils::span::get_variable_name};

use super::{
    bug_records::TyBug,
    drop::{DropRecord, LocalSpot},
    graph::SafeDropGraph,
    report::{
        SafeDropFinding, SafeDropFunction, SafeDropSite, SafeDropValue, SafeDropWitness,
        SourceLocation,
    },
};

/// Capture only relevant state and cap the alias neighborhood per witness.
pub fn witness(
    graph: &AliasGraph<'_>,
    records: &[DropRecord],
    value_idx: usize,
    path: &[usize],
) -> SafeDropWitness {
    let record = &records[value_idx];
    let mut ids = BTreeSet::from([value_idx]);
    ids.extend(record.prop_chain.iter().copied());
    // drop_spot.local is a MIR local (not necessarily a projected value index).
    ids.extend(record.drop_spot.local);
    let seeds: Vec<_> = ids.iter().copied().collect();
    for id in seeds {
        if let Some(aliases) = graph.get_alias_set(id) {
            ids.extend(aliases);
        }
    }
    let mut limitations = Vec::new();
    // Keep the triggering value even when its index is greater than the cap.
    let mut selected = vec![value_idx];
    selected.extend(ids.iter().copied().filter(|id| *id != value_idx).take(63));
    if ids.len() > selected.len() {
        limitations.push("related_values_truncated".into());
    }
    let body = graph.tcx().optimized_mir(graph.def_id());
    let values = selected
        .iter()
        .filter_map(|&id| {
            let value = graph.values.get(id)?;
            let slot = graph.value_to_slot_idx(id);
            let mut pointees: Vec<_> = slot
                .map(|s| {
                    graph
                        .pts_graph
                        .direct_pointees(s)
                        .map(|p| format!("{p:?}"))
                        .collect()
                })
                .unwrap_or_default();
            pointees.sort();
            Some(SafeDropValue {
                value_index: id,
                local: value.local,
                name: get_variable_name(body, value.local),
                local_type: body
                    .local_decls
                    .get(Local::from_usize(value.local))
                    .map(|d| d.ty.to_string()),
                fields: slot
                    .and_then(|s| graph.pts_graph.get_slot(s))
                    .map(|s| s.fields.clone())
                    .unwrap_or_default(),
                kind: slot.map(|s| format!("{:?}", graph.pts_graph.slot_kind(s))),
                may_drop: graph.value_may_drop(id),
                needs_drop: slot.is_some_and(|s| graph.pts_graph.need_drop(s)),
                is_dropped: records.get(id).is_some_and(|r| r.is_dropped),
                has_dropped_field: records.get(id).is_some_and(|r| r.has_dropped_field),
                may_alias: graph.get_alias_set(id).unwrap_or_default(),
                direct_pointees: pointees,
            })
        })
        .collect();
    let mut owner_transfers: Vec<_> = graph
        .owner_transfers
        .iter()
        .filter(|(dest, src)| selected.contains(dest) || selected.contains(src))
        .map(|(&dest, &src)| (dest, src))
        .collect();
    owner_transfers.sort_unstable();
    SafeDropWitness {
        path_prefix: path.to_vec(),
        drop_propagation: record.prop_chain.clone(),
        values,
        owner_transfers,
        limitations,
    }
}

pub fn source_location(graph: &AliasGraph<'_>, span: Span) -> Option<SourceLocation> {
    if span.is_dummy() {
        return None;
    }
    let sm = graph.tcx().sess.source_map();
    let start = sm.lookup_char_pos(span.lo());
    let end = sm.lookup_char_pos(span.hi());
    if start.file.start_pos != end.file.start_pos {
        return None;
    }
    let FileName::Real(name) = &start.file.name else {
        return None;
    };
    let path = name.local_path()?.to_string_lossy().into_owned();
    // Hash the compiler's source snapshot rather than a later filesystem read.
    // FNV is a freshness hint, not a cryptographic integrity guarantee.
    let source_digest = start.file.src.as_ref().map(|source| {
        let hash = source
            .as_bytes()
            .iter()
            .fold(0xcbf29ce484222325u64, |hash, byte| {
                (hash ^ u64::from(*byte)).wrapping_mul(0x100000001b3)
            });
        format!("fnv1a64:{hash:016x}")
    });
    Some(SourceLocation {
        path,
        start_line: NonZeroU32::new(u32::try_from(start.line).ok()?)?,
        start_column: NonZeroU32::new(u32::try_from(start.col.0).ok()?.checked_add(1)?)?,
        end_line: NonZeroU32::new(u32::try_from(end.line).ok()?)?,
        end_column: NonZeroU32::new(u32::try_from(end.col.0).ok()?.checked_add(1)?)?,
        source_digest,
    })
}

fn site(graph: &AliasGraph<'_>, spot: LocalSpot) -> SafeDropSite {
    // A terminator mapping is only a block-level anchor, not necessarily the
    // first release or exact UAF instruction.
    let location = spot
        .bb
        .and_then(|bb| graph.terminator(bb))
        .and_then(|term| source_location(graph, term.source_info.span));
    SafeDropSite {
        local: spot.local,
        basic_block: spot.bb,
        location,
    }
}

pub fn function_context(graph: &SafeDropGraph<'_>) -> SafeDropFunction {
    let alias = &graph.alias_graph;
    let body = alias.tcx().optimized_mir(alias.def_id());
    let source = alias
        .tcx()
        .sess
        .source_map()
        .span_to_snippet(alias.span())
        .ok();
    let mut mir = String::new();
    use std::fmt::Write;
    for (local, decl) in body.local_decls.iter_enumerated() {
        let _ = writeln!(mir, "let {local:?}: {};", decl.ty);
    }
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let _ = writeln!(mir, "{bb:?} (cleanup={}):", data.is_cleanup);
        for stmt in &data.statements {
            let _ = writeln!(mir, "  {stmt:?}");
        }
        if let Some(term) = &data.terminator {
            let _ = writeln!(mir, "  {term:?}");
        }
    }
    SafeDropFunction { source, mir }
}

pub fn findings(graph: &SafeDropGraph<'_>) -> Vec<SafeDropFinding> {
    if graph.bug_records.is_bug_free() {
        return Vec::new();
    }
    let alias = &graph.alias_graph;
    let body = alias.tcx().optimized_mir(alias.def_id());
    let records = &graph.bug_records;
    let mut bugs: Vec<(&TyBug, bool)> = Vec::new();
    for (map, unwind) in [
        (&records.df_bugs, false),
        (&records.df_bugs_unwind, true),
        (&records.uaf_bugs, false),
        (&records.dp_bugs, false),
        (&records.dp_bugs_unwind, true),
    ] {
        bugs.extend(map.values().map(|bug| (bug, unwind)));
    }
    bugs.sort_by_key(|(b, unwind)| {
        (
            b.trigger_info.bb,
            b.trigger_info.local,
            b.drop_spot.bb,
            *unwind,
        )
    });
    bugs.into_iter()
        .map(|(bug, unwind)| {
            let location = source_location(alias, bug.span);
            let during_unwind = unwind
                || bug.trigger_info.bb.is_some_and(|bb| {
                    body.basic_blocks
                        .get(BasicBlock::from_usize(bb))
                        .is_some_and(|b| b.is_cleanup)
                });
            SafeDropFinding {
                id: String::new(), // assigned within this compilation unit when written
                function: alias.tcx().def_path_str(alias.def_id()),
                bug_type: bug.bug_type,
                confidence: bug.confidence,
                during_unwind,
                location,
                drop_site: site(alias, bug.drop_spot),
                trigger_site: site(alias, bug.trigger_info),
                witness: bug.witness.clone(),
            }
        })
        .collect()
}
