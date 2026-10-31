//! Convert live MIR, ownership and solver state into reviewable evidence.

use std::{collections::BTreeSet, fmt::Write, num::NonZeroU32};

use rustc_middle::{
    mir::{BasicBlock, Body, Local, Terminator},
    ty::TyCtxt,
};
use rustc_span::{FileName, Span, def_id::DefId};

use crate::utils::span::get_variable_name;

use super::{
    ranalyzer::{IcxSliceFroBlock, ownership::IntraVar},
    report::{
        BugType, RCanaryFinding, RCanaryFunction, RCanaryLocal, RCanarySite, SolverEvidence,
        SourceLocation,
    },
};

#[derive(Default)]
pub(crate) struct FunctionReport {
    pub findings: Vec<RCanaryFinding>,
    pub checked_returns: usize,
    pub limitations: BTreeSet<String>,
}

pub fn source_location(tcx: TyCtxt<'_>, span: Span) -> Option<SourceLocation> {
    if span.is_dummy() {
        return None;
    }
    let sm = tcx.sess.source_map();
    let start = sm.lookup_char_pos(span.lo());
    let end = sm.lookup_char_pos(span.hi());
    if start.file.start_pos != end.file.start_pos {
        return None;
    }
    let FileName::Real(name) = &start.file.name else {
        return None;
    };
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
        path: name.local_path()?.to_string_lossy().into_owned(),
        start_line: NonZeroU32::new(u32::try_from(start.line).ok()?)?,
        start_column: NonZeroU32::new(u32::try_from(start.col.0).ok()?.checked_add(1)?)?,
        end_line: NonZeroU32::new(u32::try_from(end.line).ok()?)?,
        end_column: NonZeroU32::new(u32::try_from(end.col.0).ok()?.checked_add(1)?)?,
        source_digest,
    })
}

pub fn function_context(tcx: TyCtxt<'_>, body: &Body<'_>) -> RCanaryFunction {
    let mut mir = String::new();
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
    RCanaryFunction {
        source: tcx.sess.source_map().span_to_snippet(body.span).ok(),
        mir,
    }
}

fn site(tcx: TyCtxt<'_>, bidx: usize, term: &Terminator<'_>) -> RCanarySite {
    RCanarySite {
        basic_block: bidx,
        location: source_location(tcx, term.source_info.span),
        mir: format!("{:?}", term.kind),
    }
}

pub fn finding(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    def_id: DefId,
    bidx: usize,
    sources: &[(usize, Terminator<'_>)],
    state: &IcxSliceFroBlock<'_, '_>,
    solver: &z3::Solver<'_>,
) -> RCanaryFinding {
    let locals = state
        .var()
        .iter()
        .enumerate()
        .filter_map(|(index, var)| {
            let mut taint: Vec<_> = state.taint()[index]
                .set()
                .iter()
                .map(|ty| format!("{ty:?}"))
                .collect();
            taint.sort();
            if var.is_declared() && taint.is_empty() {
                return None;
            }
            let bit_width = state.len()[index];
            Some(RCanaryLocal {
                local: index,
                name: get_variable_name(body, index),
                local_type: body.local_decls[Local::from_usize(index)].ty.to_string(),
                state: match var {
                    IntraVar::Declared => "declared",
                    IntraVar::Init(_) => "initialized",
                    IntraVar::Unsupported => "unsupported",
                }
                .into(),
                bit_width,
                ownership_bits: match var {
                    IntraVar::Init(bits) => Some(bits.to_string()),
                    _ => None,
                },
                layout: state.layout()[index]
                    .iter()
                    .map(|item| format!("{item:?}"))
                    .collect(),
                taint,
                checked_at_return: index > body.arg_count && bit_width > 0 && var.is_init(),
            })
        })
        .collect();
    RCanaryFinding {
        id: String::new(),
        function: tcx.def_path_str(def_id),
        bug_type: BugType::MemoryLeak,
        location: source_location(tcx, body.span),
        return_site: site(
            tcx,
            bidx,
            body.basic_blocks[BasicBlock::from_usize(bidx)].terminator(),
        ),
        source_sites: sources
            .iter()
            .map(|(bb, term)| site(tcx, *bb, term))
            .collect(),
        solver: SolverEvidence {
            result: "unsat".into(),
            constraints: solver.to_string(),
        },
        locals,
    }
}
