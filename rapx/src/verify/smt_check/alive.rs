//! Lifetime anchoring checks for the `Alive` safety property.
//!
//! `Alive` is different from numeric SPs: `from_raw_parts(_mut)` does not only
//! require a valid address at the callsite, it also asks the returned view's
//! lifetime to be anchored to a source that really owns or borrows the memory.
//! This first checker intentionally focuses on common safe-wrapper shapes:
//!
//! - elided returns tied to `&self` / `&mut self`;
//! - explicit returns tied to a real host parameter used to produce the pointer;
//! - obvious lifetime widening, unrelated host, and `'static` escapes.

use std::collections::HashSet;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Local, StatementKind},
    ty::{self, TyCtxt},
};

use crate::{
    helpers::name::parse_signature,
    verify::{
        call_summary::CallEffect,
        contract::{PlaceBase, Property, PropertyArg, PropertyKind},
        def_use::PlaceKey,
        helpers::Checkpoint,
        verifier::{AbstractValue, CallSummary, ForwardVisitResult, StateFact},
    },
};

use super::common::{
    SmtCheckResult, SmtChecker, call_destination, failed_smt, rvalue_source_place,
};
use crate::verify::report::CheckResult;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AliveProducer {
    SharedSlice,
    UniqueSlice,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ReturnLifetime {
    Elided,
    Named(String),
    Static,
    Unknown,
}

#[derive(Clone, Debug)]
struct SignatureInfo {
    text: String,
    return_lifetime: ReturnLifetime,
    has_ref_self: bool,
    has_mut_self: bool,
    consumes_self: bool,
}

/// Checks whether an `Alive` obligation has a lifetime anchor for the returned view.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(destination) = call_destination(checker.tcx, checkpoint) else {
        return SmtCheckResult::unknown("Alive producer destination could not be resolved");
    };
    let Some(producer) =
        alive_producer_from_destination(checker.tcx, checkpoint.caller, destination)
    else {
        return SmtCheckResult::unknown(
            "Alive lowering currently supports borrowed view producers",
        );
    };
    if !destination_flows_to_return(checker.tcx, checkpoint.caller, destination) {
        return SmtCheckResult::proved(
            "Alive view is local; no escaped returned lifetime must be anchored",
        );
    }

    let Some(signature) = SignatureInfo::from_def_id(checker.tcx, checkpoint.caller) else {
        return SmtCheckResult::unknown("Alive caller signature could not be recovered");
    };
    let target = checker
        .property_target(checkpoint, property)
        .or_else(|| checker.callsite_arg_place(checkpoint, 0));
    let pointer_origin_param = target.as_ref().and_then(|place| {
        pointer_origin_param_local(checker.tcx, checkpoint.caller, place, forward)
    });

    match &signature.return_lifetime {
        ReturnLifetime::Elided => {
            let result = check_elided_return(producer, &signature);
            if result.result == CheckResult::Unknown {
                if let Some(origin) = pointer_origin_param {
                    if let Some(fallback) =
                        check_elided_param_ref(checker.tcx, checkpoint.caller, origin, producer)
                    {
                        return fallback;
                    }
                }
            }
            result
        }
        ReturnLifetime::Static => failed_smt("Alive failed: returned slice is widened to 'static"),
        ReturnLifetime::Named(lifetime) => {
            let contract_lifetime = property.args.get(1).and_then(|a| match a {
                PropertyArg::Ident(id) => Some(id.as_str()),
                _ => None,
            });
            if let Some(cl) = contract_lifetime {
                if !lifetime.contains(cl) && !lifetime.contains(&format!("'{cl}")) {
                    return failed_smt(format!(
                        "Alive failed: contract declares lifetime '{cl} but return uses '{lifetime}"
                    ));
                }
            }
            check_named_return(
                checker.tcx,
                checkpoint.caller,
                producer,
                &signature,
                lifetime,
                pointer_origin_param,
            )
        }
        ReturnLifetime::Unknown => {
            SmtCheckResult::unknown("Alive return lifetime shape is not supported yet")
        }
    }
}

/// Checks whether an elided return lifetime can be tied to the receiver borrow.
fn check_elided_return(producer: AliveProducer, signature: &SignatureInfo) -> SmtCheckResult {
    if signature.has_mut_self && producer == AliveProducer::UniqueSlice {
        return SmtCheckResult::proved(
            "Alive proved: returned mutable slice is tied to the current &mut self borrow",
        );
    }
    if signature.has_ref_self && producer == AliveProducer::SharedSlice {
        return SmtCheckResult::proved(
            "Alive proved: returned shared slice is tied to the current &self borrow",
        );
    }
    if signature.has_ref_self && producer == AliveProducer::UniqueSlice {
        return failed_smt("Alive failed: mutable slice is tied only to a shared self borrow");
    }
    SmtCheckResult::unknown("Alive elided lifetime is not tied to a supported receiver")
}

/// Fallback check: when the elided return check fails (no &self/&mut self),
/// try matching the pointer origin against a non-self reference parameter.
fn check_elided_param_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    origin: usize,
    producer: AliveProducer,
) -> Option<SmtCheckResult> {
    let body = tcx.optimized_mir(caller);
    if origin > body.arg_count {
        return None;
    }
    let ty = body.local_decls[Local::from_usize(origin)].ty;
    match ty.kind() {
        ty::Ref(_, _, ty::Mutability::Mut) => {
            if producer == AliveProducer::UniqueSlice {
                Some(SmtCheckResult::proved(
                    "Alive proved: returned mutable slice is tied to the &mut param borrow",
                ))
            } else {
                Some(SmtCheckResult::proved(
                    "Alive proved: shared slice is tied to a &mut param borrow; Alias will catch the mutability mismatch",
                ))
            }
        }
        ty::Ref(_, _, ty::Mutability::Not) => {
            if producer == AliveProducer::SharedSlice {
                Some(SmtCheckResult::proved(
                    "Alive proved: returned shared slice is tied to the & param borrow",
                ))
            } else if producer == AliveProducer::UniqueSlice {
                Some(SmtCheckResult::proved(
                    "Alive proved: returned mutable slice is tied to a shared & param borrow; Alias will catch the mutability mismatch",
                ))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Checks whether the caller has an `Alive(param, lifetime)` contract that
/// covers the pointer origin parameter. Used for raw pointer parameters that
/// cannot carry lifetime information in their Rust type.
fn caller_alive_contract_covers(
    tcx: TyCtxt<'_>,
    caller: DefId,
    origin_param: usize,
    lifetime: &str,
) -> bool {
    let contracts = crate::verify::target::get_contract_from_annotation(tcx, caller);
    contracts.iter().any(|prop| {
        if prop.kind != PropertyKind::Alive {
            return false;
        }
        let contract_lifetime = prop.args.get(1).and_then(|a| match a {
            PropertyArg::Ident(id) => Some(id.as_str()),
            _ => None,
        });
        if contract_lifetime != Some(lifetime) {
            return false;
        }
        matches!(prop.args.first(), Some(PropertyArg::Place(place))
            if place.base == PlaceBase::Local(origin_param) && place.projections.is_empty())
    })
}

/// Checks whether an explicit return lifetime is tied to the pointer source.
fn check_named_return<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    producer: AliveProducer,
    signature: &SignatureInfo,
    lifetime: &str,
    pointer_origin_param: Option<usize>,
) -> SmtCheckResult {
    let source_params = params_with_lifetime(tcx, caller, signature, lifetime);

    if let Some(origin) = pointer_origin_param {
        if source_params.contains(&origin) {
            return SmtCheckResult::proved(format!(
                "Alive proved: returned lifetime '{lifetime} is tied to the source parameter that produced the pointer"
            ));
        }
        if !source_params.is_empty() {
            return failed_smt(format!(
                "Alive failed: returned lifetime '{lifetime} is tied to a host parameter, but the pointer comes from another source"
            ));
        }
    }

    if producer == AliveProducer::UniqueSlice
        && signature.has_ref_self
        && !signature.consumes_self
        && source_params.is_empty()
    {
        return failed_smt(format!(
            "Alive failed: returned mutable slice uses lifetime '{lifetime}, but that lifetime is not tied to this &mut self borrow"
        ));
    }

    if source_params.is_empty() {
        if let Some(origin) = pointer_origin_param
            && caller_alive_contract_covers(tcx, caller, origin, lifetime)
        {
            return SmtCheckResult::proved(format!(
                "Alive proved: caller Alive contract covers raw pointer origin for lifetime '{lifetime}"
            ));
        }
        return failed_smt(format!(
            "Alive failed: returned lifetime '{lifetime} has no proven source parameter"
        ));
    }

    SmtCheckResult::unknown(format!(
        "Alive could not prove that the pointer is produced from lifetime '{lifetime}"
    ))
}

/// Classifies the borrowed view returned by the Alive-producing call destination.
fn alive_producer_from_destination<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    destination: Local,
) -> Option<AliveProducer> {
    let body = tcx.optimized_mir(caller);
    let ty = body.local_decls[destination].ty;
    match ty.kind() {
        ty::Ref(_, _, ty::Mutability::Mut) => Some(AliveProducer::UniqueSlice),
        ty::Ref(_, _, ty::Mutability::Not) => Some(AliveProducer::SharedSlice),
        _ => None,
    }
}

impl SignatureInfo {
    /// Recovers the caller signature metadata needed for lifetime anchoring.
    fn from_def_id(tcx: TyCtxt<'_>, def_id: DefId) -> Option<Self> {
        let text = function_signature_text(tcx, def_id)?;
        let params = params_segment(&text).unwrap_or_default();
        Some(Self {
            return_lifetime: return_lifetime(&text),
            has_mut_self: params.contains("&mut self")
                || params.contains("&'") && params.contains("mut self"),
            has_ref_self: params.contains("&self")
                || params.contains("&mut self")
                || params.contains("&'") && params.contains("self"),
            consumes_self: params
                .split(',')
                .next()
                .is_some_and(|first| first.trim() == "self"),
            text,
        })
    }
}

/// Extracts a compact source-level function signature from the HIR span.
fn function_signature_text(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
    let local = def_id.as_local()?;
    let hir_id = tcx.local_def_id_to_hir_id(local);
    let span = tcx.hir_span(hir_id);
    let snippet = tcx.sess.source_map().span_to_snippet(span).ok()?;
    let start = snippet.find("fn ")?;
    let rest = &snippet[start..];
    let end = rest.find('{').unwrap_or(rest.len());
    Some(rest[..end].split_whitespace().collect::<Vec<_>>().join(" "))
}

/// Extracts the comma-separated parameter segment from a compact signature.
fn params_segment(signature: &str) -> Option<String> {
    let start = signature.find('(')?;
    let end = signature[start + 1..].find(')')? + start + 1;
    Some(signature[start + 1..end].to_string())
}

/// Parses the return lifetime shape from a compact signature.
fn return_lifetime(signature: &str) -> ReturnLifetime {
    let Some((_, ret)) = signature.split_once("->") else {
        return ReturnLifetime::Unknown;
    };
    let ret = ret
        .split("where")
        .next()
        .unwrap_or(ret)
        .trim()
        .trim_end_matches(';')
        .trim()
        .replace("& '", "&'");
    if ret.starts_with("&'static") {
        return ReturnLifetime::Static;
    }
    if let Some(rest) = ret.strip_prefix("&'") {
        let lifetime = rest
            .chars()
            .take_while(|ch| ch.is_ascii_alphanumeric() || *ch == '_')
            .collect::<String>();
        if !lifetime.is_empty() {
            return ReturnLifetime::Named(lifetime);
        }
    }
    if ret.starts_with('&') {
        return ReturnLifetime::Elided;
    }
    ReturnLifetime::Unknown
}

/// Finds MIR argument locals whose source signature type carries the target lifetime.
fn params_with_lifetime(
    tcx: TyCtxt<'_>,
    caller: DefId,
    signature: &SignatureInfo,
    lifetime: &str,
) -> HashSet<usize> {
    let (names, _) = parse_signature(tcx, caller);
    names
        .iter()
        .enumerate()
        .filter_map(|(index, name)| {
            if name.is_empty() {
                return None;
            }
            let pattern = format!("{name}: &'{lifetime}");
            let text = signature.text.replace("& '", "&'");
            text.contains(&pattern).then_some(index + 1)
        })
        .collect()
}

/// Checks whether the call destination may escape through the function return.
fn destination_flows_to_return<'tcx>(tcx: TyCtxt<'tcx>, caller: DefId, destination: Local) -> bool {
    if destination.as_usize() == 0 {
        return true;
    }
    let body = tcx.optimized_mir(caller);
    if body.local_decls[Local::from_usize(0)].ty == body.local_decls[destination].ty {
        return true;
    }
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = &**assign;
            if target.local.as_usize() != 0 {
                continue;
            }
            if rvalue_source_place(rvalue).is_some_and(|p| p.local == destination) {
                return true;
            }
        }
    }
    false
}

/// Finds the caller argument local that originally produced a pointer place.
fn pointer_origin_param_local<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    place: &PlaceKey,
    forward: &ForwardVisitResult<'tcx>,
) -> Option<usize> {
    let mut seen = HashSet::new();
    pointer_origin_param_local_inner(tcx, caller, place, forward, &mut seen)
}

/// Recursively follows local values and call summaries to recover pointer provenance.
fn pointer_origin_param_local_inner<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    place: &PlaceKey,
    forward: &ForwardVisitResult<'tcx>,
    seen: &mut HashSet<PlaceKey>,
) -> Option<usize> {
    if !seen.insert(place.clone()) {
        return None;
    }
    if let Some(local) = place.local() {
        let body = tcx.optimized_mir(caller);
        if (1..=body.arg_count).contains(&local.as_usize()) {
            return Some(local.as_usize());
        }

        if let Some(call) = call_result_for_local(forward, local) {
            return call_pointer_origin_param(tcx, caller, call, forward, seen);
        }

        if let Some(value) = forward.values.get(&local) {
            return value_pointer_origin_param(tcx, caller, value, forward, seen);
        }
    }
    None
}

/// Finds the retained call summary that produced a given local.
fn call_result_for_local<'a, 'tcx>(
    forward: &'a ForwardVisitResult<'tcx>,
    local: Local,
) -> Option<&'a CallSummary<'tcx>> {
    forward.facts.iter().find_map(|fact| {
        let StateFact::Call(call) = fact else {
            return None;
        };
        (call.destination == local).then_some(call)
    })
}

/// Recovers pointer provenance from interprocedural call effects.
fn call_pointer_origin_param<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    call: &CallSummary<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
    seen: &mut HashSet<PlaceKey>,
) -> Option<usize> {
    for effect in &call.effects {
        match effect {
            CallEffect::ReturnPointerFromArg { arg } | CallEffect::ReturnAliasArg { arg } => {
                let value = call.args.get(*arg)?;
                return value_pointer_origin_param(tcx, caller, value, forward, seen);
            }
            CallEffect::ReturnPointerAdd { base_arg, .. }
            | CallEffect::ReturnPointerSub { base_arg, .. } => {
                let value = call.args.get(*base_arg)?;
                return value_pointer_origin_param(tcx, caller, value, forward, seen);
            }
            _ => {}
        }
    }
    None
}

/// Recovers pointer provenance from an abstract value.
fn value_pointer_origin_param<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    value: &AbstractValue<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
    seen: &mut HashSet<PlaceKey>,
) -> Option<usize> {
    match value {
        AbstractValue::Place(place) | AbstractValue::Ref(place) | AbstractValue::RawPtr(place) => {
            pointer_origin_param_local_inner(tcx, caller, place, forward, seen)
        }
        AbstractValue::Cast(inner, _) => {
            value_pointer_origin_param(tcx, caller, inner, forward, seen)
        }
        AbstractValue::CallResult(call) => {
            call_pointer_origin_param(tcx, caller, call, forward, seen)
        }
        _ => None,
    }
}
