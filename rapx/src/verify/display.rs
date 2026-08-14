use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};
use rustc_middle::ty::ClauseKind;

use crate::compat::FxHashMap;
use crate::helpers::fn_info::get_cons;
use indexmap::IndexMap;

use crate::helpers::mir_scan::CheckpointLocation;
use super::report::PropertyCheckResult;
use crate::verify::contract::render::display_expr_user_friendly;

pub fn fmt_fn_with_params(path: &str, arg_names: &[String], ret_ty: Option<&str>) -> String {
    let args = arg_names.join(", ");
    match ret_ty {
        Some(ret) => format!("fn {path}({args}) -> {ret}"),
        None if args.is_empty() => format!("fn {path}"),
        None => format!("fn {path}({args})"),
    }
}

pub fn fmt_fn_path_with_generics(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
) -> String {
    let path = tcx.def_path_str(def_id);
    let generics = tcx.generics_of(def_id);
    let params: Vec<_> = generics
        .own_params
        .iter()
        .map(|p| p.name.to_string())
        .collect();
    if params.is_empty() {
        path
    } else {
        format!("{}::<{}>", path, params.join(", "))
    }
}

pub fn fmt_fn_path_with_bounds(
    tcx: TyCtxt<'_>,
    def_id: DefId,
) -> String {
    let path = tcx.def_path_str(def_id);
    let predicates = crate::compat::predicates_of(tcx, def_id);

    let mut param_bounds: FxHashMap<String, Vec<String>> = FxHashMap::default();

    macro_rules! collect_bounds {
        ($iter:expr) => {
            for (predicate, _span) in $iter {
                if let ClauseKind::Trait(trait_ref) = predicate.kind().skip_binder() {
                    let self_ty = trait_ref.self_ty();
                    if let ty::TyKind::Param(param_ty) = self_ty.kind() {
                        let param_name = param_ty.name.to_string();
                        let trait_name = tcx.item_name(trait_ref.def_id()).to_string();
                        if trait_name != "Sized" {
                            param_bounds.entry(param_name).or_default().push(trait_name);
                        }
                    }
                }
            }
        };
    }

    #[cfg(not(rapx_rustc_ge_199))]
    {
        collect_bounds!(predicates.predicates.iter());
        if let Some(parent_def_id) = predicates.parent {
            let parent_preds = crate::compat::predicates_of(tcx, parent_def_id);
            collect_bounds!(parent_preds.predicates.iter());
        }
    }
    #[cfg(rapx_rustc_ge_199)]
    {
        collect_bounds!(predicates.clauses.iter());
        if let Some(parent_def_id) = predicates.parent {
            let parent_preds = crate::compat::predicates_of(tcx, parent_def_id);
            collect_bounds!(parent_preds.clauses.iter());
        }
    }

    if param_bounds.is_empty() {
        return path;
    }

    insert_bounds_into_path(&path, &param_bounds)
}

fn insert_bounds_into_path(path: &str, param_bounds: &FxHashMap<String, Vec<String>>) -> String {
    let mut result = String::new();
    let mut remaining = path;

    while let Some(pos) = remaining.find("::<") {
        result.push_str(&remaining[..pos + 3]);
        remaining = &remaining[pos + 3..];

        let Some(end) = remaining.find('>') else {
            result.push_str(remaining);
            return result;
        };

        let params_str = &remaining[..end];
        let params: Vec<&str> = params_str.split(',').map(|s| s.trim()).collect();
        let mut new_params = Vec::new();
        let mut has_bounds = false;
        for p in &params {
            if let Some(bounds) = param_bounds.get(*p) {
                new_params.push(format!("{}: {}", p, bounds.join(" + ")));
                has_bounds = true;
            } else {
                new_params.push(p.to_string());
            }
        }

        if has_bounds {
            result.push_str(&new_params.join(", "));
        } else {
            result.push_str(params_str);
        }
        result.push('>');
        remaining = &remaining[end + 1..];
    }

    result.push_str(remaining);
    result
}

pub fn fmt_contract_expanded<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    property: &crate::verify::contract::Property<'tcx>,
    struct_def_id: Option<rustc_hir::def_id::DefId>,
    fn_def_id: Option<rustc_hir::def_id::DefId>,
) -> (String, String) {
    use crate::verify::contract::PropertyKind;
    if property.is_or() {
        let group_count = property.groups().len();
        let mut call_parts = Vec::new();
        let mut meaning = format!("any of {group_count} alternative group(s):\n");
        for (gi, group) in property.groups().iter().enumerate() {
            let is_last = gi + 1 == group_count;
            let branch = if is_last { "`-" } else { "|-" };
            let group_calls: Vec<String> = group
                .iter()
                .map(|prop| {
                    let (call, _) =
                        fmt_contract_expanded(tcx, prop, struct_def_id, fn_def_id);
                    call
                })
                .collect();
            call_parts.push(group_calls.join(" && "));
            let meanings: Vec<String> = group
                .iter()
                .map(|prop| {
                    let (_, m) =
                        fmt_contract_expanded(tcx, prop, struct_def_id, fn_def_id);
                    m
                })
                .collect();
            meaning.push_str(&format!("{branch} {}\n", meanings.join(" && ")));
        }
        return (
            format!("Or({})", call_parts.join(", ")),
            meaning.trim_end().to_string(),
        );
    }
    let kind = property.kind().expect("leaf property");
    let args: Vec<String> = property
        .args()
        .iter()
        .map(|a| a.display_for_report(tcx, struct_def_id, fn_def_id))
        .collect();
    let tag = property
        .origin_name()
        .map(String::from)
        .unwrap_or_else(|| format!("{:?}", kind));
    let tag = if property.contract_kind() == crate::verify::contract::ContractKind::Hazard {
        format!("[hazard] {tag}")
    } else if property.contract_kind() == crate::verify::contract::ContractKind::Option_ {
        format!("[option] {tag}")
    } else {
        tag
    };
    let call = if matches!(kind, PropertyKind::SplitTransmute) {
        let wrapped: Vec<String> = args.iter().map(|a| format!("[{a}]")).collect();
        format!("{tag}({})", wrapped.join(", "))
    } else if matches!(kind, PropertyKind::InBound)
        && matches!(
            property.args().first(),
            Some(crate::verify::contract::PropertyArg::Expr(
                crate::verify::contract::ContractExpr::IndexAccess { .. }
            ))
        )
    {
        use crate::verify::contract::{ContractExpr, PropertyArg};
        if let Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, index })) =
            property.args().first()
        {
            let mut s = display_expr_user_friendly(slice, tcx, struct_def_id, fn_def_id);
            s = s.strip_prefix("&mut ").unwrap_or(&s).to_string();
            s = s.strip_prefix("&").unwrap_or(&s).to_string();
            let i = display_expr_user_friendly(index, tcx, struct_def_id, fn_def_id);
            format!("{tag}({s}, {i})")
        } else {
            unreachable!()
        }
    } else {
        if matches!(kind, PropertyKind::Alive) && args.len() >= 2 {
            format!("{tag}({}, '{})", args[0], args[1])
        } else {
            format!("{tag}({})", args.join(", "))
        }
    };
    let call = if matches!(kind, PropertyKind::ValidNum)
        && let Some(crate::verify::contract::PropertyArg::Predicates(preds)) = property.args().first()
    {
        let inner = preds
            .iter()
            .map(|p| p.display_user_friendly(tcx, struct_def_id, fn_def_id))
            .collect::<Vec<_>>()
            .join(", ");
        format!("{tag}({inner})")
    } else {
        call
    };
    let meaning = match kind {
        PropertyKind::NonNull => format!(
            "{} as usize != 0",
            args.first().map(|s| s.as_str()).unwrap_or("_")
        ),
        PropertyKind::Align => {
            let ptr = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            let ty = args.get(1).map(|s| s.as_str()).unwrap_or("T");
            format!("({ptr} as usize) % align_of::<{ty}>() == 0")
        }
        PropertyKind::InBound => {
            use crate::verify::contract::{ContractExpr, PropertyArg};
            let placeholder = format!("InBound({})", args.join(", "));
            match property.args().first() {
                Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, index })) => {
                    let mut s = display_expr_user_friendly(slice, tcx, struct_def_id, fn_def_id);
                    s = s.strip_prefix("&mut ").unwrap_or(&s).to_string();
                    s = s.strip_prefix("&").unwrap_or(&s).to_string();
                    let i = display_expr_user_friendly(index, tcx, struct_def_id, fn_def_id);
                    format!("0 <= {i} < {s}.len()")
                }
                Some(PropertyArg::Expr(ContractExpr::Place(place))) => {
                    let ptr = place.display_user_friendly(tcx, struct_def_id, fn_def_id);
                    let ty = property
                        .args()
                        .get(1)
                        .and_then(|a| match a {
                            PropertyArg::Ty(ty) => Some(ty.to_string()),
                            _ => None,
                        })
                        .unwrap_or_else(|| "?".to_string());
                    let cnt = property
                        .args()
                        .get(2)
                        .map(|a| a.display_for_report(tcx, struct_def_id, fn_def_id))
                        .unwrap_or_else(|| "?".to_string());
                    format!("same_alloc([{ptr}, {ptr} + sizeof({ty})*{cnt}])")
                }
                _ => placeholder,
            }
        }
        PropertyKind::Init => {
            let p = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            let ty = args.get(1).map(|s| s.as_str()).unwrap_or("T");
            let cnt = args.get(2).map(|s| s.as_str()).unwrap_or("count");
            format!(
                "forall i in 0..{cnt}: *({p} + i*sizeof({ty})) |= type_invariant({ty}), and the {cnt} value(s) are initialized"
            )
        }
        PropertyKind::Typed => {
            let ptr = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            let ty = args.get(1).map(|s| s.as_str()).unwrap_or("T");
            format!("*{ptr} holds TypeInvariant({ty})")
        }
        PropertyKind::Alive => {
            let ptr = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            if let Some(lt) = args.get(1) {
                format!("*{ptr} outlives '{lt}")
            } else {
                format!("*{ptr} outlives return")
            }
        }
        PropertyKind::Alias => {
            let p1 = args.first().map(|s| s.as_str()).unwrap_or("p1");
            let p2 = args.get(1).map(|s| s.as_str()).unwrap_or("p2");
            format!("{p1} and {p2} alias each other (hazard)")
        }
        PropertyKind::Allocated => {
            let ptr = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            let suffix = if args.len() >= 3 {
                format!(", {}, {}", args[1], args[2])
            } else {
                String::new()
            };
            format!("{ptr} points to live heap/stack allocation{suffix}")
        }
        PropertyKind::NonOverlap => {
            let joined = args.join(", ");
            format!("[{joined}] are pairwise disjoint memory ranges")
        }
        PropertyKind::ValidNum => args.join(" && "),
        PropertyKind::ValidTransmute => {
            let src = args.first().map(|s| s.as_str()).unwrap_or("Src");
            let dst = args.get(1).map(|s| s.as_str()).unwrap_or("Dst");
            format!("bytes_of({dst}) within bytes_of({src})")
        }
        PropertyKind::SplitTransmute => {
            let src = args.first().map(|s| s.as_str()).unwrap_or("T");
            let dst = args.get(1).map(|s| s.as_str()).unwrap_or("U");
            let line1 = format!(
                "[{src}] as [{dst}]: every size_of({dst})-byte contiguous chunk of [{src}] is a valid bit-pattern of {dst} (type_invariant satisfied, alignment not required)"
            );
            let line2 = format!(
                "forall w subset bytes([{src}]), |w| == |{dst}|: reinterpret_as_{dst}(w) |= type_invariant({dst}) \\ align_of({dst})",
            );
            format!("{line1}\n{line2}")
        }
        PropertyKind::Owning => {
            let ptr = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            format!("ownership(*{ptr}) = none: no live owner aliases the pointee")
        }
        PropertyKind::Size => {
            let ty = args.first().map(|s| s.as_str()).unwrap_or("T");
            let sz = args.get(1).map(|s| s.as_str()).unwrap_or("1");
            match sz {
                "sized" => format!("{ty} is Sized (non-ZST)"),
                "unsized" => format!("{ty} is !Sized"),
                n => format!("sizeof({ty}) = {n}"),
            }
        }
        PropertyKind::NoPadding => {
            let t = args.first().map(|s| s.as_str()).unwrap_or("T");
            format!("{t} has no padding bytes between fields")
        }
        PropertyKind::Unwrap => {
            let x = args.first().map(|s| s.as_str()).unwrap_or("x");
            let v = args.get(1).map(|s| s.as_str()).unwrap_or("T");
            format!("unwrap({x}) = {v}")
        }
        PropertyKind::ValidString => {
            let v = args.first().map(|s| s.as_str()).unwrap_or("v");
            format!("{v} is valid UTF-8")
        }
        PropertyKind::ValidCStr => {
            let p = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            format!("{p} is a null-terminated valid UTF-8 byte sequence")
        }
        PropertyKind::Pinned => {
            let p = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            format!("{p} will not be moved")
        }
        PropertyKind::NonVolatile => {
            let p = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            format!("{p} does not reference volatile memory")
        }
        PropertyKind::Opened => {
            let f = args.first().map(|s| s.as_str()).unwrap_or("fd");
            format!("{f} is a valid open file descriptor")
        }
        PropertyKind::Trait => {
            let t = args.first().map(|s| s.as_str()).unwrap_or("T");
            let tr = args.get(1).map(|s| s.as_str()).unwrap_or("Trait");
            format!("{t} satisfies the trait bound {tr}")
        }
        PropertyKind::Unreachable => "not Reachable()".to_string(),
        PropertyKind::Unknown => "(unresolved contract)".to_string(),
    };
    (call, meaning)
}

pub fn emit_results_counts_and_checkpoints<'tcx>(
    tcx: TyCtxt<'tcx>,
    all_results: &[PropertyCheckResult<'tcx>],
) -> (usize, usize) {

    use crate::verify::contract::ContractKind;
    use super::report::CheckResult;

    let unproved = all_results
        .iter()
        .filter(|r| {
            r.property.contract_kind() != ContractKind::Hazard
                && r.property.contract_kind() != ContractKind::Option_
                && !matches!(r.result, CheckResult::Proved)
        })
        .count();
    let hazard_failed = all_results
        .iter()
        .filter(|r| {
            r.property.contract_kind() == ContractKind::Hazard
                && !matches!(r.result, CheckResult::Proved)
        })
        .count();

    let mut groups: IndexMap<(CheckpointLocation, String), Vec<&PropertyCheckResult<'_>>> =
        IndexMap::new();
    for r in all_results {
        groups
            .entry((r.checkpoint, r.callee_name.clone()))
            .or_default()
            .push(r);
    }

    let checkpoint_groups: Vec<_> = groups
        .iter()
        .filter(|((_, name), _)| !name.starts_with("struct-invariant"))
        .collect();
    let invariant_groups: Vec<_> = groups
        .iter()
        .filter(|((_, name), _)| name.starts_with("struct-invariant"))
        .collect();

    if !checkpoint_groups.is_empty() {
        rap_info!("  --- unsafe checkpoints ---");
        for ((checkpoint, callee_name), results) in &checkpoint_groups {
            rap_info!(
                "      unsafe checkpoint: bb{} -> {callee_name}",
                checkpoint.block.as_usize(),
            );
            emit_property_rows(tcx, results);
        }
    }

    if !invariant_groups.is_empty() {
        rap_info!("  --- struct invariants ---");
        for ((checkpoint, _), results) in &invariant_groups {
            rap_info!("      checkpoint bb{}:", checkpoint.block.as_usize());
            emit_property_rows(tcx, results);
        }
    }

    (unproved, hazard_failed)
}

pub fn emit_verify_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    target_path: &str,
    def_id: rustc_hir::def_id::DefId,
    all_results: &[PropertyCheckResult<'tcx>],
    skip_invariant: bool,
) {
    rap_info!("============================================================");
    rap_info!("[rapx::verify] function: {target_path}");
    rap_info!("============================================================");

    if skip_invariant {
        let cons = get_cons(tcx, def_id);
        for con in &cons {
            rap_info!("  + constructor: {}", tcx.def_path_str(*con));
        }
    }

    emit_results_and_verdict(tcx, all_results);
    rap_info!("");
}

pub fn emit_results_and_verdict<'tcx>(
    tcx: TyCtxt<'tcx>,
    all_results: &[PropertyCheckResult<'tcx>],
) {
    let (unproved, hazard_failed) = emit_results_counts_and_checkpoints(tcx, all_results);

    if unproved == 0 && hazard_failed == 0 {
        rap_info!(green, "  result: SOUND");
    } else {
        rap_warn!("  result: UNSOUND ({unproved} unproved, {hazard_failed} hazard)");
    }
}



pub fn emit_property_rows<'tcx>(
    _tcx: TyCtxt<'tcx>,
    results: &[&PropertyCheckResult<'tcx>],
) {
    let path_groups: Vec<(&str, Vec<_>)> = {
        let mut map: FxHashMap<&str, Vec<_>> = FxHashMap::default();
        for r in results.iter() {
            map.entry(r.path_description.as_str())
                .or_default()
                .push(r);
        }
        let mut entries: Vec<_> = map.into_iter().collect();
        entries.sort_by_key(|(desc, _)| desc.matches(',').count());
        entries
    };
    for (path_desc, props) in &path_groups {
        rap_info!("        path {path_desc}:");
        // Count identical (kind, origin, hazard, result) groups for dedup.
        let mut counts: Vec<(
            Option<crate::verify::contract::PropertyKind>,
            Option<String>,
            bool,
            bool,
            super::report::CheckResult,
            usize,
        )> = Vec::new();
        for r in props.iter() {
            let is_hazard =
                r.property.contract_kind() == crate::verify::contract::ContractKind::Hazard;
            let is_option =
                r.property.contract_kind() == crate::verify::contract::ContractKind::Option_;
            let origin = r.property.origin_name().map(String::from);
            let result = r.result.clone();
            if let Some(entry) = counts.iter_mut().find(|(k, on, h, o, res, _)| {
                *k == r.property.kind()
                    && *on == origin
                    && *h == is_hazard
                    && *o == is_option
                    && *res == result
            }) {
                entry.5 += 1;
            } else {
                counts.push((
                    r.property.kind(),
                    origin,
                    is_hazard,
                    is_option,
                    result,
                    1usize,
                ));
            }
        }
        let n = counts.len();
        for (i, (kind, origin, is_hazard, is_option, result, count)) in counts.iter().enumerate() {
            let is_last = i + 1 == n;
            let conn = if n > 1 {
                if is_last { "└── " } else { "├── " }
            } else {
                ""
            };
            let name = origin.clone().unwrap_or_else(|| match kind {
                Some(k) => format!("{k:?}"),
                None => "Or".to_string(),
            });
            let tag = if *is_hazard {
                format!("[hazard] {name}")
            } else if *is_option {
                format!("[option] {name}")
            } else {
                name
            };
            let mut line = format!("          {conn}{tag} | {:?}", result);
            if *count > 1 {
                line.push_str(&format!(" (x{count})"));
            }
            if matches!(result, super::report::CheckResult::Proved) {
                rap_info!(green, "{line}");
            } else {
                rap_warn!("{line}");
            }
        }
    }
}
