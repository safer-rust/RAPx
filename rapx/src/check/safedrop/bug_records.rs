use annotate_snippets::{Level, Renderer, Snippet};
use rustc_data_structures::fx::FxHashMap;
use rustc_span::{Span, symbol::Symbol};

use crate::utils::log::{
    are_spans_in_same_file, get_basic_block_span, get_variable_name, relative_pos_range,
    span_to_filename, span_to_line_number, span_to_source_code,
};
use rustc_middle::mir::{Body, HasLocalDecls, Local};

use super::drop::LocalSpot;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BugType {
    UseAfterFree,
    DoubleFree,
    DanglingPointer,
    UseAfterFreeAndDoubleFree,
}

#[derive(Debug)]
pub struct TyBug {
    pub drop_spot: LocalSpot,
    pub trigger_info: LocalSpot,
    pub prop_chain: Vec<usize>,
    pub span: Span,
    pub confidence: usize,
    pub bug_type: BugType,
}

/*
 * For each bug in the HashMap, the key is local of the value.
 */
#[derive(Debug)]
pub struct BugRecords {
    pub df_bugs: FxHashMap<usize, TyBug>,
    pub df_bugs_unwind: FxHashMap<usize, TyBug>,
    pub uaf_bugs: FxHashMap<usize, TyBug>,
    pub dp_bugs: FxHashMap<usize, TyBug>,
    pub dp_bugs_unwind: FxHashMap<usize, TyBug>,
}

impl BugRecords {
    pub fn new() -> BugRecords {
        BugRecords {
            df_bugs: FxHashMap::default(),
            df_bugs_unwind: FxHashMap::default(),
            uaf_bugs: FxHashMap::default(),
            dp_bugs: FxHashMap::default(),
            dp_bugs_unwind: FxHashMap::default(),
        }
    }

    /// Returns `Some(bug_type)` if the caller should insert the bug with the returned type.
    /// Returns `None` if the bug should be skipped (already covered by an existing entry).
    /// When both UAF and DF exist for the same pair, DF wins as the survivor.
    pub fn try_merge_pair(&mut self, drop_spot: LocalSpot, trigger_bb: usize, in_type: BugType) -> Option<BugType> {
        let pair_match = |bug: &TyBug| bug.drop_spot == drop_spot && bug.trigger_info.bb == Some(trigger_bb);
        if in_type == BugType::UseAfterFree {
            for bug in self.df_bugs.values_mut() {
                if pair_match(bug) { bug.bug_type = BugType::UseAfterFreeAndDoubleFree; return None; }
            }
            for bug in self.df_bugs_unwind.values_mut() {
                if pair_match(bug) { bug.bug_type = BugType::UseAfterFreeAndDoubleFree; return None; }
            }
        } else {
            let uaf_keys: Vec<usize> = self.uaf_bugs.iter()
                .filter(|(_, bug)| pair_match(bug))
                .map(|(k, _)| *k)
                .collect();
            if !uaf_keys.is_empty() {
                for k in &uaf_keys {
                    self.uaf_bugs.remove(k);
                }
                return Some(BugType::UseAfterFreeAndDoubleFree);
            }
        }
        let check = |bugs: &FxHashMap<usize, TyBug>| -> bool {
            bugs.values().any(pair_match)
        };
        if check(&self.uaf_bugs) || check(&self.df_bugs) || check(&self.df_bugs_unwind) {
            return None;
        }
        Some(in_type)
    }

    pub fn is_bug_free(&self) -> bool {
        self.df_bugs.is_empty()
            && self.df_bugs_unwind.is_empty()
            && self.uaf_bugs.is_empty()
            && self.dp_bugs.is_empty()
            && self.dp_bugs_unwind.is_empty()
    }

    pub fn df_bugs_output<'tcx>(&self, body: &Body<'tcx>, fn_name: Symbol, span: Span) {
        self.emit_bug_reports(
            body, &self.df_bugs, fn_name, span,
            "Double free detected",
            "Double free detected.",
            df_uaf_detail,
        );

        self.emit_bug_reports(
            body, &self.df_bugs_unwind, fn_name, span,
            "Double free detected",
            "Double free detected during unwinding.",
            df_uaf_detail,
        );
    }

    pub fn uaf_bugs_output<'tcx>(&self, body: &Body<'tcx>, fn_name: Symbol, span: Span) {
        self.emit_bug_reports(
            body, &self.uaf_bugs, fn_name, span,
            "Use-after-free detected",
            "Use-after-free detected.",
            df_uaf_detail,
        );
    }

    pub fn dp_bug_output<'tcx>(&self, body: &Body<'tcx>, fn_name: Symbol, span: Span) {
        self.emit_bug_reports(
            body, &self.dp_bugs, fn_name, span,
            "Dangling pointer detected",
            "Dangling pointer detected.",
            dp_detail,
        );

        self.emit_bug_reports(
            body, &self.dp_bugs_unwind, fn_name, span,
            "Dangling pointer detected during unwinding",
            "Dangling pointer detected during unwinding.",
            dp_detail,
        );
    }

    fn emit_bug_reports<'tcx, F>(
        &self,
        body: &Body<'tcx>,
        bugs: &FxHashMap<usize, TyBug>,
        fn_name: Symbol,
        span: Span,
        log_msg: &str,
        title: &str,
        detail_formatter: F,
    ) where
        F: Fn(&TyBug, &str, &str, &str, &str) -> String,
    {
        if bugs.is_empty() {
            return;
        }

        rap_warn!("{} in function {:?}", log_msg, fn_name);

        let code_source = span_to_source_code(span);
        let filename = span_to_filename(span);
        let renderer = Renderer::styled();

        for bug in bugs.values() {
            if are_spans_in_same_file(span, bug.span) {
                let format_local_info = |id: usize| -> String {
                    if id >= body.local_decls().len() {
                        return format!("UNKNWON(_{}) in {}", id, fn_name.as_str());
                    }
                    let local = Local::from_usize(id);
                    let name_opt = get_variable_name(body, id);
                    let decl_span = body.local_decls[local].source_info.span;
                    let location = format!(
                        "{}:{}",
                        span_to_filename(decl_span),
                        span_to_line_number(decl_span)
                    );
                    match name_opt {
                        Some(name) => format!("_{}({}, {})", id, name, location),
                        None => format!("_{}(_, {})", id, location),
                    }
                };

                let format_bb_info = |bb_id: usize| -> String {
                    let bb_span = get_basic_block_span(body, bb_id);
                    let location = format!(
                        "{}:{}",
                        span_to_filename(bb_span),
                        span_to_line_number(bb_span)
                    );
                    format!("BB{}({})", bb_id, location)
                };

                let drop_bb = if let Some(bb) = bug.drop_spot.bb {
                    format_bb_info(bb)
                } else {
                    String::from("NA")
                };
                let drop_local = if let Some(local) = bug.drop_spot.local {
                    format_local_info(local)
                } else {
                    String::from("NA")
                };
                let trigger_bb = if let Some(bb) = bug.trigger_info.bb {
                    format_bb_info(bb)
                } else {
                    String::from("NA")
                };
                let trigger_local = if let Some(local) = bug.trigger_info.local {
                    format_local_info(local)
                } else {
                    String::from("NA")
                };

                let detail =
                    detail_formatter(bug, &drop_local, &trigger_local, &drop_bb, &trigger_bb);

                let mut snippet = Snippet::source(&code_source)
                    .line_start(span_to_line_number(span))
                    .origin(&filename)
                    .fold(false);

                snippet = snippet.annotation(
                    Level::Warning
                        .span(relative_pos_range(span, bug.span))
                        .label(&detail),
                );

                let message = Level::Warning.title(title).snippet(snippet);

                println!("{}", renderer.render(message));
            }
        }
    }
}

fn df_uaf_detail(
    bug: &TyBug,
    drop_local: &str,
    trigger_local: &str,
    drop_bb: &str,
    trigger_bb: &str,
) -> String {
    let line = format!("{} line {}.", span_to_filename(bug.span), span_to_line_number(bug.span));
    match bug.bug_type {
        BugType::UseAfterFreeAndDoubleFree => format!(
            "Double free / Use-after-free (confidence {}%): Location in file {}\n    | MIR detail: Value {} and {} are alias.\n    | MIR detail: {} is dropped at {}; {} is dropped at {}.",
            bug.confidence, line, drop_local, trigger_local, drop_local, drop_bb, trigger_local, trigger_bb
        ),
        BugType::UseAfterFree => format!(
            "Use-after-free (confidence {}%): Location in file {}\n    | MIR detail: Value {} and {} are alias.\n    | MIR detail: {} is dropped at {}; {} is used at {}.",
            bug.confidence, line, drop_local, trigger_local, drop_local, drop_bb, trigger_local, trigger_bb
        ),
        _ => format!(
            "Double free (confidence {}%): Location in file {}\n    | MIR detail: Value {} and {} are alias.\n    | MIR detail: {} is dropped at {}; {} is dropped at {}.",
            bug.confidence, line, drop_local, trigger_local, drop_local, drop_bb, trigger_local, trigger_bb
        ),
    }
}

fn dp_detail(
    bug: &TyBug,
    drop_local: &str,
    trigger_local: &str,
    drop_bb: &str,
    _trigger_bb: &str,
) -> String {
    format!(
        "Dangling pointer (confidence {}%): Location in file {} line {}.\n    | MIR detail: Value {} and {} are alias.\n    | MIR detail: {} is dropped at {}; {} became dangling.",
        bug.confidence,
        span_to_filename(bug.span),
        span_to_line_number(bug.span),
        drop_local, trigger_local,
        drop_local, drop_bb,
        trigger_local,
     )
}
