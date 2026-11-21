use annotate_snippets::{Level, Renderer, Snippet};
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::Body, ty::TyCtxt};
use rustc_span::{Span, Symbol};

use crate::util::{
    source::get_name,
    span::{
        are_spans_in_same_file, relative_pos_range, span_to_filename, span_to_line_number,
        span_to_source_code,
    },
};

pub(super) fn emit(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    body: &Body<'_>,
    sources: impl IntoIterator<Item = Span>,
) {
    let name = get_name(tcx, def_id).unwrap_or_else(|| Symbol::intern("no symbol available"));
    rap_warn!("Memory Leak detected in function {name}");
    let source = span_to_source_code(body.span);
    let file = span_to_filename(body.span);
    let mut snippet = Snippet::source(&source)
        .line_start(span_to_line_number(body.span))
        .origin(&file)
        .fold(false);
    for span in sources {
        if are_spans_in_same_file(body.span, span) {
            snippet = snippet.annotation(
                Level::Warning
                    .span(relative_pos_range(body.span, span))
                    .label("Memory Leak Candidates."),
            );
        }
    }
    let message = Level::Warning
        .title("Memory Leak detected.")
        .snippet(snippet);
    rap_warn!("{}", Renderer::styled().render(message));
}
