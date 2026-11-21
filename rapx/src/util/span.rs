use rustc_middle::mir::{BasicBlock, Body, VarDebugInfoContents};
use rustc_span::{
    source_map::get_source_map,
    {FileName, Pos, Span},
};
use std::ops::Range;

#[inline]
pub fn span_to_source_code(span: Span) -> String {
    get_source_map().unwrap().span_to_snippet(span).unwrap()
}

#[inline]
pub fn span_to_first_line(span: Span) -> Span {
    get_source_map()
        .unwrap()
        .span_extend_to_line(span.shrink_to_lo())
}

#[inline]
pub fn span_to_trimmed_span(span: Span) -> Span {
    span.trim_start(
        get_source_map()
            .unwrap()
            .span_take_while(span, |c| c.is_whitespace()),
    )
    .unwrap()
}

pub fn span_to_filename(span: Span) -> String {
    let filename = get_source_map().unwrap().span_to_filename(span);
    if let FileName::Real(realname) = filename
        && let Some(path) = realname.local_path() {
            return path.to_string_lossy().into();
        }
    "<unknown>".to_string()
}

#[inline]
pub fn span_to_line_number(span: Span) -> usize {
    get_source_map().unwrap().lookup_char_pos(span.lo()).line
}

pub fn get_variable_name<'tcx>(body: &Body<'tcx>, local_index: usize) -> Option<String> {
    let target_local = rustc_middle::mir::Local::from_usize(local_index);

    for info in &body.var_debug_info {
        if let VarDebugInfoContents::Place(place) = info.value
            && place.local == target_local && place.projection.is_empty() {
                return Some(info.name.to_string());
            }
    }

    None
}

pub fn get_basic_block_span<'tcx>(body: &Body<'tcx>, bb_index: usize) -> Span {
    if bb_index >= body.basic_blocks.len() {
        return body.span;
    }

    let bb = BasicBlock::from_usize(bb_index);
    let block_data = &body.basic_blocks[bb];

    if let Some(ref term) = block_data.terminator {
        return term.source_info.span;
    }

    if let Some(stmt) = block_data.statements.first() {
        return stmt.source_info.span;
    }

    body.span
}

#[inline]
pub fn relative_pos_range(span: Span, sub_span: Span) -> Range<usize> {
    if sub_span.lo() < span.lo() || sub_span.hi() > span.hi() {
        return 0..0;
    }
    let offset = span.lo();
    let lo = (sub_span.lo() - offset).to_usize();
    let hi = (sub_span.hi() - offset).to_usize();
    lo..hi
}

pub fn are_spans_in_same_file(span1: Span, span2: Span) -> bool {
    let file1 = get_source_map().unwrap().lookup_source_file(span1.lo());
    let file2 = get_source_map().unwrap().lookup_source_file(span2.lo());
    file1.name == file2.name
}
