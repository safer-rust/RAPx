use annotate_snippets::{Level, Renderer, Snippet};

use crate::utils::span::{
    relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code,
};
use rustc_span::Span;

#[must_use]
pub struct OptReport {
    code_source: String,
    filename: String,
    line_start: usize,
    rel_span: Span,
    annotations: Vec<(Level, Span, String)>,
    title: String,
    title_level: Level,
    footer: Option<String>,
}

impl OptReport {
    pub fn new(base_span: Span, rel_span: Span) -> Self {
        let code_source = span_to_source_code(base_span);
        let filename = span_to_filename(base_span);
        let line_start = span_to_line_number(base_span);
        Self {
            code_source,
            filename,
            line_start,
            rel_span,
            annotations: Vec::new(),
            title: String::new(),
            title_level: Level::Warning,
            footer: None,
        }
    }

    pub fn from_graph(graph: &crate::analysis::dataflow::Graph) -> Self {
        Self::new(graph.span, graph.span)
    }

    pub fn file_name(mut self, span: Span) -> Self {
        self.filename = span_to_filename(span);
        self
    }

    pub fn title(mut self, title: impl Into<String>) -> Self {
        self.title = title.into();
        self
    }

    pub fn message_level(mut self, level: Level) -> Self {
        self.title_level = level;
        self
    }

    pub fn annotate(mut self, level: Level, span: Span, label: impl Into<String>) -> Self {
        self.annotations.push((level, span, label.into()));
        self
    }

    pub fn footer(mut self, footer: impl Into<String>) -> Self {
        self.footer = Some(footer.into());
        self
    }

    pub fn emit(&self) {
        let mut snippet = Snippet::source(&self.code_source)
            .line_start(self.line_start)
            .origin(&self.filename)
            .fold(true);
        for (level, span, label) in &self.annotations {
            snippet = snippet.annotation(
                level
                    .span(relative_pos_range(self.rel_span, *span))
                    .label(label),
            );
        }
        let message = if let Some(ref footer) = self.footer {
            self.title_level
                .title(&self.title)
                .snippet(snippet)
                .footer(Level::Help.title(footer.as_str()))
        } else {
            self.title_level.title(&self.title).snippet(snippet)
        };
        let renderer = Renderer::styled();
        rap_warn!("{}", renderer.render(message));
    }
}
