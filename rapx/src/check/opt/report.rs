use annotate_snippets::{Level, Renderer, Snippet};

use crate::utils::span::{
    relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code,
};
use rustc_span::Span;
use serde::{Deserialize, Serialize};

/// Stable rule identities, independent of diagnostic wording and source locations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OptRule {
    BoundsLen,
    BoundsLoopPush,
    BoundsExtend,
    VecEncoding,
    ArrayEncoding,
    StringPush,
    StringLowercase,
    VecRemove,
    SliceContains,
    Participant,
    LocalSet,
    VecInit,
    UnreservedHash,
    UnreservedVec,
    FlattenCollect,
    UsedAsImmutable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OptCategory {
    BoundsChecking,
    EncodingChecking,
    Suboptimal,
    Initialization,
    Reallocation,
    Cloning,
}

impl OptRule {
    pub fn category(self) -> OptCategory {
        match self {
            Self::BoundsLen | Self::BoundsLoopPush | Self::BoundsExtend => {
                OptCategory::BoundsChecking
            }
            Self::VecEncoding | Self::ArrayEncoding | Self::StringPush | Self::StringLowercase => {
                OptCategory::EncodingChecking
            }
            Self::VecRemove | Self::SliceContains | Self::Participant => OptCategory::Suboptimal,
            Self::LocalSet | Self::VecInit => OptCategory::Initialization,
            Self::UnreservedHash | Self::UnreservedVec | Self::FlattenCollect => {
                OptCategory::Reallocation
            }
            Self::UsedAsImmutable => OptCategory::Cloning,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RunStatus {
    Completed,
    Skipped,
}

/// Written last for each compilation unit; absence means output is incomplete.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OptProfile {
    pub schema_version: u32,
    pub unit: String,
    pub rapx_version: String,
    pub rustc_version: Option<String>,
    pub working_directory: String,
    pub status: RunStatus,
    pub level: usize,
    pub no_std: bool,
    /// User function/closure graphs checked, excluding the two RAPx-injected helpers.
    pub analyzed_functions: usize,
    pub finding_count: usize,
    /// Counts sites, in category order: bounds, encoding, suboptimal,
    /// initialization, reallocation, cloning. A report can annotate several sites.
    pub statistics: [usize; 6],
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub limitations: Vec<String>,
}

/// The same source snippet, annotations and advice shown in the terminal.
/// This is a static candidate, kept separate from any later AI review.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OptFinding {
    /// Unit-local identity, not a cross-run matching fingerprint.
    pub id: String,
    pub rule_id: OptRule,
    pub category: OptCategory,
    pub function: String,
    pub title: String,
    pub level: String,
    pub file: String,
    pub line_start: usize,
    pub source: String,
    pub annotations: Vec<OptAnnotation>,
    pub static_advice: Option<String>,
    pub static_status: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OptAnnotation {
    pub file: String,
    /// One-based source line.
    pub line: usize,
    /// Byte offsets relative to the finding's source snippet, with exclusive end.
    /// 0..0 means the annotation could not be mapped into that snippet.
    pub range: std::ops::Range<usize>,
    pub level: String,
    pub label: String,
}

#[must_use]
pub struct OptReport {
    rule: OptRule,
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
    pub fn new(base_span: Span, rel_span: Span, rule: OptRule) -> Self {
        let code_source = span_to_source_code(base_span);
        let filename = span_to_filename(base_span);
        let line_start = span_to_line_number(base_span);
        Self {
            rule,
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

    pub fn from_graph(graph: &crate::analysis::dataflow::Graph, rule: OptRule) -> Self {
        Self::new(graph.span, graph.span, rule)
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

    pub fn into_finding(self, function: String) -> OptFinding {
        let annotations = self
            .annotations
            .into_iter()
            .map(|(level, span, label)| OptAnnotation {
                file: span_to_filename(span),
                line: span_to_line_number(span),
                range: relative_pos_range(self.rel_span, span),
                level: level_name(level).into(),
                label,
            })
            .collect();
        OptFinding {
            id: String::new(),
            rule_id: self.rule,
            category: self.rule.category(),
            function,
            title: self.title,
            level: level_name(self.title_level).into(),
            file: self.filename,
            line_start: self.line_start,
            source: self.code_source,
            annotations,
            static_advice: self.footer,
            static_status: "optimization_candidate".into(),
        }
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

fn level_name(level: Level) -> &'static str {
    match level {
        Level::Error => "error",
        Level::Warning => "warning",
        Level::Info => "info",
        Level::Note => "note",
        Level::Help => "help",
    }
}
