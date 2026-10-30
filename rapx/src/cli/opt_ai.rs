use clap::Args;
use std::path::PathBuf;

/// Run opt, review its findings, and write an auditable report.
#[derive(Debug, Clone, Args)]
pub struct OptAiArgs {
    /// Export evidence and prompts without contacting an AI service
    #[arg(long)]
    pub offline: bool,
    /// Parent directory for a new, unique run directory
    #[arg(long, default_value = "target/rapx-opt-ai")]
    pub output: PathBuf,
    /// Full chat-completions endpoint (or RAPX_AI_URL)
    #[arg(long)]
    pub api_url: Option<String>,
    /// Model identifier (or RAPX_AI_MODEL)
    #[arg(long)]
    pub model: Option<String>,
    /// Maximum seconds per API request
    #[arg(long, default_value_t = 60, value_parser = clap::value_parser!(u64).range(1..))]
    pub api_timeout: u64,
    /// Maximum number of API requests; other findings remain unreviewed
    #[arg(long, default_value_t = 20)]
    pub max_findings: usize,
    /// Maximum evidence bytes per request; oversized findings remain unreviewed
    #[arg(long, default_value_t = 48000)]
    pub max_context_bytes: usize,
}
