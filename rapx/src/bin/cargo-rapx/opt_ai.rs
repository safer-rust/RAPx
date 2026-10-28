use std::process::Command;

pub fn run(options: &rapx::cli::OptAiArgs) {
    let config = serde_json::json!({
        "offline": options.offline,
        "output": options.output,
        "api_url": options.api_url,
        "model": options.model,
        "api_timeout": options.api_timeout,
        "max_findings": options.max_findings,
        "max_context_bytes": options.max_context_bytes,
        "cargo_rapx": crate::args::current_exe_path(),
        "cargo_args": crate::args::rap_and_cargo_args()[1],
        "scan_timeout": crate::args::cargo_cli().args().timeout,
    });
    // Embed the stdlib-only helper so cargo install does not need a source checkout.
    let python = std::env::var_os("RAPX_PYTHON").unwrap_or_else(|| "python3".into());
    let result = Command::new(python)
        .args([
            "-c",
            include_str!("../../../opt_ai.py"),
            &config.to_string(),
        ])
        .status();
    match result {
        Ok(status) => std::process::exit(status.code().unwrap_or(1)),
        Err(_) => rapx::utils::log::rap_error_and_exit(
            "opt-ai requires Python 3.10+; set RAPX_PYTHON to its executable path",
        ),
    }
}
