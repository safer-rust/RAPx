//! Optional per-process JSONL output. Completion records distinguish an empty
//! successful scan from a skipped/crashed compiler invocation.
use serde_json::{Value, json};
use std::{fs::File, io::Write, sync::Mutex};

static SINK: Mutex<Option<File>> = Mutex::new(None);

pub fn begin(crate_name: &str) {
    let Some(dir) = std::env::var_os("RAPX_OPT_EVIDENCE_DIR") else {
        return;
    };
    let path = std::path::PathBuf::from(dir).join(format!("{}.jsonl", std::process::id()));
    let file = File::options()
        .create_new(true)
        .write(true)
        .open(path)
        .unwrap_or_else(|e| fail(e));
    *SINK.lock().unwrap() = Some(file);
    emit(json!({"type": "begin", "schema_version": 1, "crate": crate_name}));
}

pub fn emit(record: Value) {
    if let Some(file) = SINK.lock().unwrap().as_mut() {
        let mut bytes = serde_json::to_vec(&record).expect("serialize opt evidence");
        bytes.push(b'\n');
        file.write_all(&bytes).unwrap_or_else(|e| fail(e));
    }
}

pub fn finish(statistics: [usize; 6]) {
    emit(json!({"type": "complete", "statistics": statistics}));
    if let Some(mut file) = SINK.lock().unwrap().take() {
        file.flush().unwrap_or_else(|e| fail(e));
    }
}

fn fail(error: std::io::Error) -> ! {
    crate::utils::log::rap_error_and_exit(format!("Cannot write opt evidence: {error}"))
}
