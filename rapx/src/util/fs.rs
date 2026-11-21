use crate::util::log::rap_error_and_exit;

use std::fs;
use std::path::Path;

pub fn rap_create_file<P: AsRef<Path>>(path: P, msg: impl AsRef<str>) -> fs::File {
    match fs::File::create(path) {
        Ok(file) => file,
        Err(e) => rap_error_and_exit(format!("{}: {}", msg.as_ref(), e)),
    }
}
