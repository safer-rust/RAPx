//! Identify the compilation unit whose SafeDrop report is being written.

pub fn unit_name(rustc_args: &[String]) -> Result<String, String> {
    let (unit, kind) = safedrop_unit(
        rustc_args,
        std::env::var_os("CARGO_BIN_NAME").is_some(),
        std::env::var_os("CARGO_TARGET_TMPDIR").is_some(),
    )?;
    Ok(format!("{unit}-{kind}"))
}

/// Cargo omits --crate-type for test harnesses. CARGO_BIN_NAME identifies a
/// binary's unit tests; CARGO_TARGET_TMPDIR distinguishes integration targets
/// from library unit tests when cargo check --tests is used.
fn safedrop_unit(
    arguments: &[String],
    cargo_binary: bool,
    cargo_target_tmpdir: bool,
) -> Result<(&str, &'static str), String> {
    let name = rustc_option_values(arguments, "--crate-name")
        .first()
        .copied()
        .filter(|name| !name.is_empty())
        .ok_or_else(|| "Cannot name SafeDrop output: rustc --crate-name is missing".to_owned())?;
    let types: Vec<_> = rustc_option_values(arguments, "--crate-type")
        .into_iter()
        .flat_map(|value| value.split(','))
        .collect();
    let mut binary = false;
    let mut library = false;
    for crate_type in &types {
        match *crate_type {
            "bin" => binary = true,
            "lib" => library = true,
            other => return Err(format!("Cannot classify SafeDrop crate type `{other}`")),
        }
    }
    if binary && library {
        return Err(
            "Cannot export mixed library and binary crate types to one SafeDrop unit report".into(),
        );
    }
    let test = arguments.iter().any(|arg| arg == "--test");
    let kind = if test {
        if binary || (types.is_empty() && cargo_binary) {
            "bin-test"
        } else if types.is_empty() && cargo_target_tmpdir {
            "integration-test"
        } else {
            "lib-test"
        }
    } else if library {
        "lib"
    } else {
        // rustc defaults to a binary when --crate-type is not specified.
        "bin"
    };
    Ok((name, kind))
}

fn rustc_option_values<'a>(arguments: &'a [String], key: &str) -> Vec<&'a str> {
    let prefix = format!("{key}=");
    arguments
        .iter()
        .enumerate()
        .filter_map(|(index, arg)| {
            if arg == key {
                arguments.get(index + 1).map(String::as_str)
            } else {
                arg.strip_prefix(&prefix)
            }
        })
        .collect()
}
