use cargo_metadata::{MetadataCommand, camino::Utf8Path};
use rapx::util::log::rap_error_and_exit;
use std::{env, path::Path};

const BUILD_SCRIPTS: &str = "RAPX_BUILD_SCRIPTS";

// Manifest path, rustc crate name, and source path.
type BuildScript = (String, String, String);

pub fn collect(dir: &Utf8Path, cargo_args: &[String]) -> String {
    let mut command = MetadataCommand::new();
    command.current_dir(dir).no_deps();
    if let Some(path) = option(cargo_args, "--manifest-path") {
        command.manifest_path(path);
    }
    let metadata = command.exec().unwrap_or_else(|err| {
        rap_error_and_exit(format!("Failed to identify build-script targets: {err}"))
    });
    let scripts: Vec<BuildScript> = metadata
        .packages
        .iter()
        .flat_map(|package| {
            package.targets.iter().filter_map(|target| {
                target
                    .kind
                    .iter()
                    .any(|kind| kind == "custom-build")
                    .then(|| {
                        (
                            package.manifest_path.to_string(),
                            target.name.replace('-', "_"),
                            target.src_path.to_string(),
                        )
                    })
            })
        })
        .collect();
    serde_json::to_string(&scripts).expect("Failed to encode build-script targets")
}

pub fn configure(command: &mut std::process::Command, scripts: String) {
    command.env(BUILD_SCRIPTS, scripts);
}

pub fn is_build_script(args: &[String]) -> bool {
    if env::var_os("CARGO_BIN_NAME").is_some()
        || option(args, "--crate-type") != Some("bin")
        || args.iter().any(|arg| arg == "--test")
        || !option(args, "--emit").is_some_and(|emit| emit.split(',').any(|kind| kind == "link"))
    {
        return false;
    }
    let Some(manifest_dir) = env::var_os("CARGO_MANIFEST_DIR") else {
        return false;
    };
    let manifest = Path::new(&manifest_dir).join("Cargo.toml");
    let scripts: Vec<BuildScript> =
        serde_json::from_str(&env::var(BUILD_SCRIPTS).unwrap_or_else(|_| "[]".to_owned()))
            .unwrap_or_else(|err| {
                rap_error_and_exit(format!("Invalid build-script targets: {err}"))
            });
    scripts.iter().any(|(package, name, source)| {
        option(args, "--crate-name") == Some(name.as_str())
            && same_path(&manifest, Path::new(package))
            && args
                .iter()
                .any(|arg| same_path(Path::new(arg), Path::new(source)))
    })
}

fn same_path(left: &Path, right: &Path) -> bool {
    match (left.canonicalize(), right.canonicalize()) {
        (Ok(left), Ok(right)) => left == right,
        _ => false,
    }
}

fn option<'a>(args: &'a [String], name: &str) -> Option<&'a str> {
    args.iter().enumerate().find_map(|(index, arg)| {
        if arg == name {
            args.get(index + 1).map(String::as_str)
        } else {
            arg.strip_prefix(name)?.strip_prefix('=')
        }
    })
}
