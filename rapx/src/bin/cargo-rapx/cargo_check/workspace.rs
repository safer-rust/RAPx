use cargo_metadata::{
    Metadata,
    camino::{Utf8Path, Utf8PathBuf},
};
use rapx::util::log::rap_error_and_exit;
use std::collections::BTreeMap;

/// Run cargo check in each member folder under current workspace.
pub fn shallow_run() {
    let cargo_toml = Utf8Path::new("Cargo.toml");
    if !cargo_toml.exists() {
        rap_error_and_exit("rapx should be run in a folder directly containing Cargo.toml");
    }
    let ws_metadata = workspace(cargo_toml);
    check_members(&ws_metadata);
}

/// Recursively run cargo check in each package folder from current folder.
pub fn deep_run() {
    let cargo_tomls = get_cargo_tomls_deep_recursively(".");
    for ws_metadata in workspaces(&cargo_tomls).values() {
        check_members(ws_metadata);
    }
}

fn check_members(ws_metadata: &Metadata) {
    // Force clean even if `RAPX_CLEAN` is false, because rapx is in control of
    // caches for all packages and there should be no cache.
    let ws_root = &ws_metadata.workspace_root;
    rap_trace!("cargo clean in workspace root {ws_root}");
    super::cargo_clean(ws_root, true);

    for pkg_folder in get_member_folders(ws_metadata) {
        super::cargo_check(pkg_folder);
    }
}

fn get_member_folders(meta: &Metadata) -> Vec<&Utf8Path> {
    meta.workspace_packages()
        .iter()
        .map(|pkg| pkg.manifest_path.parent().unwrap())
        .collect()
}

type Workspaces = BTreeMap<Utf8PathBuf, Metadata>;

fn workspace(cargo_toml: &Utf8Path) -> Metadata {
    let exec = cargo_metadata::MetadataCommand::new()
        .manifest_path(cargo_toml)
        .exec();

    match exec {
        Ok(metadata) => metadata,
        Err(err) => {
            let err = format!(
                "Failed to get the result of cargo metadata \
                 in {cargo_toml}:\n{err}"
            );
            rap_error_and_exit(err)
        }
    }
}

fn workspaces(cargo_tomls: &[Utf8PathBuf]) -> Workspaces {
    let mut map = BTreeMap::new();
    for cargo_toml in cargo_tomls {
        let metadata = workspace(cargo_toml);
        let root = &metadata.workspace_root;
        // The workspace_root and members are the same for each member package
        if !map.contains_key(root) {
            map.insert(root.clone(), metadata);
        }
    }

    map
}

fn get_cargo_tomls_deep_recursively(dir: &str) -> Vec<Utf8PathBuf> {
    walkdir::WalkDir::new(dir)
        .into_iter()
        .filter_map(|entry| {
            if let Ok(e) = entry {
                if e.file_type().is_file() && e.file_name().to_str()? == "Cargo.toml" {
                    let path = Utf8PathBuf::from_path_buf(e.into_path());
                    return path.ok()?.canonicalize_utf8().ok();
                }
            }
            None
        })
        .collect()
}
