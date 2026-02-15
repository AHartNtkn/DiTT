#![allow(dead_code)]

use std::fs;
use std::path::{Path, PathBuf};

/// Recursively collect all `.ditt` files under `root`, returning absolute paths.
pub fn collect_ditt_files(root: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    collect_ditt_files_into(root, &mut out);
    out
}

/// Recursively collect all `.ditt` files under `root`, returning paths relative to `tests/`.
pub fn collect_ditt_fixture_paths(root: &Path) -> Vec<String> {
    let tests_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests");
    let mut out = Vec::new();
    let mut abs = Vec::new();
    collect_ditt_files_into(root, &mut abs);
    for path in abs {
        let rel = path
            .strip_prefix(&tests_dir)
            .unwrap()
            .to_string_lossy()
            .to_string();
        out.push(rel);
    }
    out
}

fn collect_ditt_files_into(root: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_ditt_files_into(&path, out);
            continue;
        }
        if path.extension().and_then(|s| s.to_str()) == Some("ditt") {
            out.push(path);
        }
    }
}
