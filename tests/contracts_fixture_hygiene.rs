use std::fs;
use std::path::{Path, PathBuf};

use regex::Regex;

fn is_fixture_or_spec_doc(path: &Path) -> bool {
    matches!(
        path.extension().and_then(|s| s.to_str()),
        Some("ditt")
            | Some("spec")
            | Some("csv")
            | Some("txt")
            | Some("md")
            | Some("stdin")
            | Some("args")
            | Some("expect")
            | Some("diag")
    )
}

fn collect_files(root: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_files(&path, out);
            continue;
        }
        if is_fixture_or_spec_doc(&path) {
            out.push(path);
        }
    }
}

#[test]
fn fixtures_and_spec_docs_do_not_contain_placeholder_markers() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let targets = [root.join("tests").join("conformance"), root.join("docs")];
    let markers = [
        ("todo", Regex::new(r"(?i)\btodo\b").unwrap()),
        ("placeholder", Regex::new(r"(?i)\bplaceholder\b").unwrap()),
        ("future work", Regex::new(r"(?i)\bfuture\s+work\b").unwrap()),
    ];

    let mut files = Vec::new();
    for dir in targets {
        collect_files(&dir, &mut files);
    }
    files.sort();

    let mut violations = Vec::new();
    for file in files {
        let body = fs::read_to_string(&file).unwrap();
        for (line_idx, line) in body.lines().enumerate() {
            for (marker, regex) in &markers {
                if regex.is_match(line) {
                    violations.push(format!("{}:{}:{}", file.display(), line_idx + 1, marker));
                }
            }
        }
    }

    assert!(
        violations.is_empty(),
        "placeholder marker(s) found in fixtures/spec docs: {violations:?}"
    );
}
