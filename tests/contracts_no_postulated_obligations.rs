mod common;

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use common::conformance::parse_judgment_rows;
use common::fixtures::collect_ditt_files;

fn collect_rs_files(root: &Path, out: &mut Vec<PathBuf>) {
    let entries = fs::read_dir(root).unwrap();
    for entry in entries {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_rs_files(&path, out);
            continue;
        }
        if path.extension().and_then(|s| s.to_str()) == Some("rs") {
            out.push(path);
        }
    }
}

fn is_ident(name: &str) -> bool {
    let mut chars = name.chars();
    let first = match chars.next() {
        Some(c) => c,
        None => return false,
    };
    if !(first == '_' || first.is_ascii_alphabetic()) {
        return false;
    }
    chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
}

fn decl_name(line: &str) -> Option<String> {
    let (head, _) = line.split_once(':')?;
    let candidate = head.trim();
    if is_ident(candidate) {
        Some(candidate.to_string())
    } else {
        None
    }
}

fn inline_postulate_name(line: &str) -> Option<String> {
    let rest = line.strip_prefix("postulate")?.trim();
    decl_name(rest)
}

fn collect_postulated_names_from_text(body: &str) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    let mut in_postulate_block = false;

    for (idx, raw) in body.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with("//") {
            continue;
        }

        if line == "postulate" || line.contains("\\npostulate\\n") {
            in_postulate_block = true;
            continue;
        }

        if let Some(name) = inline_postulate_name(line) {
            out.push((idx + 1, name));
            in_postulate_block = false;
            continue;
        }

        if let Some(pos) = line.find("postulate ") {
            let rest = line[pos + "postulate ".len()..].trim();
            if let Some(name) = decl_name(rest) {
                out.push((idx + 1, name));
                in_postulate_block = false;
                continue;
            }
        }

        if in_postulate_block {
            if let Some(name) = decl_name(line) {
                out.push((idx + 1, name));
                continue;
            }
            in_postulate_block = false;
        }
    }

    out
}

#[test]
fn conformance_and_inline_test_fixtures_do_not_postulate_judgment_obligations() {
    let mut forbidden = BTreeSet::new();
    for row in parse_judgment_rows("conformance/semantics/judgments.csv") {
        forbidden.insert(row.name);
    }
    for row in parse_judgment_rows("conformance/semantics/negative_boundaries.csv") {
        forbidden.insert(row.name);
    }

    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("conformance");
    let ditt_files = collect_ditt_files(&root);

    let mut violations = Vec::new();
    for file in ditt_files {
        let body = fs::read_to_string(&file).unwrap();
        for (line, name) in collect_postulated_names_from_text(&body) {
            if forbidden.contains(&name) {
                violations.push(format!("{}:{}:{}", file.display(), line, name));
            }
        }
    }

    let tests_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests");
    let mut rs_files = Vec::new();
    collect_rs_files(&tests_root, &mut rs_files);

    for file in rs_files {
        let body = fs::read_to_string(&file).unwrap();
        for (line, name) in collect_postulated_names_from_text(&body) {
            if forbidden.contains(&name) {
                violations.push(format!("{}:{}:{}", file.display(), line, name));
            }
        }
    }

    assert!(
        violations.is_empty(),
        "judgment obligations must not be postulated in conformance or inline test fixtures: {violations:?}"
    );
}
