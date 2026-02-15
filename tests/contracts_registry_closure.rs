use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

fn contract_files() -> Vec<PathBuf> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests");
    let mut files = fs::read_dir(&root)
        .unwrap()
        .filter_map(|entry| {
            let path = entry.unwrap().path();
            let name = path.file_name()?.to_str()?;
            if name.starts_with("contracts_") && name.ends_with(".rs") {
                Some(path)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    files.sort();
    files
}

fn test_functions(path: &PathBuf) -> Vec<String> {
    let body = fs::read_to_string(path).unwrap();
    let mut names = Vec::new();
    let lines = body.lines().collect::<Vec<_>>();
    for idx in 0..lines.len() {
        if lines[idx].trim() != "#[test]" {
            continue;
        }
        let mut j = idx + 1;
        while j < lines.len() && lines[j].trim().starts_with("#[") {
            j += 1;
        }
        if j >= lines.len() {
            continue;
        }
        let trimmed = lines[j].trim();
        if let Some(rest) = trimmed.strip_prefix("fn ")
            && let Some((name, _)) = rest.split_once('(')
        {
            names.push(name.trim().to_string());
        }
    }
    names
}

fn docs_corpus() -> String {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("docs");
    let mut corpus = String::new();
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            continue;
        }
        let Some(ext) = path.extension().and_then(|s| s.to_str()) else {
            continue;
        };
        if !matches!(ext, "md" | "csv") {
            continue;
        }
        corpus.push_str(&fs::read_to_string(path).unwrap());
        corpus.push('\n');
    }
    corpus
}

#[test]
fn every_executable_contract_test_is_referenced_by_registry_or_matrix() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let corpus = docs_corpus();

    let mut missing = Vec::new();
    for file in contract_files() {
        let rel = file
            .strip_prefix(&root)
            .unwrap()
            .to_string_lossy()
            .to_string();
        let file_listed = corpus.contains(&rel);

        let tests = test_functions(&file);
        if tests.is_empty() {
            continue;
        }
        for name in tests {
            let id = format!("{rel}::{name}");
            if !(corpus.contains(&id) || file_listed) {
                missing.push(id);
            }
        }
    }

    missing.sort();
    missing.dedup();
    assert!(
        missing.is_empty(),
        "untracked executable contract tests: {missing:?}"
    );
}

#[test]
fn registry_contract_ids_reference_existing_executable_tests() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let corpus = docs_corpus();
    let mut ids = BTreeSet::new();

    for token in corpus.split_whitespace() {
        let raw = token.trim_matches('`').trim_matches(',').trim_matches('|');
        if raw.starts_with("tests/contracts_") && raw.contains("::") {
            ids.insert(raw.to_string());
        }
    }

    for id in ids {
        let (path, symbol) = id.split_once("::").unwrap();
        let full = root.join(path);
        assert!(full.exists(), "registry contract path missing: {id}");
        let body = fs::read_to_string(full).unwrap();
        assert!(
            body.contains(&format!("fn {symbol}")),
            "registry contract symbol missing: {id}"
        );
    }
}
