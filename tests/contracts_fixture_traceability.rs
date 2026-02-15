use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

fn collect_files(root: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_files(&path, out);
            continue;
        }
        out.push(path);
    }
}

fn is_fixture(path: &Path) -> bool {
    matches!(
        path.extension().and_then(|s| s.to_str()),
        Some("ditt")
            | Some("spec")
            | Some("csv")
            | Some("json")
            | Some("txt")
            | Some("stdin")
            | Some("args")
            | Some("expect")
            | Some("diag")
    )
}

fn assert_contract_link_exists(contract_id: &str) {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let (path, symbol) = contract_id.split_once("::").unwrap_or((contract_id, ""));
    assert!(
        !symbol.is_empty(),
        "contract id missing symbol: {contract_id}"
    );
    let full_path = root.join(path);
    assert!(full_path.exists(), "contract file missing: {path}");
    let body = fs::read_to_string(full_path).unwrap();
    assert!(
        body.contains(&format!("fn {symbol}")) || body.contains(symbol),
        "contract symbol missing: {contract_id}"
    );
}

#[test]
fn every_conformance_fixture_is_referenced_by_tests_or_contract_registry() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let conformance_root = root.join("tests").join("conformance");

    let mut fixtures = Vec::new();
    collect_files(&conformance_root, &mut fixtures);
    fixtures.retain(|p| is_fixture(p));
    fixtures.retain(|p| p.file_name().and_then(|s| s.to_str()) != Some("README.md"));
    fixtures.sort();

    let mut sources = Vec::new();
    collect_files(&root.join("tests"), &mut sources);
    collect_files(&root.join("docs"), &mut sources);
    let corpus = sources
        .into_iter()
        .filter_map(|p| fs::read_to_string(p).ok())
        .collect::<Vec<_>>()
        .join("\n");

    let mut missing = Vec::new();
    for fixture in fixtures {
        let rel = fixture
            .strip_prefix(root.join("tests"))
            .unwrap()
            .to_string_lossy()
            .to_string();
        if !corpus.contains(&rel) {
            missing.push(rel);
        }
    }
    assert!(
        missing.is_empty(),
        "orphan fixtures with no test/registry reference: {missing:?}"
    );
}

#[test]
fn coverage_rows_do_not_reference_orphan_contracts_or_missing_fixtures() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    let surface =
        fs::read_to_string(root.join("docs").join("SURFACE_SYNTAX_COVERAGE.csv")).unwrap();
    for (idx, line) in surface.lines().enumerate() {
        if idx == 0 || line.trim().is_empty() {
            continue;
        }
        let cols = line.split(',').map(|s| s.trim()).collect::<Vec<_>>();
        assert_eq!(cols.len(), 5, "bad surface coverage row");
        assert!(
            root.join("tests").join(cols[2]).exists(),
            "missing positive fixture"
        );
        assert!(
            root.join("tests").join(cols[3]).exists(),
            "missing negative fixture"
        );
        assert_contract_link_exists(cols[1]);
    }

    let paper = fs::read_to_string(root.join("docs").join("PAPER_RULE_COVERAGE.csv")).unwrap();
    let mut seen_rule_ids = BTreeSet::new();
    for (idx, line) in paper.lines().enumerate() {
        if idx == 0 || line.trim().is_empty() {
            continue;
        }
        let cols = line.split(',').map(|s| s.trim()).collect::<Vec<_>>();
        assert_eq!(cols.len(), 4, "bad paper coverage row");
        assert!(
            seen_rule_ids.insert(cols[0].to_string()),
            "duplicate rule id in paper coverage"
        );
        assert_contract_link_exists(cols[2]);
        assert_contract_link_exists(cols[3]);
    }
}
