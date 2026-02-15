use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

fn extract_clause_ids_from_contract_doc() -> BTreeSet<String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let body = fs::read_to_string(root.join("docs").join("SURFACE_SYNTAX_CONTRACT.md")).unwrap();
    let mut out = BTreeSet::new();

    let mut start = 0usize;
    while let Some(idx) = body[start..].find("[clause:") {
        let absolute = start + idx + "[clause:".len();
        if let Some(end_rel) = body[absolute..].find(']') {
            let end = absolute + end_rel;
            let clause = body[absolute..end].trim();
            if !clause.is_empty() {
                out.insert(clause.to_string());
            }
            start = end + 1;
        } else {
            break;
        }
    }

    out
}

fn extract_clause_ids_from_coverage_csv() -> BTreeSet<String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let body = fs::read_to_string(root.join("docs").join("SURFACE_SYNTAX_COVERAGE.csv")).unwrap();
    let mut out = BTreeSet::new();

    for (idx, raw) in body.lines().enumerate() {
        if idx == 0 || raw.trim().is_empty() {
            continue;
        }
        let cols = raw.split(',').map(|s| s.trim()).collect::<Vec<_>>();
        assert_eq!(cols.len(), 5, "bad coverage row: {raw}");
        out.insert(cols[0].to_string());
    }

    out
}

#[test]
fn every_normative_surface_clause_has_coverage_row_and_no_orphans() {
    let from_doc = extract_clause_ids_from_contract_doc();
    let from_csv = extract_clause_ids_from_coverage_csv();

    assert!(
        !from_doc.is_empty(),
        "contract doc clause registry is empty"
    );
    assert_eq!(from_doc, from_csv, "doc/coverage clause sets diverged");
}
