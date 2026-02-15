mod common;

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::PathBuf;

use common::conformance::parse_csv;

#[derive(Debug, Clone)]
struct ProvenanceRow {
    kind: String,
    id: String,
    section: String,
    page: String,
    label: String,
    impl_home: String,
}

fn provenance_rows() -> Vec<ProvenanceRow> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let body = fs::read_to_string(root.join("docs").join("PAPER_PROVENANCE.csv")).unwrap();
    let mut lines = body.lines().filter(|l| !l.trim().is_empty());
    let header = lines
        .next()
        .unwrap_or_default()
        .split(',')
        .map(|s| s.trim().to_string())
        .collect::<Vec<_>>();
    assert_eq!(
        header,
        vec![
            "entity_kind",
            "entity_id",
            "section",
            "page",
            "label",
            "impl_home"
        ]
    );

    lines
        .map(|line| {
            let cols = line
                .split(',')
                .map(|s| s.trim().to_string())
                .collect::<Vec<_>>();
            assert_eq!(cols.len(), 6, "bad paper provenance row: {line}");
            ProvenanceRow {
                kind: cols[0].clone(),
                id: cols[1].clone(),
                section: cols[2].clone(),
                page: cols[3].clone(),
                label: cols[4].clone(),
                impl_home: cols[5].clone(),
            }
        })
        .collect()
}

fn rule_ids() -> BTreeSet<String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let body = fs::read_to_string(root.join("docs").join("PAPER_RULE_COVERAGE.csv")).unwrap();
    body.lines()
        .enumerate()
        .filter_map(|(idx, line)| {
            if idx == 0 || line.trim().is_empty() {
                return None;
            }
            Some(line.split(',').next().unwrap().trim().to_string())
        })
        .collect()
}

fn example_ids() -> BTreeSet<String> {
    let (_header, rows) = parse_csv("conformance/semantics/paper_examples.csv");
    let mut ids = rows
        .into_iter()
        .map(|r| r[0].clone())
        .collect::<BTreeSet<_>>();
    let (_header, variance_rows) = parse_csv("conformance/semantics/variance_examples.csv");
    for row in variance_rows {
        ids.insert(row[0].clone());
    }
    let (_header, appendix_rows) = parse_csv("conformance/semantics/paper_appendix_examples.csv");
    for row in appendix_rows {
        ids.insert(row[0].clone());
    }
    ids
}

#[test]
fn paper_provenance_is_complete_for_rules_and_examples() {
    let rows = provenance_rows();
    let rules = rule_ids();
    let examples = example_ids();

    let mut seen = BTreeMap::<(String, String), ProvenanceRow>::new();
    for row in rows {
        match row.kind.as_str() {
            "rule" => {
                assert!(row.section.starts_with('§'));
                assert!(row.page.parse::<u32>().unwrap() > 0);
                assert!(!row.label.is_empty());
                assert!(
                    !row.impl_home.is_empty(),
                    "rule {0} must have impl_home",
                    row.id
                );
            }
            "example" => {
                assert!(row.section.starts_with('§'));
                assert!(row.page.parse::<u32>().unwrap() > 0);
                assert!(!row.label.is_empty());
            }
            "surface_extension" => {
                assert_eq!(row.section, "surface_extension");
                assert_eq!(row.page, "n/a");
                assert!(!row.label.is_empty());
            }
            other => panic!("unexpected provenance kind: {other}"),
        }
        let key = (row.kind.clone(), row.id.clone());
        assert!(
            seen.insert(key, row).is_none(),
            "duplicate provenance row for entity"
        );
    }

    for rule in rules {
        assert!(
            seen.contains_key(&(String::from("rule"), rule.clone())),
            "missing rule provenance row: {rule}"
        );
    }
    for ex in examples {
        assert!(
            seen.contains_key(&(String::from("example"), ex.clone())),
            "missing example provenance row: {ex}"
        );
    }
}
