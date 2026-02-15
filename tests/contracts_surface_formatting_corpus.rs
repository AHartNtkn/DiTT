mod common;

use std::collections::BTreeSet;
use std::path::PathBuf;

use common::conformance::{parse_csv, read_fixture};
use common::fixtures::collect_ditt_fixture_paths;
use common::support::assert_format_contracts;
use ditt_lang::api::*;
use ditt_lang::runtime::SyntaxEngine;

fn excluded_paths() -> BTreeSet<String> {
    let (_header, rows) = parse_csv("conformance/syntax/negative_expectations.csv");
    let mut out = rows
        .into_iter()
        .map(|row| row[0].clone())
        .collect::<BTreeSet<_>>();
    out.insert("conformance/parser/invalid_missing_paren.ditt".to_string());
    out
}

fn formatting_targets() -> Vec<String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("conformance");
    let excluded = excluded_paths();
    let mut out = collect_ditt_fixture_paths(&root);
    out.retain(|p| !excluded.contains(p));
    out.sort();
    out
}

#[test]
fn formatting_targets_are_exhaustive_over_non_negative_corpus() {
    let targets = formatting_targets();
    assert!(!targets.is_empty(), "formatting target set is empty");
    for fixture in targets {
        assert!(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests")
                .join(&fixture)
                .exists(),
            "missing fixture: {fixture}"
        );
    }
}

#[test]
fn formatter_constraints_hold_for_all_non_negative_corpus_targets() {
    let syntax = SyntaxEngine::default();
    for fixture in formatting_targets() {
        let source = read_fixture(&fixture);
        let parsed = syntax.parse_module(&source).unwrap();
        let formatted = syntax.format_module(&parsed).unwrap();
        assert_format_contracts(&formatted);

        let reparsed = syntax.parse_module(&formatted).unwrap();
        let eq = syntax.alpha_equivalent_modules(&parsed, &reparsed).unwrap();
        assert!(eq, "formatting changed semantics for {fixture}");
    }
}
