mod common;

use std::collections::BTreeSet;
use std::path::PathBuf;

use common::conformance::{parse_csv, read_fixture};
use common::fixtures::collect_ditt_fixture_paths;
use ditt_lang::api::*;
use ditt_lang::runtime::SyntaxEngine;

fn excluded_roundtrip_paths() -> BTreeSet<String> {
    let (_header, rows) = parse_csv("conformance/syntax/negative_expectations.csv");
    let mut out = rows
        .into_iter()
        .map(|row| row[0].clone())
        .collect::<BTreeSet<_>>();
    out.insert("conformance/parser/invalid_missing_paren.ditt".to_string());
    out
}

fn roundtrip_targets() -> Vec<String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("conformance");
    let excluded = excluded_roundtrip_paths();
    let mut files = collect_ditt_fixture_paths(&root);
    files.retain(|p| !excluded.contains(p));
    files.sort();
    files
}

#[test]
fn roundtrip_target_set_is_nonempty_and_only_includes_existing_fixtures() {
    let targets = roundtrip_targets();
    assert!(!targets.is_empty(), "roundtrip target set is empty");

    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests");
    for fixture in targets {
        assert!(root.join(&fixture).exists(), "missing fixture: {fixture}");
    }
}

#[test]
fn parse_format_parse_is_alpha_equivalent_and_format_is_idempotent_for_all_targets() {
    let syntax = SyntaxEngine::default();
    for fixture in roundtrip_targets() {
        let source = read_fixture(&fixture);
        let parsed_1 = syntax.parse_module(&source).unwrap();
        let formatted_1 = syntax.format_module(&parsed_1).unwrap();
        let parsed_2 = syntax.parse_module(&formatted_1).unwrap();
        let formatted_2 = syntax.format_module(&parsed_2).unwrap();

        let equivalent = syntax
            .alpha_equivalent_modules(&parsed_1, &parsed_2)
            .unwrap();
        assert!(equivalent, "roundtrip changed semantics for {fixture}");
        assert_eq!(
            formatted_1, formatted_2,
            "format not idempotent for {fixture}"
        );
    }
}

#[test]
fn let_shadowing_roundtrip_preserves_capture_avoiding_scope() {
    let syntax = SyntaxEngine::default();
    let shadowed = r#"
module Surface.Roundtrip.LetShadowing where

postulate C : Cat
postulate a : C
probe : C = let x : C = a in let x : C = x in x
"#;
    let alpha_renamed = r#"
module Surface.Roundtrip.LetShadowing where

postulate C : Cat
postulate a : C
probe : C = let outer : C = a in let inner : C = outer in inner
"#;

    let parsed_shadowed = syntax.parse_module(shadowed).unwrap();
    let parsed_alpha_renamed = syntax.parse_module(alpha_renamed).unwrap();
    let alpha_equivalent = syntax
        .alpha_equivalent_modules(&parsed_shadowed, &parsed_alpha_renamed)
        .unwrap();
    assert!(
        alpha_equivalent,
        "shadowed let-binding must preserve capture-avoiding scope under alpha-renaming"
    );

    let formatted = syntax.format_module(&parsed_shadowed).unwrap();
    let reparsed = syntax.parse_module(&formatted).unwrap();
    let roundtrip_equivalent = syntax
        .alpha_equivalent_modules(&parsed_shadowed, &reparsed)
        .unwrap();
    assert!(
        roundtrip_equivalent,
        "let-shadowing roundtrip must preserve inner-let reference to outer binding"
    );
}
