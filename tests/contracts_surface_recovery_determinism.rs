mod common;

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use common::conformance::{canonical_severity, read_fixture};
use ditt_lang::api::*;
use ditt_lang::runtime::SyntaxEngine;

type DiagnosticKey = (String, String, Option<usize>, Option<usize>, String);

fn diagnostic_signature_multiset(bundle: &DiagnosticBundle) -> BTreeMap<DiagnosticKey, usize> {
    let mut counts = BTreeMap::new();
    for diagnostic in &bundle.diagnostics {
        let key = (
            diagnostic.category.clone(),
            canonical_severity(&diagnostic.severity).to_string(),
            diagnostic.span.map(|s| s.start),
            diagnostic.span.map(|s| s.end),
            diagnostic.message.clone(),
        );
        *counts.entry(key).or_insert(0) += 1;
    }
    counts
}

fn collect_negative_syntax_fixtures(root: &Path, out: &mut Vec<String>) {
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_negative_syntax_fixtures(&path, out);
            continue;
        }
        if path.extension().and_then(|s| s.to_str()) != Some("ditt") {
            continue;
        }
        let rel = path
            .strip_prefix(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests"))
            .unwrap()
            .to_string_lossy()
            .to_string();
        out.push(rel);
    }
}

#[test]
fn parser_recovery_is_deterministic_for_all_negative_surface_fixtures() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("conformance")
        .join("syntax")
        .join("negative");
    let mut fixtures = Vec::new();
    collect_negative_syntax_fixtures(&root, &mut fixtures);
    fixtures.sort();

    let syntax = SyntaxEngine::default();
    let semantics = ditt_lang::runtime::SemanticEngine::default();
    for fixture in fixtures {
        let source = read_fixture(&fixture);
        match syntax.parse_module(&source) {
            Err(e1) => {
                // Parse-stage negative: verify recovery determinism.
                let b1 = e1.into_diagnostics();
                let b2 = syntax.parse_module(&source).unwrap_err().into_diagnostics();

                assert_eq!(
                    diagnostic_signature_multiset(&b1),
                    diagnostic_signature_multiset(&b2),
                    "recovery bundle content must be stable for {fixture} regardless of order"
                );
                assert!(
                    !b1.diagnostics.is_empty(),
                    "negative fixture {fixture} had no diagnostics"
                );

                for d in b1.diagnostics {
                    assert!(!d.category.is_empty());
                    assert!(!d.message.is_empty());
                    if let Some(span) = d.span {
                        assert!(span.start <= span.end);
                    }
                }
            }
            Ok(parsed) => {
                // Check-stage negative: parses fine, must fail during elaboration.
                let b1 = semantics
                    .elaborate_module(&parsed)
                    .unwrap_err()
                    .into_diagnostics();
                let b2 = semantics
                    .elaborate_module(&parsed)
                    .unwrap_err()
                    .into_diagnostics();

                assert_eq!(
                    diagnostic_signature_multiset(&b1),
                    diagnostic_signature_multiset(&b2),
                    "elaboration error must be stable for check-stage negative {fixture}"
                );
                assert!(
                    !b1.diagnostics.is_empty(),
                    "check-stage negative fixture {fixture} had no diagnostics"
                );
            }
        }
    }
}
