mod common;

use std::collections::{BTreeMap, BTreeSet};

use common::conformance::{parse_csv, parse_kv_fixture};
use ditt_lang::api::*;
use ditt_lang::runtime::SyntaxEngine;

#[test]
fn diagnostic_catalog_rows_are_well_formed() {
    let (header, rows) = parse_csv("conformance/diagnostics/catalog.csv");
    assert_eq!(header, vec!["category", "severity", "summary"]);

    let mut seen = BTreeSet::new();
    for row in rows {
        assert_eq!(row.len(), 3);
        assert!(!row[0].is_empty());
        assert!(matches!(row[1].as_str(), "Error" | "Warning" | "Info"));
        assert!(!row[2].is_empty());
        assert!(
            seen.insert((row[0].clone(), row[1].clone(), row[2].clone())),
            "duplicate catalog row"
        );
    }
}

#[test]
fn emitted_diagnostics_use_catalog_categories_and_stable_ordering_contract() {
    let syntax = SyntaxEngine::default();
    let (_header, rows) = parse_csv("conformance/diagnostics/catalog.csv");
    let categories = rows
        .into_iter()
        .map(|r| r[0].clone())
        .collect::<BTreeSet<_>>();

    let bundle = syntax
        .parse_module("module M where\nx =\ny =\n")
        .unwrap_err()
        .into_diagnostics();
    for d in &bundle.diagnostics {
        assert!(
            categories.contains(&d.category),
            "unknown diagnostic category {}",
            d.category
        );
        assert!(!d.message.is_empty());
        if let Some(span) = d.span {
            assert!(span.start <= span.end);
        }
    }

    let ordering = parse_kv_fixture("conformance/diagnostics/ordering.expect");
    assert_eq!(
        ordering.get("order"),
        Some(&"category,severity,span.start,message".to_string())
    );
}

#[test]
fn diagnostics_do_not_duplicate_identical_entries() {
    let syntax = SyntaxEngine::default();
    let bundle = syntax
        .parse_module("module M where\nx =\n")
        .unwrap_err()
        .into_diagnostics();
    let mut seen = BTreeMap::<(String, usize, usize), usize>::new();
    for d in &bundle.diagnostics {
        let (s, e) = d.span.map(|sp| (sp.start, sp.end)).unwrap_or((0, 0));
        *seen.entry((d.category.clone(), s, e)).or_insert(0) += 1;
    }
    assert!(seen.values().all(|count| *count == 1));
}

#[test]
fn diagnostic_spans_index_into_source_at_erroneous_region() {
    let syntax = SyntaxEngine::default();
    let source = "module M where\nbroken_def (x : C : C = x\n";
    let bundle = syntax.parse_module(source).unwrap_err().into_diagnostics();
    assert!(
        !bundle.diagnostics.is_empty(),
        "invalid source must produce diagnostics"
    );

    for d in &bundle.diagnostics {
        if let Some(span) = d.span {
            assert!(
                span.end <= source.len(),
                "span end {} exceeds source length {}",
                span.end,
                source.len()
            );
            assert!(
                span.start < span.end,
                "diagnostic span must be non-empty: start={}, end={}",
                span.start,
                span.end
            );
            let slice = &source[span.start..span.end];
            assert!(
                !slice.trim().is_empty(),
                "source slice at diagnostic span must contain non-whitespace content"
            );
        }
    }
}
