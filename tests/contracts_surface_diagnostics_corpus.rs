mod common;

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use common::conformance::{parse_csv, read_fixture};
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};

#[derive(Debug, Clone)]
struct NegativeRow {
    fixture: String,
    stage: String,
    expected_category: String,
}

#[derive(Debug, Clone)]
struct MessageExpectationRow {
    fixture: String,
    required_fragment: String,
}

fn negative_rows() -> Vec<NegativeRow> {
    let (header, rows) = parse_csv("conformance/syntax/negative_expectations.csv");
    assert_eq!(header, vec!["fixture", "stage", "expected_category"]);
    assert!(!rows.is_empty());

    rows.into_iter()
        .map(|row| {
            assert_eq!(row.len(), 3, "bad negative expectation row");
            NegativeRow {
                fixture: row[0].clone(),
                stage: row[1].clone(),
                expected_category: row[2].clone(),
            }
        })
        .collect()
}

fn message_expectation_rows() -> Vec<MessageExpectationRow> {
    let (header, rows) = parse_csv("conformance/syntax/negative_message_expectations.csv");
    assert_eq!(header, vec!["fixture", "required_fragment"]);
    assert!(!rows.is_empty());

    rows.into_iter()
        .map(|row| {
            assert_eq!(row.len(), 2, "bad negative message expectation row");
            MessageExpectationRow {
                fixture: row[0].clone(),
                required_fragment: row[1].clone(),
            }
        })
        .collect()
}

fn collect_negative_fixtures(root: &Path, out: &mut Vec<String>) {
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_negative_fixtures(&path, out);
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

fn assert_diagnostic_shape(bundle: &DiagnosticBundle) {
    assert!(!bundle.diagnostics.is_empty(), "expected diagnostics");
    for diag in &bundle.diagnostics {
        assert!(!diag.category.trim().is_empty());
        assert!(!diag.message.trim().is_empty());
        if let Some(span) = diag.span {
            assert!(span.start <= span.end);
        }
    }
}

fn diagnostics_for_negative_fixture(
    syntax: &SyntaxEngine,
    semantics: &SemanticEngine,
    row: &NegativeRow,
    source: &str,
) -> DiagnosticBundle {
    match row.stage.as_str() {
        "parse" => syntax.parse_module(source).unwrap_err().into_diagnostics(),
        "check" => {
            let parsed = syntax.parse_module(source).unwrap();
            let err = semantics.elaborate_module(&parsed).unwrap_err();
            err.into_diagnostics()
        }
        _ => panic!("unsupported stage"),
    }
}

#[test]
fn negative_syntax_expectation_rows_cover_all_negative_fixtures_without_orphans() {
    let mut from_disk = Vec::new();
    collect_negative_fixtures(
        &PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("conformance")
            .join("syntax")
            .join("negative"),
        &mut from_disk,
    );
    from_disk.sort();

    let rows = negative_rows();
    let mut from_csv = rows.iter().map(|r| r.fixture.clone()).collect::<Vec<_>>();
    from_csv.sort();

    assert_eq!(
        from_disk, from_csv,
        "negative fixture set and matrix diverged"
    );

    let mut seen = BTreeSet::new();
    for row in rows {
        assert!(
            seen.insert(row.fixture.clone()),
            "duplicate fixture row: {}",
            row.fixture
        );
        assert!(matches!(row.stage.as_str(), "parse" | "check"));
        assert!(!row.expected_category.is_empty());
    }
}

#[test]
fn negative_syntax_fixtures_emit_expected_category_and_valid_span_shape() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    for row in negative_rows() {
        let source = read_fixture(&row.fixture);
        let bundle = diagnostics_for_negative_fixture(&syntax, &semantics, &row, &source);
        assert_diagnostic_shape(&bundle);
        assert!(
            bundle
                .diagnostics
                .iter()
                .any(|d| d.category == row.expected_category),
            "expected category '{}' missing for {}",
            row.expected_category,
            row.fixture
        );
    }
}

#[test]
fn parse_stage_diagnostics_always_include_spans() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    for row in negative_rows()
        .into_iter()
        .filter(|row| row.stage.as_str() == "parse")
    {
        let source = read_fixture(&row.fixture);
        let bundle = diagnostics_for_negative_fixture(&syntax, &semantics, &row, &source);
        assert!(
            !bundle.diagnostics.is_empty(),
            "expected diagnostics for {}",
            row.fixture
        );
        for diagnostic in bundle.diagnostics {
            assert!(
                diagnostic.span.is_some(),
                "parse-stage diagnostic must include a source span for {}",
                row.fixture
            );
        }
    }
}

#[test]
fn negative_message_expectation_rows_are_linked_to_known_negative_fixtures() {
    let mut seen = BTreeSet::new();
    let negatives = negative_rows()
        .into_iter()
        .map(|row| row.fixture)
        .collect::<BTreeSet<_>>();

    for row in message_expectation_rows() {
        assert!(
            negatives.contains(&row.fixture),
            "message expectation references unknown negative fixture: {}",
            row.fixture
        );
        assert!(
            seen.insert(row.fixture.clone()),
            "duplicate message expectation fixture row: {}",
            row.fixture
        );
        assert!(
            row.required_fragment.trim().len() >= 3,
            "required message fragment must be at least 3 chars for {}",
            row.fixture
        );
    }
}

#[test]
fn key_negative_syntax_fixtures_emit_required_message_fragments() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let negatives = negative_rows()
        .into_iter()
        .map(|row| (row.fixture.clone(), row))
        .collect::<std::collections::BTreeMap<_, _>>();

    for message_row in message_expectation_rows() {
        let row = negatives
            .get(&message_row.fixture)
            .unwrap_or_else(|| panic!("missing negative row for {}", message_row.fixture));
        let source = read_fixture(&message_row.fixture);
        let bundle = diagnostics_for_negative_fixture(&syntax, &semantics, row, &source);
        assert_diagnostic_shape(&bundle);
        assert!(
            bundle
                .diagnostics
                .iter()
                .any(|d| d.category == row.expected_category),
            "expected category '{}' missing for {}",
            row.expected_category,
            row.fixture
        );
        let required = message_row.required_fragment.to_ascii_lowercase();
        assert!(
            bundle
                .diagnostics
                .iter()
                .any(|d| d.message.to_ascii_lowercase().contains(&required)),
            "required message fragment '{}' missing for {}",
            message_row.required_fragment,
            message_row.fixture
        );
    }
}
