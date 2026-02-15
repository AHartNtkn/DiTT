mod common;

use std::collections::BTreeMap;
use std::path::PathBuf;

use common::conformance::{parse_csv, read_fixture};
use common::fixtures::collect_ditt_fixture_paths;
use common::support::invocation;
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine, ToolingEngine};

fn negative_stage_map() -> BTreeMap<String, String> {
    let (header, rows) = parse_csv("conformance/syntax/negative_expectations.csv");
    assert_eq!(header, vec!["fixture", "stage", "expected_category"]);
    let mut out = BTreeMap::new();
    for row in rows {
        assert_eq!(row.len(), 3);
        out.insert(row[0].clone(), row[1].clone());
    }
    out
}

fn all_positive_syntax_fixtures() -> Vec<String> {
    let mut fixtures = collect_ditt_fixture_paths(
        &PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("conformance")
            .join("syntax")
            .join("positive"),
    );
    fixtures.sort();
    fixtures
}

fn all_negative_syntax_fixtures() -> Vec<String> {
    let mut fixtures = collect_ditt_fixture_paths(
        &PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("conformance")
            .join("syntax")
            .join("negative"),
    );
    fixtures.sort();
    fixtures
}

fn assert_valid_across_frontends(relative: &str) {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let mut tooling = ToolingEngine::default();
    let source = read_fixture(relative);

    let module = syntax.parse_module(&source).unwrap();
    let _typed = semantics.elaborate_module(&module).unwrap();

    let cli = tooling
        .invoke(&invocation(&["check", "--json"], &source))
        .unwrap();
    assert_eq!(cli.exit_code, 0);

    let session = tooling.start_session().unwrap();
    let repl = tooling.submit(session, &source).unwrap();
    assert!(repl.diagnostics.diagnostics.is_empty());

    let notebook = tooling
        .execute(&ExecuteRequest {
            session,
            code: source.clone(),
            silent: false,
            store_history: true,
        })
        .unwrap();
    assert_eq!(notebook.status, ExecutionStatus::Ok);

    let uri = DocumentUri("file:///tmp/surface_valid.ditt".to_string());
    tooling.open_document(&uri, &source).unwrap();
    let lsp = tooling.diagnostics(&uri).unwrap();
    assert!(lsp.diagnostics.is_empty());
}

fn assert_invalid_parse_stage_across_frontends(relative: &str) {
    let syntax = SyntaxEngine::default();
    let mut tooling = ToolingEngine::default();
    let source = read_fixture(relative);

    let parser_bundle = syntax.parse_module(&source).unwrap_err().into_diagnostics();
    assert!(!parser_bundle.diagnostics.is_empty());

    let cli = tooling
        .invoke(&invocation(&["check", "--json"], &source))
        .unwrap();
    assert_ne!(cli.exit_code, 0);

    let session = tooling.start_session().unwrap();
    let repl = tooling.submit(session, &source).unwrap();
    assert!(!repl.diagnostics.diagnostics.is_empty());

    let notebook = tooling
        .execute(&ExecuteRequest {
            session,
            code: source.clone(),
            silent: false,
            store_history: true,
        })
        .unwrap();
    assert_eq!(notebook.status, ExecutionStatus::Error);

    let uri = DocumentUri("file:///tmp/surface_invalid.ditt".to_string());
    tooling.open_document(&uri, &source).unwrap();
    let lsp = tooling.diagnostics(&uri).unwrap();
    assert!(!lsp.diagnostics.is_empty());
}

fn assert_invalid_check_stage_across_frontends(relative: &str) {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let mut tooling = ToolingEngine::default();
    let source = read_fixture(relative);

    let module = syntax.parse_module(&source).unwrap();
    let check_err = semantics.elaborate_module(&module).unwrap_err();
    let bundle = check_err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());

    let cli = tooling
        .invoke(&invocation(&["check", "--json"], &source))
        .unwrap();
    assert_ne!(cli.exit_code, 0);

    let session = tooling.start_session().unwrap();
    let repl = tooling.submit(session, &source).unwrap();
    assert!(!repl.diagnostics.diagnostics.is_empty());

    let notebook = tooling
        .execute(&ExecuteRequest {
            session,
            code: source.clone(),
            silent: false,
            store_history: true,
        })
        .unwrap();
    assert_eq!(notebook.status, ExecutionStatus::Error);

    let uri = DocumentUri("file:///tmp/surface_invalid_check_stage.ditt".to_string());
    tooling.open_document(&uri, &source).unwrap();
    let lsp = tooling.diagnostics(&uri).unwrap();
    assert!(!lsp.diagnostics.is_empty());
}

#[test]
fn all_positive_surface_fixtures_are_accepted_consistently_across_frontends() {
    let fixtures = all_positive_syntax_fixtures();
    assert!(!fixtures.is_empty());
    for fixture in fixtures {
        assert_valid_across_frontends(&fixture);
    }
}

#[test]
fn all_negative_surface_fixtures_are_rejected_consistently_across_frontends() {
    let stage_map = negative_stage_map();
    let fixtures = all_negative_syntax_fixtures();
    assert!(!fixtures.is_empty());
    for fixture in fixtures {
        let stage = stage_map
            .get(&fixture)
            .unwrap_or_else(|| panic!("missing stage row for {fixture}"));
        match stage.as_str() {
            "parse" => assert_invalid_parse_stage_across_frontends(&fixture),
            "check" => assert_invalid_check_stage_across_frontends(&fixture),
            _ => panic!("unsupported stage in negative matrix"),
        }
    }
}
