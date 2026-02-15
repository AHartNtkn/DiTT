mod common;

use std::collections::{BTreeMap, BTreeSet};

use common::conformance::{canonical_severity, parse_csv, read_fixture};
use common::support::invocation;
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine, ToolingEngine};
use serde_json::Value;

#[derive(Debug, Clone, PartialEq, Eq)]
struct DiagnosticSignature {
    category: String,
    severity: String,
    has_span: bool,
    span_start: Option<usize>,
    message: String,
}

#[derive(Debug, Clone)]
struct NegativeRow {
    fixture: String,
    stage: String,
}

fn rows() -> Vec<NegativeRow> {
    let (header, rows) = parse_csv("conformance/syntax/negative_expectations.csv");
    assert_eq!(header, vec!["fixture", "stage", "expected_category"]);
    rows.into_iter()
        .map(|r| NegativeRow {
            fixture: r[0].clone(),
            stage: r[1].clone(),
        })
        .collect()
}

fn normalize_message(raw: &str) -> String {
    raw.split_whitespace()
        .map(|s| s.to_ascii_lowercase())
        .collect::<Vec<_>>()
        .join(" ")
}

fn assert_message_quality(message: &str) {
    let normalized = normalize_message(message);
    assert!(!normalized.is_empty());
    assert!(
        normalized.chars().any(|c| c.is_ascii_alphabetic()),
        "diagnostic message must carry explanatory text"
    );
}

fn diagnostic_signature(bundle: &DiagnosticBundle) -> Vec<DiagnosticSignature> {
    assert!(!bundle.diagnostics.is_empty());
    bundle
        .diagnostics
        .iter()
        .map(|d| {
            assert!(!d.category.trim().is_empty());
            assert_message_quality(&d.message);
            DiagnosticSignature {
                category: d.category.to_ascii_lowercase(),
                severity: canonical_severity(&d.severity).to_ascii_lowercase(),
                has_span: d.span.is_some(),
                span_start: d.span.map(|s| s.start),
                message: normalize_message(&d.message),
            }
        })
        .collect::<Vec<_>>()
}

fn baseline_diagnostics(
    syntax: &SyntaxEngine,
    semantics: &SemanticEngine,
    source: &str,
    stage: &str,
) -> DiagnosticBundle {
    let bundle = match stage {
        "parse" => syntax.parse_module(source).unwrap_err().into_diagnostics(),
        "check" => {
            let parsed = syntax.parse_module(source).unwrap();
            semantics
                .elaborate_module(&parsed)
                .unwrap_err()
                .into_diagnostics()
        }
        _ => panic!("unsupported stage"),
    };
    assert!(!bundle.diagnostics.is_empty());
    bundle
}

fn cli_signature(cli: &CliResponse) -> Vec<DiagnosticSignature> {
    let raw = cli
        .json
        .as_ref()
        .expect("check --json must return machine-readable diagnostics");
    let parsed: Value = serde_json::from_str(raw).expect("cli json must be valid");
    let diagnostics = parsed
        .get("diagnostics")
        .and_then(Value::as_array)
        .expect("cli json must include diagnostics array");

    diagnostics
        .iter()
        .map(|d| {
            let category = d
                .get("category")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_ascii_lowercase();
            let severity = d
                .get("severity")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_ascii_lowercase();
            let message = d.get("message").and_then(Value::as_str).unwrap_or_default();
            assert!(!category.trim().is_empty());
            assert!(!severity.trim().is_empty());
            assert_message_quality(message);
            let span = d.get("span").unwrap_or(&Value::Null);
            let span_start = span
                .get("start")
                .and_then(Value::as_u64)
                .map(|n| n as usize);
            DiagnosticSignature {
                category,
                severity,
                has_span: !span.is_null(),
                span_start,
                message: normalize_message(message),
            }
        })
        .collect::<Vec<_>>()
}

fn notebook_message_aligns_with_baseline(notebook: &str, baseline: &str) -> bool {
    let notebook_tokens = normalize_message(notebook)
        .split_whitespace()
        .filter(|token| token.len() >= 2)
        .map(str::to_string)
        .collect::<BTreeSet<_>>();
    let baseline_tokens = normalize_message(baseline)
        .split_whitespace()
        .filter(|token| token.len() >= 2)
        .map(str::to_string)
        .collect::<BTreeSet<_>>();

    if baseline_tokens.is_empty() {
        return !notebook_tokens.is_empty();
    }

    baseline_tokens.is_subset(&notebook_tokens)
}

fn signature_core_key(sig: &DiagnosticSignature) -> (String, String, bool) {
    (sig.category.clone(), sig.severity.clone(), sig.has_span)
}

fn assert_surface_signature_aligns(
    label: &str,
    actual: &[DiagnosticSignature],
    baseline: &[DiagnosticSignature],
) {
    let mut actual_by_core = BTreeMap::<(String, String, bool), Vec<String>>::new();
    let mut baseline_by_core = BTreeMap::<(String, String, bool), Vec<String>>::new();

    for sig in actual {
        actual_by_core
            .entry(signature_core_key(sig))
            .or_default()
            .push(sig.message.clone());
    }
    for sig in baseline {
        baseline_by_core
            .entry(signature_core_key(sig))
            .or_default()
            .push(sig.message.clone());
    }

    assert_eq!(
        actual_by_core.len(),
        baseline_by_core.len(),
        "{label} diagnostic core-signature set differs from baseline"
    );

    for (core, got_messages) in actual_by_core {
        let expected_messages = baseline_by_core.get(&core).unwrap_or_else(|| {
            panic!("{label} diagnostic core-signature missing in baseline: {core:?}")
        });
        assert_eq!(
            got_messages.len(),
            expected_messages.len(),
            "{label} diagnostic multiplicity differs for core-signature {core:?}"
        );

        for got_message in got_messages {
            assert!(
                expected_messages
                    .iter()
                    .any(|expected| notebook_message_aligns_with_baseline(&got_message, expected)),
                "{label} diagnostic message '{}' has no aligned baseline message within core-signature {:?}",
                got_message,
                core
            );
        }
    }
}

#[test]
fn diagnostics_signatures_align_across_frontends() {
    for row in rows() {
        let source = read_fixture(&row.fixture);
        let syntax = SyntaxEngine::default();
        let semantics = SemanticEngine::default();
        let mut tooling = ToolingEngine::default();
        let base_bundle = baseline_diagnostics(&syntax, &semantics, &source, &row.stage);
        let base_signature = diagnostic_signature(&base_bundle);
        let base_categories = base_signature
            .iter()
            .map(|d| d.category.clone())
            .collect::<Vec<_>>();

        let cli = tooling
            .invoke(&invocation(&["check", "--json"], &source))
            .unwrap();
        assert_ne!(cli.exit_code, 0);
        let cli_signature = cli_signature(&cli);
        assert_surface_signature_aligns("cli", &cli_signature, &base_signature);

        let session = tooling.start_session().unwrap();
        let repl = tooling.submit(session, &source).unwrap();
        let repl_signature = diagnostic_signature(&repl.diagnostics);
        assert_surface_signature_aligns("repl", &repl_signature, &base_signature);

        let notebook = tooling
            .execute(&ExecuteRequest {
                session,
                code: source.clone(),
                silent: false,
                store_history: true,
            })
            .unwrap();
        assert_eq!(notebook.status, ExecutionStatus::Error);
        let notebook_errors = notebook
            .events
            .iter()
            .filter_map(|e| match e {
                NotebookEvent::Error { ename, evalue } => Some((ename.clone(), evalue.clone())),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(notebook_errors.len(), base_signature.len());
        for (ename, evalue) in notebook_errors {
            assert!(!ename.trim().is_empty());
            assert_message_quality(&evalue);
            let lowered = ename.to_ascii_lowercase();
            assert!(
                base_categories
                    .iter()
                    .any(|c| lowered == *c || lowered.contains(c)),
                "notebook error class '{}' not aligned with baseline categories {:?}",
                ename,
                base_categories
            );
            assert!(
                base_signature
                    .iter()
                    .any(|sig| notebook_message_aligns_with_baseline(&evalue, &sig.message)),
                "notebook message '{}' not aligned with any baseline diagnostic message",
                evalue,
            );
        }

        let uri = DocumentUri(format!("file:///tmp/diag_parity_{}.ditt", row.stage));
        tooling.open_document(&uri, &source).unwrap();
        let lsp = tooling.diagnostics(&uri).unwrap();
        let lsp_signature = diagnostic_signature(&lsp);
        assert_surface_signature_aligns("lsp", &lsp_signature, &base_signature);
    }
}
