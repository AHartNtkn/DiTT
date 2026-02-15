mod common;

use std::collections::BTreeMap;

use common::conformance::{canonical_severity, read_fixture};
use ditt_lang::api::*;
use ditt_lang::runtime::ToolingEngine;

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

#[test]
fn notebook_execute_respects_silent_and_store_history_flags() {
    let mut tooling = ToolingEngine::default();
    let first = tooling
        .execute(&ExecuteRequest {
            session: 1,
            code: "postulate C : Cat".to_string(),
            silent: true,
            store_history: false,
        })
        .unwrap();
    let second = tooling
        .execute(&ExecuteRequest {
            session: 1,
            code: "C".to_string(),
            silent: false,
            store_history: true,
        })
        .unwrap();

    assert!(first.events.is_empty());
    assert!(second.execution_count > first.execution_count);
}

#[test]
fn notebook_completion_cursor_bounds_are_valid() {
    let tooling = ToolingEngine::default();
    let code = "postulate C : Cat\nmap : (x : C) -> C = \\x. x\nma";
    let cursor = code.len();
    let reply = NotebookKernel::complete(&tooling, code, cursor).unwrap();

    assert!(reply.cursor_start <= reply.cursor_end);
    assert!(reply.cursor_end <= cursor);
}

#[test]
fn notebook_inspect_returns_contextual_information_with_valid_bounds() {
    let tooling = ToolingEngine::default();
    let code = "postulate C : Cat\nid : (x : C) -> C = \\x. x\nid";
    let cursor = code.len();
    let reply = tooling.inspect(code, cursor).unwrap();

    assert!(reply.cursor_start <= reply.cursor_end);
    assert!(reply.cursor_end <= cursor);
    if reply.found {
        assert!(!reply.contents.is_empty());
    }
}

#[test]
fn notebook_interrupt_restart_and_shutdown_follow_protocol_contract() {
    let mut tooling = ToolingEngine::default();
    let flow = read_fixture("conformance/notebook/session_flow.txt");
    assert!(flow.contains("interrupt=1"));
    assert!(flow.contains("restart=1"));
    assert!(flow.contains("shutdown=1"));

    let _ = tooling
        .execute(&ExecuteRequest {
            session: 1,
            code: "postulate C : Cat".to_string(),
            silent: false,
            store_history: true,
        })
        .unwrap();
    tooling.interrupt(1).unwrap();
    tooling.restart(1).unwrap();
    tooling.shutdown().unwrap();

    let after_shutdown = tooling.execute(&ExecuteRequest {
        session: 1,
        code: "C".to_string(),
        silent: false,
        store_history: true,
    });
    assert!(after_shutdown.is_err());
}

#[test]
fn lsp_incremental_edit_lifecycle_open_change_save_cancel_close() {
    let mut tooling = ToolingEngine::default();
    let flow = read_fixture("conformance/lsp/edit_flow.txt");
    let uri = DocumentUri("file:///tmp/conformance_lsp.ditt".to_string());
    assert!(flow.contains("open=module Main where"));
    assert!(flow.contains("change=module Main where\\npostulate C : Cat"));
    assert!(flow.contains("cancel=42"));

    tooling
        .open_document(&uri, "module Main where\npostulate C : Cat")
        .unwrap();
    tooling
        .change_document(
            &uri,
            "module Main where\npostulate C : Cat\nid : (x : C) -> C = \\x. x",
        )
        .unwrap();
    tooling.save_document(&uri).unwrap();
    let diagnostics_before = tooling.diagnostics(&uri).unwrap();
    tooling.cancel(RequestId::from(42)).unwrap();
    tooling.close_document(&uri).unwrap();
    let diagnostics_after = tooling.diagnostics(&uri).unwrap();

    assert!(diagnostics_before.diagnostics.len() >= diagnostics_after.diagnostics.len());
}

#[test]
fn lsp_diagnostic_content_is_stable_without_order_dependence() {
    let mut tooling = ToolingEngine::default();
    let uri = DocumentUri("file:///tmp/sorted_lsp.ditt".to_string());
    tooling
        .open_document(
            &uri,
            "module Main where\npostulate C : Cat\nbad : (x : C) -> C =\nbad2 : (x : C) -> C =",
        )
        .unwrap();

    let first = tooling.diagnostics(&uri).unwrap();
    let second = tooling.diagnostics(&uri).unwrap();
    assert_eq!(
        diagnostic_signature_multiset(&first),
        diagnostic_signature_multiset(&second),
        "diagnostic content must remain stable regardless of emission order"
    );

    for d in &first.diagnostics {
        if let Some(span) = d.span {
            assert!(span.start <= span.end);
        }
    }
}
