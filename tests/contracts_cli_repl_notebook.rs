mod common;

use common::support::invocation;
use ditt_lang::api::*;
use ditt_lang::runtime::ToolingEngine;
use serde_json::Value;

fn parse_json(response: &CliResponse) -> Value {
    let raw = response
        .json
        .as_ref()
        .expect("cli --json mode must emit json payload");
    serde_json::from_str(raw).expect("cli json payload must be valid")
}

#[test]
fn cli_check_returns_zero_for_valid_module_and_nonzero_for_invalid_module() {
    let tooling = ToolingEngine::default();

    let ok = tooling
        .invoke(&invocation(
            &["check"],
            "module Main where\npostulate C : Cat\nid : (x : C) -> C = \\x. x\n",
        ))
        .unwrap();
    let err = tooling
        .invoke(&invocation(
            &["check"],
            "module Main where\npostulate C : Cat\nid : (x : C) -> C =",
        ))
        .unwrap();

    assert_eq!(ok.exit_code, 0);
    assert_ne!(err.exit_code, 0);
}

#[test]
fn cli_json_mode_emits_machine_readable_json_without_ansi_sequences() {
    let tooling = ToolingEngine::default();
    let response = tooling
        .invoke(&invocation(
            &["check", "--json"],
            "module Main where\npostulate C : Cat\nid : (x : C) -> C = \\x. x\n",
        ))
        .unwrap();

    let json = parse_json(&response);
    assert!(json.get("status").is_some());
    assert!(json.get("diagnostics").is_some());
    assert!(!response.stdout.contains('\u{1b}'));
    assert!(!response.stderr.contains('\u{1b}'));
}

#[test]
fn cli_run_entrypoint_evaluates_and_renders_value() {
    let tooling = ToolingEngine::default();
    let source = "module Main where\npostulate C : Cat\nmain : (x : C) -> C = \\x. x\n";
    let response = tooling
        .invoke(&invocation(
            &["run", "--entry", "Main.main", "--json"],
            source,
        ))
        .unwrap();

    assert_eq!(response.exit_code, 0);
    assert!(!response.stdout.trim().is_empty());
    let json = parse_json(&response);
    assert_eq!(json.get("status").and_then(Value::as_str), Some("ok"));
    assert!(json.get("value").is_some());
}

#[test]
fn cli_run_normalize_named_term_emits_normal_form() {
    let tooling = ToolingEngine::default();
    let source = "module Main where\npostulate C : Cat\nid : (x : C) -> C = \\x. x\n";
    let response = tooling
        .invoke(&invocation(&["run", "--normalize", "id", "--json"], source))
        .unwrap();

    assert_eq!(response.exit_code, 0);
    assert!(!response.stdout.trim().is_empty());
    let json = parse_json(&response);
    assert_eq!(json.get("status").and_then(Value::as_str), Some("ok"));
    assert!(json.get("normal_form").is_some());
}

#[test]
fn repl_persists_definitions_across_submissions() {
    let mut tooling = ToolingEngine::default();
    let session = tooling.start_session().unwrap();

    let _ = tooling.submit(session, "postulate C : Cat").unwrap();
    let _ = tooling
        .submit(session, "id : (x : C) -> C = \\x. x")
        .unwrap();
    let result = tooling.submit(session, "id").unwrap();

    assert!(result.diagnostics.diagnostics.is_empty());
    assert!(!result.rendered.is_empty());
}

#[test]
fn repl_completion_is_deterministic() {
    let mut tooling = ToolingEngine::default();
    let session = tooling.start_session().unwrap();

    for prefix in ["", "i", "id", "trans", "foo"] {
        let first = Repl::complete(&tooling, session, prefix).unwrap();
        let second = Repl::complete(&tooling, session, prefix).unwrap();
        assert_eq!(first, second);
    }
}

#[test]
fn repl_sessions_have_distinct_ids() {
    let mut tooling = ToolingEngine::default();
    let session_a = tooling.start_session().unwrap();
    let session_b = tooling.start_session().unwrap();
    assert_ne!(
        session_a, session_b,
        "each start_session call must return a distinct SessionId"
    );
}

#[test]
fn repl_invalid_syntax_produces_diagnostics() {
    let mut tooling = ToolingEngine::default();
    let session = tooling.start_session().unwrap();
    let result = tooling.submit(session, "broken (x :").unwrap();
    assert!(
        !result.diagnostics.diagnostics.is_empty(),
        "submitting invalid syntax must produce at least one diagnostic"
    );
}

#[test]
fn repl_sessions_are_isolated() {
    let mut tooling = ToolingEngine::default();
    let session_a = tooling.start_session().unwrap();
    let session_b = tooling.start_session().unwrap();

    let _ = tooling.submit(session_a, "postulate C : Cat").unwrap();
    let _ = tooling
        .submit(session_a, "id_a : (x : C) -> C = \\x. x")
        .unwrap();

    let result = tooling.submit(session_b, "id_a").unwrap();
    assert!(
        !result.diagnostics.diagnostics.is_empty(),
        "definition from session A must not be visible in session B"
    );
}

#[test]
fn notebook_kernel_exposes_expected_metadata() {
    let tooling = ToolingEngine::default();
    let info = tooling.kernel_info().unwrap();

    assert_eq!(info.file_extension, ".ditt");
    assert_eq!(info.mimetype, "text/x-ditt");
    assert!(!info.language_name.is_empty());
}

#[test]
fn notebook_execution_count_is_monotonic() {
    let mut tooling = ToolingEngine::default();
    let mut last = 0u64;
    let snippets = [
        "postulate C : Cat",
        "id : (x : C) -> C = \\x. x",
        "id",
        "C",
        "id",
    ];

    for code in snippets {
        let reply = tooling
            .execute(&ExecuteRequest {
                session: 1,
                code: code.to_string(),
                silent: false,
                store_history: true,
            })
            .unwrap();
        assert!(reply.execution_count > last);
        last = reply.execution_count;
    }
}

#[test]
fn notebook_state_is_preserved_across_execute_requests() {
    let mut tooling = ToolingEngine::default();
    let _ = tooling
        .execute(&ExecuteRequest {
            session: 1,
            code: "postulate C : Cat".to_string(),
            silent: false,
            store_history: true,
        })
        .unwrap();
    let reply = tooling
        .execute(&ExecuteRequest {
            session: 1,
            code: "C".to_string(),
            silent: false,
            store_history: true,
        })
        .unwrap();

    assert_eq!(reply.status, ExecutionStatus::Ok);
    assert!(!reply.events.is_empty());
}
