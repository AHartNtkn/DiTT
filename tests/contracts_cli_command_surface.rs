mod common;

use common::support::invocation;
use ditt_lang::api::*;
use ditt_lang::runtime::ToolingEngine;
use serde_json::Value;

fn parse_json(response: &CliResponse) -> Value {
    let raw = response
        .json
        .as_ref()
        .expect("cli --json mode must emit machine-readable payload");
    serde_json::from_str(raw).expect("cli json payload must be valid")
}

#[test]
fn cli_build_command_surface_returns_machine_readable_response() {
    let tooling = ToolingEngine::default();
    let response = tooling
        .invoke(&invocation(
            &["build", "--json"],
            "module Main where\npostulate C : Cat\nid : (x : C) -> C = \\x. x\n",
        ))
        .unwrap();
    assert!(response.json.is_some());
    assert!(!response.stdout.contains('\u{1b}'));
    assert!(!response.stderr.contains('\u{1b}'));
}

#[test]
fn cli_build_command_surface_human_mode_is_textual_and_not_json() {
    let tooling = ToolingEngine::default();
    let response = tooling
        .invoke(&invocation(
            &["build"],
            "module Main where\npostulate C : Cat\nid : (x : C) -> C = \\x. x\n",
        ))
        .unwrap();
    assert_eq!(response.exit_code, 0);
    assert!(response.json.is_none());
}

#[test]
fn cli_fmt_command_surface_emits_formatted_program() {
    let tooling = ToolingEngine::default();
    let response = tooling
        .invoke(&invocation(
            &["fmt", "--check", "--json"],
            "module Main where\npostulate C : Cat\nid:(x : C)->C=\\x.x",
        ))
        .unwrap();
    assert!(response.json.is_some());
    assert!(!response.stderr.contains('\u{1b}'));
}

#[test]
fn cli_fmt_command_surface_human_mode_is_textual_and_not_json() {
    let tooling = ToolingEngine::default();
    let response = tooling
        .invoke(&invocation(
            &["fmt", "--check"],
            "module Main where\npostulate C : Cat\nid:(x : C)->C=\\x.x",
        ))
        .unwrap();
    assert_ne!(response.exit_code, 0);
    assert!(response.json.is_none());
}

#[test]
fn cli_repl_command_surface_is_invocable() {
    let tooling = ToolingEngine::default();
    let response = tooling
        .invoke(&invocation(&["repl", "--json"], ":type id"))
        .unwrap();
    assert!(response.json.is_some());
    assert!(!response.stderr.contains('\u{1b}'));
}

#[test]
fn cli_lsp_command_surface_is_invocable() {
    let tooling = ToolingEngine::default();
    let response = tooling
        .invoke(&invocation(&["lsp", "--stdio", "--json"], ""))
        .unwrap();
    assert!(response.json.is_some());
    assert!(!response.stderr.contains('\u{1b}'));
}

#[test]
fn cli_notebook_command_surface_is_invocable() {
    let tooling = ToolingEngine::default();
    let response = tooling
        .invoke(&invocation(
            &["notebook", "kernel", "--json"],
            "kernel_info",
        ))
        .unwrap();
    assert!(response.json.is_some());
    assert!(!response.stderr.contains('\u{1b}'));
}

#[test]
fn cli_unknown_command_returns_machine_readable_usage_error() {
    let tooling = ToolingEngine::default();
    let response = tooling
        .invoke(&invocation(&["bogus", "--json"], ""))
        .unwrap();
    assert_ne!(response.exit_code, 0);
    let json = parse_json(&response);
    assert_eq!(json.get("status").and_then(Value::as_str), Some("error"));
    assert!(json.get("diagnostics").is_some() || json.get("error").is_some());
}

#[test]
fn cli_check_rejects_unknown_option_with_structured_error() {
    let tooling = ToolingEngine::default();
    let response = tooling
        .invoke(&invocation(&["check", "--json", "--bogus-option"], ""))
        .unwrap();
    assert_ne!(response.exit_code, 0);
    let json = parse_json(&response);
    assert_eq!(json.get("status").and_then(Value::as_str), Some("error"));
    assert!(json.get("diagnostics").is_some() || json.get("error").is_some());
}

#[test]
fn cli_run_rejects_missing_selector_between_entry_and_normalize() {
    let tooling = ToolingEngine::default();
    let source = "module Main where\npostulate C : Cat\nmain : (x : C) -> C = \\x. x\n";
    let response = tooling
        .invoke(&invocation(&["run", "--json"], source))
        .unwrap();
    assert_ne!(response.exit_code, 0);
    let json = parse_json(&response);
    assert_eq!(json.get("status").and_then(Value::as_str), Some("error"));
    assert!(json.get("diagnostics").is_some() || json.get("error").is_some());
}

#[test]
fn cli_run_rejects_conflicting_entry_and_normalize_selectors() {
    let tooling = ToolingEngine::default();
    let source = "module Main where\npostulate C : Cat\nmain : (x : C) -> C = \\x. x\n";
    let response = tooling
        .invoke(&invocation(
            &[
                "run",
                "--entry",
                "Main.main",
                "--normalize",
                "main",
                "--json",
            ],
            source,
        ))
        .unwrap();
    assert_ne!(response.exit_code, 0);
    let json = parse_json(&response);
    assert_eq!(json.get("status").and_then(Value::as_str), Some("error"));
    assert!(json.get("diagnostics").is_some() || json.get("error").is_some());
}

#[test]
fn cli_check_human_mode_omits_machine_payload() {
    let tooling = ToolingEngine::default();
    let source = "module Main where\npostulate C : Cat\nmain : (x : C) -> C = \\x. x\n";
    let response = tooling.invoke(&invocation(&["check"], source)).unwrap();
    assert!(response.json.is_none());
    assert_eq!(response.exit_code, 0);
}

#[test]
fn cli_run_entry_human_mode_emits_textual_value_and_omits_machine_payload() {
    let tooling = ToolingEngine::default();
    let source = "module Main where\npostulate C : Cat\nmain : (x : C) -> C = \\x. x\n";
    let response = tooling
        .invoke(&invocation(&["run", "--entry", "Main.main"], source))
        .unwrap();
    assert_eq!(response.exit_code, 0);
    assert!(!response.stdout.trim().is_empty());
    assert!(response.json.is_none());
}

#[test]
fn cli_run_normalize_human_mode_emits_textual_normal_form_and_omits_machine_payload() {
    let tooling = ToolingEngine::default();
    let source = "module Main where\npostulate C : Cat\nid : (x : C) -> C = \\x. x\n";
    let response = tooling
        .invoke(&invocation(&["run", "--normalize", "id"], source))
        .unwrap();
    assert_eq!(response.exit_code, 0);
    assert!(!response.stdout.trim().is_empty());
    assert!(response.json.is_none());
}
