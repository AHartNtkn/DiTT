mod common;

use common::engines::compile_with_engines;
use common::support::invocation;
use ditt_lang::api::*;
use ditt_lang::runtime::ToolingEngine;
use serde_json::Value;

fn parse_json(response: &CliResponse) -> Value {
    let raw = response
        .json
        .as_ref()
        .expect("run/check --json must emit machine-readable payload");
    serde_json::from_str(raw).expect("cli json must be valid")
}

fn normalize_rendering(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn notebook_execute_result_repr(reply: &ExecuteReply) -> Option<String> {
    reply.events.iter().find_map(|event| match event {
        NotebookEvent::ExecuteResult { repr } => Some(repr.clone()),
        _ => None,
    })
}

#[test]
fn run_normalize_semantics_agree_with_normalizer_api() {
    let source = r#"
module Main where
postulate C : Cat
id : (x : C) -> C = \x. x
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let tooling = ToolingEngine::default();
    let api_nf = semantics.normalize_term(&typed, &Expr::var("id")).unwrap();

    let cli = tooling
        .invoke(&invocation(&["run", "--normalize", "id", "--json"], source))
        .unwrap();
    assert_eq!(cli.exit_code, 0);
    let json = parse_json(&cli);
    assert_eq!(json.get("status").and_then(Value::as_str), Some("ok"));
    let nf_str = api_nf.structure().to_string();
    assert_eq!(
        json.get("normal_form").and_then(Value::as_str),
        Some(nf_str.as_str())
    );
}

#[test]
fn run_entry_requires_module_that_checks_successfully() {
    let tooling = ToolingEngine::default();
    let source = r#"
module Main where
postulate C : Cat
main : (x : C) -> C = \x. x
"#;
    let check = tooling
        .invoke(&invocation(&["check", "--json"], source))
        .unwrap();
    let run = tooling
        .invoke(&invocation(
            &["run", "--entry", "Main.main", "--json"],
            source,
        ))
        .unwrap();

    assert_eq!(check.exit_code, 0);
    assert_eq!(run.exit_code, 0);
    let check_json = parse_json(&check);
    assert_eq!(check_json.get("status").and_then(Value::as_str), Some("ok"));
    assert!(check_json.get("diagnostics").is_some());

    let run_json = parse_json(&run);
    assert_eq!(run_json.get("status").and_then(Value::as_str), Some("ok"));
    assert!(run_json.get("value").is_some());
}

#[test]
fn run_normalize_is_semantically_aligned_across_api_cli_repl_and_notebook() {
    let source = r#"
module Main where
postulate C : Cat
id : (x : C) -> C = \x. x
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let mut tooling = ToolingEngine::default();
    let api_nf = semantics.normalize_term(&typed, &Expr::var("id")).unwrap();

    let cli = tooling
        .invoke(&invocation(&["run", "--normalize", "id", "--json"], source))
        .unwrap();
    assert_eq!(cli.exit_code, 0);
    let cli_json = parse_json(&cli);
    let cli_nf = cli_json
        .get("normal_form")
        .and_then(Value::as_str)
        .expect("run --normalize must include normal_form");
    assert_eq!(
        normalize_rendering(&api_nf.structure().to_string()),
        normalize_rendering(cli_nf)
    );

    let session = tooling.start_session().unwrap();
    let _ = tooling.submit(session, source).unwrap();
    let repl = tooling.submit(session, "id").unwrap();
    assert_eq!(
        normalize_rendering(&api_nf.structure().to_string()),
        normalize_rendering(&repl.rendered)
    );

    let _ = tooling
        .execute(&ExecuteRequest {
            session,
            code: source.to_string(),
            silent: false,
            store_history: true,
        })
        .unwrap();
    let notebook = tooling
        .execute(&ExecuteRequest {
            session,
            code: "id".to_string(),
            silent: false,
            store_history: true,
        })
        .unwrap();
    assert_eq!(notebook.status, ExecutionStatus::Ok);
    let repr = notebook_execute_result_repr(&notebook)
        .expect("notebook execution must emit execute_result for successful query");
    assert_eq!(
        normalize_rendering(&api_nf.structure().to_string()),
        normalize_rendering(&repr)
    );
}

#[test]
fn run_entry_is_semantically_aligned_across_api_cli_repl_and_notebook() {
    let source = r#"
module Main where
postulate C : Cat
main : (x : C) -> C = \x. x
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let mut tooling = ToolingEngine::default();
    let api = semantics.evaluate_term(&typed, &Expr::var("main")).unwrap();

    let cli = tooling
        .invoke(&invocation(
            &["run", "--entry", "Main.main", "--json"],
            source,
        ))
        .unwrap();
    assert_eq!(cli.exit_code, 0);
    let cli_json = parse_json(&cli);
    let cli_value = cli_json
        .get("value")
        .and_then(Value::as_str)
        .expect("run --entry must include value");
    assert_eq!(
        normalize_rendering(&api.value),
        normalize_rendering(cli_value)
    );

    let session = tooling.start_session().unwrap();
    let _ = tooling.submit(session, source).unwrap();
    let repl = tooling.submit(session, "main").unwrap();
    assert_eq!(
        normalize_rendering(&api.value),
        normalize_rendering(&repl.rendered)
    );

    let _ = tooling
        .execute(&ExecuteRequest {
            session,
            code: source.to_string(),
            silent: false,
            store_history: true,
        })
        .unwrap();
    let notebook = tooling
        .execute(&ExecuteRequest {
            session,
            code: "main".to_string(),
            silent: false,
            store_history: true,
        })
        .unwrap();
    assert_eq!(notebook.status, ExecutionStatus::Ok);
    let repr = notebook_execute_result_repr(&notebook)
        .expect("notebook execution must emit execute_result for successful query");
    assert_eq!(normalize_rendering(&api.value), normalize_rendering(&repr));
}
