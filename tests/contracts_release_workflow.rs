use ditt_lang::api::*;
use ditt_lang::runtime::ToolingEngine;
use std::collections::BTreeMap;

#[test]
fn release_workflow_init_check_repl_notebook_lsp_is_coherent() {
    let mut tooling = ToolingEngine::default();

    let source = "module Main where\npostulate C : Cat\nt : (x : C) -> C = \\x. x\n";
    let cli = tooling
        .invoke(&CliInvocation {
            args: vec!["check".to_string(), "--json".to_string()],
            stdin: source.to_string(),
            env: BTreeMap::new(),
        })
        .unwrap();
    assert_eq!(cli.exit_code, 0);

    let session = tooling.start_session().unwrap();
    let _ = tooling.submit(session, ":load Main").unwrap();
    let _ = tooling.submit(session, "t").unwrap();

    let kernel_info = tooling.kernel_info().unwrap();
    assert!(!kernel_info.language_name.is_empty());
    let _ = tooling
        .execute(&ExecuteRequest {
            session,
            code: "t".to_string(),
            silent: false,
            store_history: true,
        })
        .unwrap();

    let uri = DocumentUri("file:///tmp/release_main.ditt".to_string());
    tooling.open_document(&uri, source).unwrap();
    let _ = tooling.diagnostics(&uri).unwrap();
}
