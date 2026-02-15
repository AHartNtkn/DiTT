use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;

use ditt_lang::api::*;
use ditt_lang::runtime::ToolingEngine;

fn snapshot_dir(path: &PathBuf) -> Vec<String> {
    let mut entries = fs::read_dir(path)
        .unwrap()
        .map(|e| e.unwrap().file_name().to_string_lossy().to_string())
        .collect::<Vec<_>>();
    entries.sort();
    entries
}

#[test]
fn cli_rejects_hostile_invocation_without_side_effects() {
    let tooling = ToolingEngine::default();
    let temp = PathBuf::from("/tmp/ditt_security_cli");
    let _ = fs::remove_dir_all(&temp);
    fs::create_dir_all(&temp).unwrap();
    fs::write(temp.join("sentinel.txt"), "keep").unwrap();
    let before = snapshot_dir(&temp);

    let mut env = BTreeMap::new();
    env.insert("DITT_WORKDIR".to_string(), temp.display().to_string());
    let err = tooling
        .invoke(&CliInvocation {
            args: vec!["check".to_string(), "--unsafe-eval".to_string()],
            stdin: "module M where\n".to_string(),
            env,
        })
        .unwrap_err();
    let after = snapshot_dir(&temp);

    assert_eq!(before, after);
    match err {
        err if !err.diagnostics().diagnostics.is_empty() => {}
        other => panic!("hostile invocation must be rejected with structured error: {other:?}"),
    }
}

#[test]
fn notebook_execution_rejects_unsafe_fs_or_network_primitives() {
    let mut tooling = ToolingEngine::default();
    let err = tooling
        .execute(&ExecuteRequest {
            session: 1,
            code: "open('/etc/passwd'); net.connect('example.com')".to_string(),
            silent: false,
            store_history: true,
        })
        .unwrap_err();

    match err {
        err if !err.diagnostics().diagnostics.is_empty() => {}
        other => panic!("unsafe notebook primitives must be blocked: {other:?}"),
    }
}

#[test]
fn lsp_requests_cannot_escape_workspace_via_uri_traversal() {
    let mut tooling = ToolingEngine::default();
    let err = tooling
        .open_document(
            &DocumentUri("file:///workspace/../../etc/passwd".to_string()),
            "module M",
        )
        .unwrap_err();
    match err {
        err if !err.diagnostics().diagnostics.is_empty() => {}
        other => panic!("uri traversal must be rejected: {other:?}"),
    }
}
