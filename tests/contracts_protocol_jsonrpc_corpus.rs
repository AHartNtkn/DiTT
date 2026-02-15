use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use serde_json::Value;

fn collect_jsonrpc_transcripts(root: &Path, out: &mut Vec<String>) {
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_jsonrpc_transcripts(&path, out);
            continue;
        }
        let Some(name) = path.file_name().and_then(|s| s.to_str()) else {
            continue;
        };
        if !(name.starts_with("jsonrpc_") && name.ends_with(".jsonl")) {
            continue;
        }
        out.push(
            path.strip_prefix(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests"))
                .unwrap()
                .to_string_lossy()
                .to_string(),
        );
    }
}

fn id_key(id: &Value) -> String {
    if let Some(s) = id.as_str() {
        return format!("s:{s}");
    }
    if let Some(n) = id.as_i64() {
        return format!("i:{n}");
    }
    if let Some(u) = id.as_u64() {
        return format!("u:{u}");
    }
    panic!("json-rpc id must be string or number");
}

fn assert_text_document_position_params(params: &Value, context: &str) {
    let doc = params
        .get("textDocument")
        .and_then(Value::as_object)
        .expect(context);
    assert!(
        doc.get("uri").and_then(Value::as_str).is_some(),
        "missing textDocument.uri in {context}"
    );
    let pos = params
        .get("position")
        .and_then(Value::as_object)
        .expect(context);
    assert!(
        pos.get("line").and_then(Value::as_u64).is_some(),
        "missing position.line in {context}"
    );
    assert!(
        pos.get("character").and_then(Value::as_u64).is_some(),
        "missing position.character in {context}"
    );
}

fn assert_request_shape(method: &str, params: &Value, relative: &str, line_no: usize) {
    let context = format!("{relative}:{line_no}:{method}");
    match method {
        "initialize" => {
            assert!(
                params.get("capabilities").is_some(),
                "initialize request must include capabilities in {context}"
            );
        }
        "textDocument/hover" | "textDocument/definition" | "textDocument/completion" => {
            assert_text_document_position_params(params, &context);
        }
        "textDocument/didOpen" => {
            let doc = params
                .get("textDocument")
                .and_then(Value::as_object)
                .expect("didOpen must include textDocument object");
            assert!(doc.get("uri").and_then(Value::as_str).is_some());
            assert!(doc.get("text").and_then(Value::as_str).is_some());
            assert!(doc.get("version").and_then(Value::as_i64).is_some());
        }
        "textDocument/didChange" => {
            let doc = params
                .get("textDocument")
                .and_then(Value::as_object)
                .expect("didChange must include textDocument object");
            assert!(doc.get("uri").and_then(Value::as_str).is_some());
            assert!(doc.get("version").and_then(Value::as_i64).is_some());
            let changes = params
                .get("contentChanges")
                .and_then(Value::as_array)
                .expect("didChange must include contentChanges array");
            assert!(
                !changes.is_empty(),
                "didChange must include at least one edit"
            );
        }
        "kernel_info" => {
            assert!(
                params.as_object().is_some(),
                "kernel_info params must be an object"
            );
        }
        "execute_request" => {
            assert!(params.get("session").and_then(Value::as_str).is_some());
            assert!(params.get("code").and_then(Value::as_str).is_some());
            assert!(params.get("silent").and_then(Value::as_bool).is_some());
        }
        "complete_request" | "inspect_request" => {
            assert!(params.get("code").and_then(Value::as_str).is_some());
            assert!(params.get("cursor").and_then(Value::as_u64).is_some());
        }
        _ => {}
    }
}

fn assert_response_shape_for_method(method: &str, result: &Value, relative: &str, line_no: usize) {
    let context = format!("{relative}:{line_no}:{method}");
    match method {
        "initialize" => {
            assert!(
                result
                    .get("capabilities")
                    .and_then(Value::as_object)
                    .is_some(),
                "initialize response must include capabilities in {context}"
            );
        }
        "textDocument/hover" => {
            assert!(
                result.get("contents").and_then(Value::as_str).is_some(),
                "hover response must include textual contents in {context}"
            );
        }
        "textDocument/completion" => {
            assert!(
                result.get("items").and_then(Value::as_array).is_some(),
                "completion response must include items array in {context}"
            );
        }
        "kernel_info" => {
            assert!(
                result
                    .get("language_name")
                    .and_then(Value::as_str)
                    .is_some()
            );
            assert!(
                result
                    .get("file_extension")
                    .and_then(Value::as_str)
                    .is_some()
            );
        }
        "execute_request" => {
            assert!(result.get("status").and_then(Value::as_str).is_some());
            assert!(
                result
                    .get("execution_count")
                    .and_then(Value::as_u64)
                    .is_some()
            );
        }
        "complete_request" => {
            assert!(result.get("matches").and_then(Value::as_array).is_some());
            assert!(result.get("cursor_start").and_then(Value::as_u64).is_some());
            assert!(result.get("cursor_end").and_then(Value::as_u64).is_some());
        }
        "inspect_request" => {
            assert!(result.get("found").and_then(Value::as_bool).is_some());
            assert!(result.get("contents").and_then(Value::as_str).is_some());
            assert!(result.get("cursor_start").and_then(Value::as_u64).is_some());
            assert!(result.get("cursor_end").and_then(Value::as_u64).is_some());
        }
        _ => {}
    }
}

#[test]
fn protocol_jsonrpc_transcript_set_is_complete_and_nonempty() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("conformance");
    let mut files = Vec::new();
    collect_jsonrpc_transcripts(&root, &mut files);
    files.sort();

    let expected = [
        "conformance/lsp/jsonrpc_cancelled_request.jsonl",
        "conformance/lsp/jsonrpc_incremental_completion_success.jsonl",
        "conformance/lsp/jsonrpc_initialize_hover_success.jsonl",
        "conformance/lsp/jsonrpc_invalid_params_and_method_not_found.jsonl",
        "conformance/notebook/jsonrpc_complete_and_inspect_success.jsonl",
        "conformance/notebook/jsonrpc_execute_error_and_cancel.jsonl",
        "conformance/notebook/jsonrpc_execute_success.jsonl",
        "conformance/notebook/jsonrpc_invalid_params_and_method_not_found.jsonl",
    ]
    .into_iter()
    .map(str::to_string)
    .collect::<Vec<_>>();
    assert_eq!(files, expected);
}

#[test]
fn protocol_jsonrpc_transcripts_obey_ordering_id_cancellation_and_error_envelope_contracts() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("conformance");
    let mut files = Vec::new();
    collect_jsonrpc_transcripts(&root, &mut files);
    files.sort();

    for relative in files {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join(&relative);
        let body = fs::read_to_string(path).unwrap();

        let mut req_index = BTreeMap::<String, usize>::new();
        let mut resp_index = BTreeMap::<String, usize>::new();
        let mut resp_is_error = BTreeMap::<String, bool>::new();
        let mut req_method = BTreeMap::<String, String>::new();
        let mut cancelled = BTreeSet::<String>::new();
        let mut saw_initialize_request = false;
        let mut saw_initialize_response = false;

        for (idx, raw) in body.lines().enumerate() {
            let line_no = idx + 1;
            if raw.trim().is_empty() {
                continue;
            }
            let msg: Value = serde_json::from_str(raw).expect("invalid json line");
            let obj = msg.as_object().expect("json-rpc line must be object");
            assert_eq!(
                obj.get("jsonrpc").and_then(|v| v.as_str()),
                Some("2.0"),
                "jsonrpc version mismatch in {relative}:{line_no}"
            );
            assert!(
                obj.get("role").and_then(|v| v.as_str()).is_some(),
                "missing role in {relative}:{line_no}"
            );

            let has_method = obj.contains_key("method");
            let has_id = obj.contains_key("id");
            let has_result = obj.contains_key("result");
            let has_error = obj.contains_key("error");

            if has_method && has_id {
                let method = obj["method"].as_str().expect("method must be string");
                let key = id_key(&obj["id"]);
                assert!(
                    !req_index.contains_key(&key),
                    "duplicate request id in {relative}:{line_no}"
                );
                assert!(
                    !resp_index.contains_key(&key),
                    "request id reused after response in {relative}:{line_no}"
                );
                req_index.insert(key, idx);
                assert!(!method.is_empty());
                let params = obj.get("params").cloned().unwrap_or(Value::Null);
                assert_request_shape(method, &params, &relative, line_no);
                if method == "initialize" {
                    saw_initialize_request = true;
                }
                req_method.insert(id_key(&obj["id"]), method.to_string());
                continue;
            }

            if has_method && !has_id {
                let method = obj["method"].as_str().expect("method must be string");
                assert!(!method.is_empty());
                let params = obj.get("params").cloned().unwrap_or(Value::Null);
                assert_request_shape(method, &params, &relative, line_no);
                if method == "$/cancelRequest" {
                    let cancel_id = obj
                        .get("params")
                        .and_then(|v| v.get("id"))
                        .expect("cancel request must carry params.id");
                    let key = id_key(cancel_id);
                    assert!(
                        req_index.contains_key(&key),
                        "cancel references unknown request id in {relative}:{line_no}"
                    );
                    cancelled.insert(key);
                }
                continue;
            }

            if has_id && !has_method {
                assert!(
                    has_result ^ has_error,
                    "response must have result xor error"
                );
                let key = id_key(&obj["id"]);
                let req_at = *req_index
                    .get(&key)
                    .expect("response references unknown request id");
                let request_method = req_method
                    .get(&key)
                    .expect("response id must correspond to tracked request method");
                assert!(idx > req_at, "response appears before request");
                assert!(
                    !resp_index.contains_key(&key),
                    "duplicate response id in {relative}:{line_no}"
                );
                resp_index.insert(key.clone(), idx);
                resp_is_error.insert(key.clone(), has_error);

                if has_error {
                    let err = obj["error"].as_object().expect("error must be object");
                    assert!(err.get("code").and_then(|v| v.as_i64()).is_some());
                    let message = err.get("message").and_then(|v| v.as_str()).unwrap_or("");
                    assert!(
                        !message.trim().is_empty(),
                        "error message must be non-empty"
                    );
                } else {
                    assert_response_shape_for_method(
                        request_method,
                        obj.get("result").unwrap_or(&Value::Null),
                        &relative,
                        line_no,
                    );
                    if request_method == "initialize" {
                        saw_initialize_response = true;
                    }
                }
                continue;
            }

            panic!("invalid json-rpc envelope in {relative}:{line_no}");
        }

        for id in cancelled {
            assert!(
                resp_is_error.get(&id).copied().unwrap_or(false),
                "cancelled request must terminate with error response in {relative}"
            );
        }
        if relative.contains("/lsp/") {
            assert!(
                saw_initialize_request && saw_initialize_response,
                "lsp transcript must include initialize handshake in {relative}"
            );
        }
    }
}
