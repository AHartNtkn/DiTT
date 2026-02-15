use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

#[derive(Debug, Clone)]
struct CliRow {
    command_id: String,
    args_pattern: String,
    contract_id: String,
}

fn cli_rows() -> Vec<CliRow> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let body = fs::read_to_string(root.join("docs").join("CLI_CONTRACT_COVERAGE.csv")).unwrap();
    let mut lines = body.lines().filter(|l| !l.trim().is_empty());
    let header = lines
        .next()
        .unwrap_or_default()
        .split(',')
        .map(|s| s.trim().to_string())
        .collect::<Vec<_>>();
    assert_eq!(header, vec!["command_id", "args_pattern", "contract_id"]);

    lines
        .map(|line| {
            let cols = line
                .split(',')
                .map(|s| s.trim().to_string())
                .collect::<Vec<_>>();
            assert_eq!(cols.len(), 3, "bad cli coverage row");
            CliRow {
                command_id: cols[0].clone(),
                args_pattern: cols[1].clone(),
                contract_id: cols[2].clone(),
            }
        })
        .collect()
}

fn assert_contract_link_exists(contract_id: &str) {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let (path, symbol) = contract_id.split_once("::").unwrap_or((contract_id, ""));
    assert!(!symbol.is_empty(), "missing contract symbol in id");

    let full_path = root.join(path);
    assert!(full_path.exists(), "contract file missing: {path}");
    let body = fs::read_to_string(full_path).unwrap();
    assert!(
        body.contains(&format!("fn {symbol}")),
        "missing contract fn"
    );
}

fn args_pattern_is_exercised(pattern: &str, corpus: &str) -> bool {
    pattern
        .split_whitespace()
        .all(|token| corpus.contains(&format!("\"{token}\"")))
}

#[test]
fn cli_contract_coverage_registry_is_complete_and_unique() {
    let rows = cli_rows();
    assert!(!rows.is_empty());

    let mut seen = BTreeSet::new();
    for row in &rows {
        assert!(seen.insert(row.command_id.clone()), "duplicate command id");
        assert!(!row.args_pattern.is_empty());
        assert_contract_link_exists(&row.contract_id);
    }

    let required = [
        "check",
        "check_human",
        "check_json",
        "build_human",
        "build_json",
        "fmt_check_human",
        "fmt_check_json",
        "run_entry_human",
        "run_entry_json",
        "run_normalize_human",
        "run_normalize_json",
        "repl_json",
        "lsp_stdio_json",
        "notebook_kernel_json",
        "unknown_command_json",
        "check_unknown_option_json",
        "run_missing_selector_json",
        "run_conflicting_selectors_json",
    ]
    .into_iter()
    .map(str::to_string)
    .collect::<BTreeSet<_>>();
    assert_eq!(seen, required, "cli command registry is incomplete");
}

#[test]
fn every_cli_args_pattern_is_exercised_by_executable_contracts() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let corpus = [
        fs::read_to_string(root.join("tests/contracts_cli_command_surface.rs")).unwrap(),
        fs::read_to_string(root.join("tests/contracts_cli_repl_notebook.rs")).unwrap(),
        fs::read_to_string(root.join("tests/contracts_surface_frontend_parity.rs")).unwrap(),
    ]
    .join("\n");

    for row in cli_rows() {
        assert!(
            args_pattern_is_exercised(&row.args_pattern, &corpus),
            "args pattern '{}' is not exercised",
            row.args_pattern
        );
    }
}
