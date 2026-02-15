mod common;

use std::time::{Duration, Instant};

use common::engines::compile_module;
use common::support::directed_theory_module;
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine, ToolingEngine};

#[test]
#[ignore = "performance contract: run explicitly in CI perf job"]
fn parse_check_normalize_stays_within_budget_for_medium_module() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let source = directed_theory_module();

    let t0 = Instant::now();
    let parsed = syntax.parse_module(source).unwrap();
    let t1 = Instant::now();
    let typed = semantics.elaborate_module(&parsed).unwrap();
    let t2 = Instant::now();
    let _ = semantics
        .normalize_term(&typed, &Expr::var("refl"))
        .unwrap();
    let t3 = Instant::now();

    let parse_ms = (t1 - t0).as_millis();
    let check_ms = (t2 - t1).as_millis();
    let normalize_ms = (t3 - t2).as_millis();
    println!("PERF_METRIC metric=parse_ms value={parse_ms} budget=100");
    println!("PERF_METRIC metric=check_ms value={check_ms} budget=250");
    println!("PERF_METRIC metric=normalize_ms value={normalize_ms} budget=150");

    // Provisional target: 100ms parse budget assumes the directed_theory_module (~30 definitions)
    // represents a medium-sized module. Parsing is purely syntactic and should be dominated by
    // I/O rather than computation at this scale.
    assert!(t1 - t0 <= Duration::from_millis(100));
    // Provisional target: 250ms check budget accounts for full elaboration including
    // variance inference and directed cut analysis on the directed_theory_module.
    // Type-checking is the most expensive phase and gets the largest budget.
    assert!(t2 - t1 <= Duration::from_millis(250));
    // Provisional target: 150ms normalize budget covers beta-reduction of a single
    // already-elaborated term. Normalization traverses the term once and should be
    // proportional to term size, not module size.
    assert!(t3 - t2 <= Duration::from_millis(150));
}

#[test]
#[ignore = "performance contract: run explicitly in CI perf job"]
fn lsp_incremental_change_diagnostics_latency_budget() {
    let mut tooling = ToolingEngine::default();
    let uri = DocumentUri("file:///tmp/perf.ditt".to_string());
    tooling
        .open_document(&uri, directed_theory_module())
        .unwrap();

    let start = Instant::now();
    tooling
        .change_document(&uri, "module Perf where\nx : C\ny =")
        .unwrap();
    let _ = tooling.diagnostics(&uri).unwrap();
    let elapsed = start.elapsed();
    println!(
        "PERF_METRIC metric=lsp_incremental_diagnostics_ms value={} budget=100",
        elapsed.as_millis()
    );
    // Provisional target: 100ms LSP incremental budget. Incremental re-checking after a
    // single-line edit should not re-elaborate the entire module. The budget matches the
    // parse budget since incremental changes should do at most a re-parse plus localized
    // diagnostic collection.
    assert!(elapsed <= Duration::from_millis(100));
}

#[test]
#[ignore = "performance contract: run explicitly in CI perf job"]
fn cli_json_response_latency_budget() {
    let _ = compile_module(directed_theory_module());
    let tooling = ToolingEngine::default();
    let start = Instant::now();
    let _ = tooling
        .invoke(&CliInvocation {
            args: vec!["check".to_string(), "--json".to_string()],
            stdin: directed_theory_module().to_string(),
            env: std::collections::BTreeMap::new(),
        })
        .unwrap();
    let elapsed = start.elapsed();
    println!(
        "PERF_METRIC metric=cli_check_json_ms value={} budget=150",
        elapsed.as_millis()
    );
    // Provisional target: 150ms CLI budget covers full parse + check + JSON serialization
    // of the directed_theory_module. This is higher than the parse budget but lower than
    // parse + check combined because the CLI path may share cached intermediate results.
    assert!(elapsed <= Duration::from_millis(150));
}
