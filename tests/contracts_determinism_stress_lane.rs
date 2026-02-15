mod common;

use std::path::PathBuf;

use common::conformance::read_fixture;
use common::fixtures::collect_ditt_fixture_paths;
use common::support::invocation;
use ditt_lang::api::*;
use ditt_lang::runtime::{SyntaxEngine, ToolingEngine};

fn seeded_permutation<T: Clone>(items: &[T], seed: u64) -> Vec<T> {
    let mut out = items.to_vec();
    let mut state = seed;
    for i in (1..out.len()).rev() {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        let j = (state as usize) % (i + 1);
        out.swap(i, j);
    }
    out
}

#[test]
fn randomized_repeat_runs_preserve_determinism_for_parser_cli_and_diagnostics() {
    let mut positives = collect_ditt_fixture_paths(
        &PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("conformance")
            .join("syntax")
            .join("positive"),
    );
    positives.sort();

    let mut negatives = collect_ditt_fixture_paths(
        &PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("conformance")
            .join("syntax")
            .join("negative"),
    );
    negatives.sort();

    assert!(!positives.is_empty() && !negatives.is_empty());

    for seed in 1..=5u64 {
        let syntax = SyntaxEngine::default();
        let tooling = ToolingEngine::default();

        for fixture in seeded_permutation(&positives, seed) {
            let source = read_fixture(&fixture);
            let p1 = syntax.parse_module(&source).unwrap();
            let p2 = syntax.parse_module(&source).unwrap();
            assert_eq!(p1, p2, "parse deterministic mismatch for {fixture}");

            let c1 = tooling
                .invoke(&invocation(&["check", "--json"], &source))
                .unwrap();
            let c2 = tooling
                .invoke(&invocation(&["check", "--json"], &source))
                .unwrap();
            assert_eq!(c1, c2, "cli deterministic mismatch for {fixture}");
        }

        let semantics = ditt_lang::runtime::SemanticEngine::default();
        for fixture in seeded_permutation(&negatives, seed ^ 0xA5A5_A5A5_A5A5_A5A5) {
            let source = read_fixture(&fixture);
            match syntax.parse_module(&source) {
                Err(e1) => {
                    // Parse-stage negative: verify parse error determinism.
                    let b1 = e1.into_diagnostics();
                    let b2 = syntax.parse_module(&source).unwrap_err().into_diagnostics();
                    assert_eq!(b1, b2, "recovery deterministic mismatch for {fixture}");
                }
                Ok(parsed) => {
                    // Check-stage negative: parses fine, must fail during elaboration.
                    let e1 = semantics
                        .elaborate_module(&parsed)
                        .unwrap_err()
                        .into_diagnostics();
                    let e2 = semantics
                        .elaborate_module(&parsed)
                        .unwrap_err()
                        .into_diagnostics();
                    assert_eq!(e1, e2, "elaboration deterministic mismatch for {fixture}");
                }
            }
        }
    }
}
