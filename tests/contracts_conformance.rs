mod common;

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use common::conformance::*;
use common::engines::compile_with_engines;
use common::support::{assert_format_contracts, entailment};
use ditt_lang::api::*;
use ditt_lang::runtime::{SyntaxEngine, ToolingEngine};
use serde_json::Value;

fn parse_args(line: &str) -> Vec<String> {
    line.split_whitespace().map(|s| s.to_string()).collect()
}

fn parse_cli_json(response: &CliResponse) -> Value {
    let raw = response
        .json
        .as_ref()
        .expect("cli contract requires --json payload");
    serde_json::from_str(raw).expect("cli json must be valid")
}

fn has_named_definition(source: &str, name: &str) -> bool {
    source.lines().any(|raw| {
        let line = raw.trim_start();
        line.starts_with(name)
            && line[name.len()..]
                .chars()
                .next()
                .map(|c| c == ' ' || c == '(')
                .unwrap_or(false)
            && line.contains(':')
            && line.contains('=')
    })
}

#[test]
fn conformance_parser_valid_fixture_is_semantics_preserving_and_well_formatted() {
    let syntax = SyntaxEngine::default();
    let source = read_fixture("conformance/parser/valid_identity.ditt");

    let original = syntax.parse_module(&source).unwrap();
    let formatted = syntax.format_module(&original).unwrap();
    assert_format_contracts(&formatted);
    let reparsed = syntax.parse_module(&formatted).unwrap();
    let equivalent = syntax
        .alpha_equivalent_modules(&original, &reparsed)
        .unwrap();

    assert!(equivalent);
}

#[test]
fn conformance_judgment_rows_match_expected_outcomes() {
    let module = read_fixture("conformance/semantics/directed_core.ditt");
    let rows = parse_judgment_rows("conformance/semantics/judgments.csv");

    for row in &rows {
        assert!(
            has_named_definition(&module, &row.name),
            "missing concrete definition for judgment row {} in directed_core.ditt",
            row.name
        );
    }

    let (_syntax, semantics, typed) = compile_with_engines(&module);
    for row in rows {
        let rule = nearest_derivation_rule(&row.category);
        let result = semantics.derive(&typed, &entailment(&row.name), rule);
        let got_derivable = result.is_ok();
        assert_eq!(
            got_derivable, row.expected_derivable,
            "judgment {}: expected derivable={}, got derivable={}",
            row.name, row.expected_derivable, got_derivable
        );
    }
}

#[test]
fn conformance_negative_boundaries_match_expected_outcomes() {
    let module = read_fixture("conformance/semantics/negative_cases.ditt");
    let rows = parse_judgment_rows("conformance/semantics/negative_boundaries.csv");

    for row in &rows {
        assert!(
            has_named_definition(&module, &row.name),
            "missing concrete definition for negative boundary {} in negative_cases.ditt",
            row.name
        );
    }

    let (_syntax, semantics, typed) = compile_with_engines(&module);
    for row in rows {
        let rule = nearest_derivation_rule(&row.category);
        let result = semantics.derive(&typed, &entailment(&row.name), rule);
        let got_derivable = result.is_ok();
        assert_eq!(
            got_derivable, row.expected_derivable,
            "negative boundary {}: expected derivable={}, got derivable={}",
            row.name, row.expected_derivable, got_derivable
        );
    }
}

#[test]
fn conformance_judgment_registries_cover_all_inference_rule_kinds() {
    let mut seen = BTreeSet::new();
    for row in parse_judgment_rows("conformance/semantics/judgments.csv") {
        seen.insert(
            nearest_derivation_rule(&row.category)
                .paper_rule_id()
                .to_string(),
        );
    }
    for row in parse_judgment_rows("conformance/semantics/negative_boundaries.csv") {
        seen.insert(
            nearest_derivation_rule(&row.category)
                .paper_rule_id()
                .to_string(),
        );
    }

    // The expected set contains InferenceRule paper_rule_id values that the CSV fixture
    // files must collectively reference. RuleCategory values are mapped to their nearest
    // InferenceRule via nearest_derivation_rule, so multiple categories may collapse to the
    // same InferenceRule. This set reflects the minimum coverage requirement.
    let expected = [
        "Figure11.Refl",
        "Figure11.JRule",
        "Figure11.CutNat",
        "Figure11.Var",
        "Figure11.Wk",
        "Figure11.Prod",
        "Figure16.EndElim",
        "Figure16.CoendElim",
        "Figure16.EndIntro",
    ]
    .into_iter()
    .map(String::from)
    .collect::<BTreeSet<_>>();

    assert!(
        seen.is_superset(&expected),
        "CSV registries must cover at least the expected InferenceRule categories.\n\
         Missing: {:?}",
        expected.difference(&seen).collect::<Vec<_>>()
    );
}

#[test]
fn judgment_category_csv_tokens_parse_and_display_consistently() {
    // With the RuleCategory enum, all category tokens map to one of:
    // Derivation(InferenceRule), Check(CheckJudgment), Equational, Variance, or MetaProperty.
    // This test verifies that:
    // 1. Every token used in the CSV files parses without panic
    // 2. All InferenceRule paper_rule_ids are unique strings

    // Verify all CSV tokens parse successfully
    let csv_tokens = [
        "Refl",
        "JComp",
        "JRule",
        "CutNat",
        "SymmetryNotDerivable",
        "DirectedCutRestriction",
        "SubstitutionPreservesTyping",
        "RenamingPreservesTyping",
        "WeakeningAdmissible",
        "ExchangeAdmissible",
        "SubjectReduction",
        "FunctorMapIdentity",
        "FunctorMapComposition",
        "TransportIdentity",
        "TransportComposition",
        "EndCoendAdjunction",
        "Yoneda",
        "CoYoneda",
        "FubiniExchange",
        "OpInvolution",
        "BetaLaw",
        "EtaLaw",
        "CongruenceForAllConstructors",
        "NormalizationCoherence",
    ];
    for token in &csv_tokens {
        let parsed = parse_rule_category(token);
        let key = nearest_derivation_rule(&parsed).paper_rule_id();
        assert!(
            !key.is_empty(),
            "CSV token '{token}' must produce a non-empty category key"
        );
    }

    // Verify all InferenceRule Display values are unique
    let all_rules = [
        InferenceRule::Var,
        InferenceRule::Wk,
        InferenceRule::Top,
        InferenceRule::Idx,
        InferenceRule::Contr,
        InferenceRule::Prod,
        InferenceRule::Exp,
        InferenceRule::End,
        InferenceRule::Coend,
        InferenceRule::CutDin,
        InferenceRule::CutNat,
        InferenceRule::Refl,
        InferenceRule::JRule,
        InferenceRule::EndIntro,
        InferenceRule::EndElim,
        InferenceRule::CoendElim,
        InferenceRule::CoendIntro,
    ];
    let mut display_set = BTreeSet::new();
    for rule in &all_rules {
        let display = rule.to_string();
        assert!(
            display_set.insert(display.clone()),
            "InferenceRule Display collision: {display}"
        );
    }
}

#[test]
fn conformance_cli_valid_fixture_satisfies_machine_contract() {
    let tooling = ToolingEngine::default();
    let args = parse_args(&read_fixture("conformance/cli/check_valid.args"));
    let stdin = read_fixture("conformance/cli/check_valid.stdin");
    let expected = parse_kv_fixture("conformance/cli/check_valid.expect");

    let response = tooling
        .invoke(&CliInvocation {
            args,
            stdin,
            env: BTreeMap::new(),
        })
        .unwrap();

    assert_eq!(
        response.exit_code,
        expected.get("exit_code").unwrap().parse::<i32>().unwrap()
    );
    assert_eq!(
        response.stdout.is_empty(),
        expected.get("stdout_empty") == Some(&"true".to_string())
    );
    assert_eq!(
        response.stderr.is_empty(),
        expected.get("stderr_empty") == Some(&"true".to_string())
    );

    let json_required = expected.get("json_required") == Some(&"true".to_string());
    assert_eq!(response.json.is_some(), json_required);
    let json = parse_cli_json(&response);
    assert_eq!(
        json.get("status").and_then(Value::as_str),
        Some(expected.get("status").unwrap().as_str())
    );
    assert!(
        json.get("diagnostics").and_then(Value::as_array).is_some(),
        "check --json payload must include diagnostics array"
    );
}

#[test]
fn conformance_cli_invalid_fixture_satisfies_machine_contract() {
    let tooling = ToolingEngine::default();
    let args = parse_args(&read_fixture("conformance/cli/check_valid.args"));
    let stdin = read_fixture("conformance/cli/check_invalid.stdin");
    let expected = parse_kv_fixture("conformance/cli/check_invalid.expect");

    let response = tooling
        .invoke(&CliInvocation {
            args,
            stdin,
            env: BTreeMap::new(),
        })
        .unwrap();

    assert_eq!(
        response.exit_code,
        expected.get("exit_code").unwrap().parse::<i32>().unwrap()
    );
    assert_eq!(
        response.stdout.is_empty(),
        expected.get("stdout_empty") == Some(&"true".to_string())
    );
    assert_eq!(
        response.stderr.is_empty(),
        expected.get("stderr_empty") == Some(&"true".to_string())
    );

    let json_required = expected.get("json_required") == Some(&"true".to_string());
    assert_eq!(response.json.is_some(), json_required);
    let json = parse_cli_json(&response);
    assert_eq!(
        json.get("status").and_then(Value::as_str),
        Some(expected.get("status").unwrap().as_str())
    );
    assert!(
        json.get("diagnostics").and_then(Value::as_array).is_some(),
        "check --json payload must include diagnostics array"
    );
}

#[test]
fn conformance_cli_outputs_are_byte_stable_across_repeated_runs() {
    let tooling = ToolingEngine::default();
    let args = parse_args(&read_fixture("conformance/cli/check_valid.args"));
    let stdin = read_fixture("conformance/cli/check_valid.stdin");
    let invocation = CliInvocation {
        args,
        stdin,
        env: BTreeMap::new(),
    };

    let first = tooling.invoke(&invocation).unwrap();
    let second = tooling.invoke(&invocation).unwrap();
    assert_eq!(first, second);
}
