mod common;

use std::collections::BTreeSet;

use common::conformance::{
    canonical_severity, check_rejects_derive, nearest_derivation_rule, parse_judgment_rows,
    parse_kv_fixture, read_fixture,
};
use common::engines::compile_with_engines;
use common::support::entailment;
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};

fn assert_expected_categories_present(
    bundle: &DiagnosticBundle,
    expected_categories: &BTreeSet<String>,
    context: &str,
) {
    for expected_category in expected_categories {
        assert!(
            bundle
                .diagnostics
                .iter()
                .any(|d| d.category == *expected_category),
            "{context}: expected at least one diagnostic in category '{expected_category}'"
        );
    }
}

#[test]
fn invalid_rule_fixture_emits_expected_rejection_diagnostics() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let source = read_fixture("conformance/semantics/invalid_rules.ditt");
    let expected = parse_kv_fixture("conformance/semantics/invalid_rules.expect.diag");

    let parsed = syntax.parse_module(&source).unwrap();
    let bundle = semantics
        .elaborate_module(&parsed)
        .unwrap_err()
        .into_diagnostics();
    assert!(
        !bundle.diagnostics.is_empty(),
        "invalid rules fixture must emit at least one diagnostic"
    );
    let expected_categories = expected
        .get("categories")
        .unwrap()
        .split(',')
        .map(|s| s.trim().to_string())
        .collect::<BTreeSet<_>>();
    assert_expected_categories_present(
        &bundle,
        &expected_categories,
        "invalid_rules.expect.diag categories",
    );

    let expected_severities = expected
        .get("severities")
        .unwrap()
        .split(',')
        .map(|s| s.trim().to_string())
        .collect::<BTreeSet<_>>();
    for expected_severity in expected_severities {
        assert!(
            bundle
                .diagnostics
                .iter()
                .any(|d| canonical_severity(&d.severity) == expected_severity),
            "expected at least one diagnostic with severity '{expected_severity}'"
        );
    }
}

#[test]
fn negative_semantics_boundaries_are_not_derivable() {
    let module = read_fixture("conformance/semantics/negative_cases.ditt");
    let rows = parse_judgment_rows("conformance/semantics/negative_boundaries.csv");
    let (_syntax, semantics, typed) = compile_with_engines(&module);

    for row in rows {
        let rule = nearest_derivation_rule(&row.category);
        let result = semantics.derive(&typed, &entailment(&row.name), rule);
        assert!(
            result.is_err(),
            "negative boundary '{}' must be non-derivable (derive must return Err), but got Ok({:?})",
            row.name,
            result.unwrap()
        );
    }
}

fn assert_single_case_rejects_derive(source: &str, name: &str, category: InferenceRule) {
    check_rejects_derive(source, &[(name, category)], "TypeTheory");
}

#[test]
fn non_derivability_reason_no_applicable_rule_is_reported() {
    assert_single_case_rejects_derive(
        r#"
module Contracts.NonDerivabilityReason.NoApplicableRule where
postulate
  C : Cat
refl_probe (x : C) : x ->[C] x =
  refl x
"#,
        "refl_probe",
        InferenceRule::JRule,
    );
}

#[test]
fn non_derivability_reason_symmetry_violation_is_reported() {
    let module = read_fixture("conformance/semantics/negative_cases.ditt");
    assert_single_case_rejects_derive(&module, "symmetry_forbidden", InferenceRule::JRule);
}

#[test]
fn non_derivability_reason_symmetry_violation_is_reported_for_base_opposite_and_product_categories()
{
    check_rejects_derive(
        r#"
module Contracts.NonDerivabilityReason.SymmetryViolation.Contexts where
postulate
  C : Cat
  D : Cat
symmetry_forbidden_base (a : C) (b : C) (e : a ->[C] b) : b ->[C] a =
  e
symmetry_forbidden_op (a : C) (b : C) (e : a ->[C^] b) : b ->[C^] a =
  e
symmetry_forbidden_product (a : C) (a2 : C) (b : D) (b2 : D) (e : (a, b) ->[(C * D)] (a2, b2)) : (a2, b2) ->[(C * D)] (a, b) =
  e
"#,
        &[
            ("symmetry_forbidden_base", InferenceRule::JRule),
            ("symmetry_forbidden_op", InferenceRule::JRule),
            ("symmetry_forbidden_product", InferenceRule::JRule),
        ],
        "TypeTheory",
    );
}

#[test]
fn non_derivability_reason_directedness_violation_is_reported() {
    let module = read_fixture("conformance/semantics/negative_cases.ditt");
    assert_single_case_rejects_derive(&module, "unrestricted_cut_forbidden", InferenceRule::CutNat);
}

#[test]
fn non_derivability_reason_directedness_violation_is_reported_for_direct_dinatural_composition() {
    assert_single_case_rejects_derive(
        r#"
module Contracts.NonDerivabilityReason.DirectednessViolation.DinaturalComposition where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  R : (x : C) -> (y : C) -> Prop
  alpha : (z : C) -> P z z -> Q z z
  gamma : (z : C) -> Q z z -> R z z
compose_without_j (z : C) (p : P z z) : R z z =
  gamma z (alpha z p)
"#,
        "compose_without_j",
        InferenceRule::CutNat,
    );
}

#[test]
fn non_derivability_reason_variance_mismatch_is_reported() {
    assert_single_case_rejects_derive(
        r#"
module Contracts.NonDerivabilityReason.VarianceMismatch where
postulate
  C : Cat
P (x : C) : Prop =
  (y : C) -> ((x ->[C] y) -> (y ->[C] x))
probe (x : C) : P x =
  \y. \k. k
"#,
        "probe",
        InferenceRule::Var,
    );
}

#[test]
fn non_derivability_reason_type_mismatch_is_reported() {
    let module = read_fixture("conformance/semantics/negative_cases.ditt");
    assert_single_case_rejects_derive(&module, "refl_wrong", InferenceRule::Refl);
}

#[test]
fn type_mismatch_inline_negative() {
    let source = r#"
module Negative.TypeMismatch where
postulate
  C : Cat
  D : Cat

bad (x : C) : D = x
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);

    let result = semantics.derive(&typed, &entailment("bad"), InferenceRule::Var);
    assert!(
        result.is_err(),
        "type mismatch (C vs D) must produce a derivation error"
    );
    let diagnostics = result.unwrap_err().into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "type mismatch must produce TypeTheory diagnostics, got: {diagnostics:?}"
    );
}
