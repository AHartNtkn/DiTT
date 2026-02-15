mod common;

use common::engines::compile_with_engines;
use common::support::{directed_theory_module, entailment};
use ditt_lang::api::*;
use ditt_lang::runtime::SemanticEngine;

#[test]
fn derivation_artifacts_are_exportable_normalizable_and_validatable() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());
    let judgment = entailment("comp_assoc");
    let rule = InferenceRule::CutNat;

    let artifact = semantics
        .export_derivation_artifact(&typed, &judgment, rule)
        .unwrap();
    semantics
        .validate_derivation_artifact(&typed, &artifact)
        .unwrap();
}

#[test]
fn malformed_derivation_artifact_is_rejected_with_structured_diagnostics() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());
    let malformed = DerivationArtifact {
        judgment: entailment("symmetry"),
        rule: InferenceRule::Refl,
        root: RuleApplication {
            rule: InferenceRule::Refl,
            premises: vec![],
        },
    };

    let err = semantics
        .validate_derivation_artifact(&typed, &malformed)
        .unwrap_err();
    let bundle = err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
}

#[test]
fn derivation_artifact_for_derivable_judgment_normalizes_and_validates() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());
    let judgment = entailment("refl_intro");
    let rule = InferenceRule::Refl;

    semantics
        .derive(&typed, &judgment, rule)
        .expect("refl_intro must be derivable before exporting derivation artifacts");

    let artifact = semantics
        .export_derivation_artifact(&typed, &judgment, rule)
        .unwrap();
    semantics
        .validate_derivation_artifact(&typed, &artifact)
        .unwrap();
}

fn assert_derivation_validation_rejects_with_diagnostics(
    semantics: &SemanticEngine,
    typed: &TypedModule,
    artifact: &DerivationArtifact,
) {
    let err = semantics
        .validate_derivation_artifact(typed, artifact)
        .unwrap_err();
    let bundle = err.into_diagnostics();
    assert!(
        !bundle.diagnostics.is_empty(),
        "malformed derivation artifact must return diagnostics"
    );
    assert!(
        bundle
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == Severity::Error),
        "derivation rejection diagnostics must include at least one error-severity entry"
    );
    assert!(
        bundle.diagnostics.iter().any(|diagnostic| {
            diagnostic.category == "Artifacts"
                || diagnostic.category == "TypeTheory"
                || diagnostic
                    .category
                    .to_ascii_lowercase()
                    .contains("derivation")
        }),
        "derivation rejection diagnostics must be categorized as artifact/type-theory related"
    );
}

#[test]
fn malformed_derivation_missing_required_premises_is_rejected() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());
    let artifact = DerivationArtifact {
        judgment: entailment("comp_assoc"),
        rule: InferenceRule::CutNat,
        root: RuleApplication {
            rule: InferenceRule::CutNat,
            premises: vec![],
        },
    };

    assert_derivation_validation_rejects_with_diagnostics(&semantics, &typed, &artifact);
}

#[test]
fn malformed_derivation_with_wrong_rule_for_judgment_is_rejected() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());
    let artifact = DerivationArtifact {
        judgment: entailment("refl_intro"),
        rule: InferenceRule::Refl,
        root: RuleApplication {
            rule: InferenceRule::CutNat,
            premises: vec![RuleApplication {
                rule: InferenceRule::Refl,
                premises: vec![],
            }],
        },
    };

    assert_derivation_validation_rejects_with_diagnostics(&semantics, &typed, &artifact);
}
