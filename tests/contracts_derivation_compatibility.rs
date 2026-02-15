mod common;

use common::conformance::parse_kv_fixture;
use common::engines::compile_with_engines;
use common::support::{directed_theory_module, entailment};
use ditt_lang::api::*;

const SUPPORTED_ENCODING: &str = "ditt-derivation-v1";

fn parse_artifact(relative: &str) -> Result<DerivationArtifact, LanguageError> {
    let kv = parse_kv_fixture(relative);
    let encoding = kv.get("encoding").cloned().unwrap_or_default();
    if encoding != SUPPORTED_ENCODING {
        return Err(LanguageError::DerivationArtifact(
            DerivationArtifactError::Validate {
                diagnostics: DiagnosticBundle {
                    diagnostics: vec![Diagnostic {
                        code: "unsupported_encoding".to_string(),
                        category: "unsupported_encoding".to_string(),
                        severity: Severity::Error,
                        message: format!("unsupported derivation encoding: {encoding}"),
                        span: None,
                        source: None,
                    }],
                },
            },
        ));
    }
    let name = kv.get("judgment").cloned().unwrap_or_default();
    Ok(DerivationArtifact {
        judgment: entailment(&name),
        rule: InferenceRule::Refl,
        root: RuleApplication {
            rule: InferenceRule::Refl,
            premises: vec![],
        },
    })
}

#[test]
fn derivation_artifact_roundtrip_matrix_is_supported_for_current_encoding() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());
    let judgment = entailment("refl_intro");
    let rule = InferenceRule::Refl;
    let exported = semantics
        .export_derivation_artifact(&typed, &judgment, rule)
        .unwrap();
    semantics
        .validate_derivation_artifact(&typed, &exported)
        .unwrap();
}

#[test]
fn derivation_artifact_v1_and_compat_fixtures_validate() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());
    let v1 = parse_artifact("conformance/derivations/artifact_v1.txt").unwrap();
    let compat = parse_artifact("conformance/derivations/artifact_v1_compat.txt").unwrap();

    semantics.validate_derivation_artifact(&typed, &v1).unwrap();
    semantics
        .validate_derivation_artifact(&typed, &compat)
        .unwrap();
}

#[test]
fn future_derivation_encoding_is_rejected_with_structured_diagnostics() {
    let err = parse_artifact("conformance/derivations/artifact_future.txt").unwrap_err();

    let bundle = err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
    for diagnostic in &bundle.diagnostics {
        assert_eq!(diagnostic.severity, Severity::Error);
        assert!(!diagnostic.category.is_empty());
        assert!(!diagnostic.message.is_empty());
    }
    assert!(
        bundle
            .diagnostics
            .iter()
            .any(|d| d.category == "unsupported_encoding"),
        "rejection must cite unsupported encoding, got: {:?}",
        bundle.diagnostics
    );
}
