use std::fs;
use std::path::PathBuf;

#[test]
fn language_error_surface_is_explicit_and_forbids_generic_buckets() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let foundation = root.join("src").join("api").join("foundation.rs");
    let body = fs::read_to_string(&foundation).unwrap();

    assert!(body.contains("pub enum LanguageError"));

    let required_variants = [
        "Syntax(",
        "StaticSemantics(",
        "DynamicSemantics(",
        "ModuleSystem(",
        "Interaction(",
        "DerivationArtifact(",
    ];
    for variant in required_variants {
        assert!(
            body.contains(variant),
            "language error API is missing required variant token: {variant}"
        );
    }

    let forbidden_tokens = [
        "ContractViolation(",
        "Diagnostics(",
        "LanguageError::Diagnostics",
        "LanguageError::ContractViolation",
    ];
    for forbidden in forbidden_tokens {
        assert!(
            !body.contains(forbidden),
            "generic or removed error bucket token present in API: {forbidden}"
        );
    }
}

#[test]
fn lsp_query_errors_carry_structured_diagnostics() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let foundation = root.join("src").join("api").join("foundation.rs");
    let body = fs::read_to_string(&foundation).unwrap();

    for token in [
        "pub enum LspError",
        "Diagnostics { diagnostics: DiagnosticBundle }",
        "Hover { diagnostics: DiagnosticBundle }",
        "Definition { diagnostics: DiagnosticBundle }",
        "Completions { diagnostics: DiagnosticBundle }",
        "RenameSymbol { diagnostics: DiagnosticBundle }",
        "SemanticTokens { diagnostics: DiagnosticBundle }",
        "InteractionError::Lsp(err) => err.diagnostics()",
    ] {
        assert!(
            body.contains(token),
            "interaction error API missing structured diagnostics token: {token}"
        );
    }
}

#[test]
fn interaction_error_is_split_by_protocol() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let foundation = root.join("src").join("api").join("foundation.rs");
    let body = fs::read_to_string(&foundation).unwrap();

    for token in [
        "pub enum InteractionError",
        "CliInvoke { diagnostics: DiagnosticBundle }",
        "Repl(ReplError)",
        "Notebook(NotebookError)",
        "Lsp(LspError)",
    ] {
        assert!(
            body.contains(token),
            "interaction error API missing protocol-split token: {token}"
        );
    }
}

#[test]
fn diagnostics_extraction_is_total_for_interaction_errors() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let foundation = root.join("src").join("api").join("foundation.rs");
    let body = fs::read_to_string(&foundation).unwrap();

    for token in [
        "impl_diagnostics!(ReplError",
        "pub fn diagnostics(&self) -> &DiagnosticBundle",
        "pub fn into_diagnostics(self) -> DiagnosticBundle",
        "impl_diagnostics!(NotebookError",
        "impl_diagnostics!(LspError",
        "impl InteractionError",
    ] {
        assert!(
            body.contains(token),
            "interaction diagnostics API missing total-extraction token: {token}"
        );
    }

    for forbidden in ["Option<&DiagnosticBundle>", "Option<DiagnosticBundle>"] {
        assert!(
            !body.contains(forbidden),
            "interaction diagnostics API must not use optional diagnostics: {forbidden}"
        );
    }
}

#[test]
fn static_semantics_error_has_variance_variants() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let foundation = root.join("src").join("api").join("foundation.rs");
    let body = fs::read_to_string(&foundation).unwrap();

    for token in [
        "ComputeVariance { diagnostics: DiagnosticBundle }",
        "AllVariances { diagnostics: DiagnosticBundle }",
    ] {
        assert!(
            body.contains(token),
            "StaticSemanticsError missing variance variant token: {token}"
        );
    }
}

#[test]
fn repl_error_covers_full_session_lifecycle() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let foundation = root.join("src").join("api").join("foundation.rs");
    let body = fs::read_to_string(&foundation).unwrap();

    for token in [
        "Start { diagnostics: DiagnosticBundle }",
        "Submit { diagnostics: DiagnosticBundle }",
        "Complete { diagnostics: DiagnosticBundle }",
        "End { diagnostics: DiagnosticBundle }",
    ] {
        assert!(
            body.contains(token),
            "ReplError missing session lifecycle variant token: {token}"
        );
    }
}
