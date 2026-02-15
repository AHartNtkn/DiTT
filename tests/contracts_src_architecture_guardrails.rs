use std::fs;
use std::path::{Path, PathBuf};

fn collect_rs_files(root: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_rs_files(&path, out);
            continue;
        }
        if path.extension().and_then(|s| s.to_str()) == Some("rs") {
            out.push(path);
        }
    }
}

#[test]
fn src_layout_avoids_test_process_artifact_naming_and_coupling() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let src = root.join("src");

    let mut files = Vec::new();
    collect_rs_files(&src, &mut files);
    assert!(!files.is_empty());

    let banned_path_tokens = ["contract", "stub", "fallback", "red_phase", "test"];
    let banned_source_tokens = [
        "ditt_lang::contract",
        "ditt_lang::stub",
        "ditt_lang::platform",
        "crate::contract",
        "crate::stub",
        "crate::platform",
    ];

    let mut path_violations = Vec::new();
    let mut source_violations = Vec::new();

    for file in files {
        let rel = file
            .strip_prefix(&root)
            .unwrap()
            .to_string_lossy()
            .to_string();
        let rel_lower = rel.to_ascii_lowercase();
        for token in banned_path_tokens {
            if rel_lower.contains(token) {
                path_violations.push(format!("{rel} contains banned token '{token}'"));
            }
        }

        let body = fs::read_to_string(&file).unwrap();
        for token in banned_source_tokens {
            if body.contains(token) {
                source_violations.push(format!("{rel} contains banned import token '{token}'"));
            }
        }
        if body.contains("tests/") || body.contains("conformance/") {
            source_violations.push(format!(
                "{rel} references test/conformance corpus paths in implementation"
            ));
        }
    }

    assert!(
        path_violations.is_empty(),
        "src path architecture violations: {path_violations:?}"
    );
    assert!(
        source_violations.is_empty(),
        "src source architecture violations: {source_violations:?}"
    );
}

#[test]
fn runtime_is_split_into_subsystem_engines() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let runtime = root.join("src").join("runtime");

    assert!(
        runtime.join("syntax.rs").exists(),
        "src/runtime/syntax.rs must exist"
    );
    assert!(
        runtime.join("semantics.rs").exists(),
        "src/runtime/semantics.rs must exist"
    );
    assert!(
        runtime.join("tooling.rs").exists(),
        "src/runtime/tooling.rs must exist"
    );
    assert!(
        !runtime.join("kernel.rs").exists(),
        "src/runtime/kernel.rs must NOT exist after subsystem split"
    );

    let syntax_body = fs::read_to_string(runtime.join("syntax.rs")).unwrap();
    assert!(
        syntax_body.contains("pub struct SyntaxEngine"),
        "src/runtime/syntax.rs must define SyntaxEngine"
    );

    let semantics_body = fs::read_to_string(runtime.join("semantics.rs")).unwrap();
    assert!(
        semantics_body.contains("pub struct SemanticEngine"),
        "src/runtime/semantics.rs must define SemanticEngine"
    );

    let tooling_body = fs::read_to_string(runtime.join("tooling.rs")).unwrap();
    assert!(
        tooling_body.contains("pub struct ToolingEngine"),
        "src/runtime/tooling.rs must define ToolingEngine"
    );
}

#[test]
fn each_engine_implements_only_its_traits() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let runtime = root.join("src").join("runtime");

    let syntax_body = fs::read_to_string(runtime.join("syntax.rs")).unwrap();
    let semantics_body = fs::read_to_string(runtime.join("semantics.rs")).unwrap();
    let tooling_body = fs::read_to_string(runtime.join("tooling.rs")).unwrap();

    // SyntaxEngine implements syntax traits
    for trait_name in ["Lexer", "Parser", "Formatter", "AstEquivalence"] {
        let token = format!("impl {trait_name} for SyntaxEngine");
        assert!(
            syntax_body.contains(&token),
            "SyntaxEngine must implement {trait_name}"
        );
    }

    // SemanticEngine implements semantics traits
    for trait_name in [
        "TypeChecker",
        "VarianceChecker",
        "Normalizer",
        "Evaluator",
        "DerivationArtifacts",
    ] {
        let token = format!("impl {trait_name} for SemanticEngine");
        assert!(
            semantics_body.contains(&token),
            "SemanticEngine must implement {trait_name}"
        );
    }

    // ToolingEngine implements tooling traits
    for trait_name in [
        "ModuleSystem",
        "Cli",
        "Repl",
        "NotebookKernel",
        "LanguageServer",
    ] {
        let token = format!("impl {trait_name} for ToolingEngine");
        assert!(
            tooling_body.contains(&token),
            "ToolingEngine must implement {trait_name}"
        );
    }

    // No engine implements traits from another subsystem
    for trait_name in [
        "TypeChecker",
        "Normalizer",
        "Evaluator",
        "ModuleSystem",
        "Cli",
    ] {
        let token = format!("impl {trait_name} for SyntaxEngine");
        assert!(
            !syntax_body.contains(&token),
            "SyntaxEngine must NOT implement {trait_name} (wrong subsystem)"
        );
    }
    for trait_name in ["Lexer", "Parser", "Formatter", "ModuleSystem", "Cli"] {
        let token = format!("impl {trait_name} for SemanticEngine");
        assert!(
            !semantics_body.contains(&token),
            "SemanticEngine must NOT implement {trait_name} (wrong subsystem)"
        );
    }
    for trait_name in ["Lexer", "Parser", "TypeChecker", "Normalizer"] {
        let token = format!("impl {trait_name} for ToolingEngine");
        assert!(
            !tooling_body.contains(&token),
            "ToolingEngine must NOT implement {trait_name} (wrong subsystem)"
        );
    }
}

#[test]
fn no_monolithic_kernel_struct() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let runtime = root.join("src").join("runtime");

    let mut rs_files = Vec::new();
    collect_rs_files(&runtime, &mut rs_files);

    for file in rs_files {
        let body = fs::read_to_string(&file).unwrap();
        let rel = file
            .strip_prefix(&root)
            .unwrap()
            .to_string_lossy()
            .to_string();
        assert!(
            !body.contains("struct Kernel"),
            "{rel} must not contain a monolithic Kernel struct"
        );
    }
}
