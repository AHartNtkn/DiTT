mod common;

use common::conformance::{parse_csv, read_fixture};
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine, ToolingEngine};

fn has_named_declaration(source: &str, name: &str) -> bool {
    source.lines().any(|raw| {
        let line = raw.trim_start();
        if line.starts_with("postulate ") {
            return line
                .trim_start_matches("postulate ")
                .split_whitespace()
                .next()
                == Some(name);
        }
        let has_prefix = line.starts_with(name)
            && line[name.len()..]
                .chars()
                .next()
                .map(|c| c == ' ' || c == '(' || c == ':')
                .unwrap_or(false);
        has_prefix && line.contains(':')
    })
}

fn stdlib_module_source(module: &str) -> String {
    match module {
        "Std.Category" => read_fixture("conformance/stdlib/category_core.ditt"),
        "Std.Functor" => read_fixture("conformance/stdlib/functor_core.ditt"),
        "Std.EndCoend" => read_fixture("conformance/stdlib/end_coend_core.ditt"),
        other => panic!("unknown stdlib module in api lock: {other}"),
    }
}

#[test]
fn stdlib_required_module_registry_is_complete_and_unique() {
    let (header, rows) = parse_csv("conformance/stdlib/required_modules.csv");
    assert_eq!(header, vec!["module"]);
    assert!(!rows.is_empty());

    let mut names = std::collections::BTreeSet::new();
    for row in rows {
        assert_eq!(row.len(), 1);
        assert!(
            names.insert(row[0].clone()),
            "duplicate stdlib module {}",
            row[0]
        );
    }
}

#[test]
fn stdlib_api_lockfile_is_complete_and_consistent_with_required_modules() {
    let (required_header, required_rows) = parse_csv("conformance/stdlib/required_modules.csv");
    assert_eq!(required_header, vec!["module"]);
    let required_modules = required_rows
        .into_iter()
        .map(|row| {
            assert_eq!(row.len(), 1);
            row[0].clone()
        })
        .collect::<std::collections::BTreeSet<_>>();

    let (header, rows) = parse_csv("conformance/stdlib/api_lock.csv");
    assert_eq!(header, vec!["module", "export", "signature"]);
    assert!(!rows.is_empty());

    let mut seen = std::collections::BTreeSet::new();
    let mut covered_modules = std::collections::BTreeSet::new();
    for row in rows {
        assert_eq!(row.len(), 3, "bad lockfile row");
        let module = row[0].clone();
        let export = row[1].clone();
        let signature = row[2].clone();

        assert!(
            required_modules.contains(&module),
            "lockfile references unknown module: {module}"
        );
        assert!(!export.is_empty(), "lockfile export is empty");
        assert!(!signature.is_empty(), "lockfile signature is empty");
        assert!(
            seen.insert((module.clone(), export.clone())),
            "duplicate lockfile export {module}.{export}"
        );
        covered_modules.insert(module);
    }

    assert_eq!(
        covered_modules, required_modules,
        "every required stdlib module must appear in api lockfile"
    );
}

#[test]
fn stdlib_modules_parse_and_typecheck() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    for fixture in [
        "conformance/stdlib/category_core.ditt",
        "conformance/stdlib/functor_core.ditt",
        "conformance/stdlib/end_coend_core.ditt",
    ] {
        let source = read_fixture(fixture);
        let parsed = syntax.parse_module(&source).unwrap();
        let typed = semantics.elaborate_module(&parsed).unwrap();
        assert!(!typed.declarations.is_empty());
    }
}

#[test]
fn stdlib_modules_form_an_acyclic_import_graph() {
    let tooling = ToolingEngine::default();
    let modules = vec![
        ModuleText {
            name: "Std.Category".to_string(),
            source: read_fixture("conformance/stdlib/category_core.ditt"),
        },
        ModuleText {
            name: "Std.Functor".to_string(),
            source: "module Std.Functor where\nimport Std.Category".to_string(),
        },
        ModuleText {
            name: "Std.EndCoend".to_string(),
            source: "module Std.EndCoend where\nimport Std.Category".to_string(),
        },
    ];
    let graph = tooling.build_graph(&modules).unwrap();
    assert!(
        !graph.has_cycle(),
        "stdlib modules must form an acyclic import graph"
    );
}

#[test]
fn stdlib_api_lock_exports_exist_in_module_surfaces() {
    let (header, rows) = parse_csv("conformance/stdlib/api_lock.csv");
    assert_eq!(header, vec!["module", "export", "signature"]);

    for row in rows {
        assert_eq!(row.len(), 3, "bad stdlib api lock row");
        let module = &row[0];
        let export = &row[1];
        let source = stdlib_module_source(module);
        assert!(
            has_named_declaration(&source, export),
            "stdlib lock export '{module}.{export}' must exist in module surface text"
        );
    }
}
