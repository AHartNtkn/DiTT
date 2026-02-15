mod common;

use std::collections::BTreeSet;

use common::conformance::parse_csv;
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine, ToolingEngine};

#[derive(Debug, Clone)]
struct CaseRow {
    case_id: String,
    stage: String,
    expected_outcome: String,
}

fn case_rows() -> Vec<CaseRow> {
    let (header, rows) = parse_csv("conformance/modules/import_resolution_cases.csv");
    assert_eq!(header, vec!["case_id", "stage", "expected_outcome"]);
    rows.into_iter()
        .map(|row| {
            assert_eq!(row.len(), 3, "bad import resolution case row");
            CaseRow {
                case_id: row[0].clone(),
                stage: row[1].clone(),
                expected_outcome: row[2].clone(),
            }
        })
        .collect()
}

fn check_case_source(case_id: &str) -> &'static str {
    match case_id {
        "duplicate_import_aliases" => {
            "module Import.DuplicateAlias where\nimport A as X\nimport B as X\npostulate C : Cat\nx : C = x\n"
        }
        "overlapping_using_hiding" => {
            "module Import.Overlap where\nimport Std.Category using (id) hiding (id)\npostulate C : Cat\nx : C = x\n"
        }
        "invalid_renaming_source" => {
            "module Import.BadRenaming where\nimport Std.Category renaming (missing to id)\npostulate C : Cat\nx : C = x\n"
        }
        "ambiguous_qualified_reference" => {
            "module Import.AmbiguousQualified where\nimport A as X using (id)\nimport B as X using (id)\npostulate C : Cat\nu : C = X.id\n"
        }
        "shadowing_between_imports" => {
            "module Import.Shadowing where\nimport A using (id)\nimport B using (id)\npostulate C : Cat\nu : C = id\n"
        }
        "renaming_valid_alias" => {
            "module Import.RenamingOK where\nimport Std.Category renaming (id to cid)\npostulate C : Cat\nu : C = cid\n"
        }
        _ => panic!("check case source missing: {case_id}"),
    }
}

fn graph_case_modules(case_id: &str) -> Vec<ModuleText> {
    match case_id {
        "import_cycle_direct" => vec![
            ModuleText {
                name: "A".to_string(),
                source: "module A where\nimport B\n".to_string(),
            },
            ModuleText {
                name: "B".to_string(),
                source: "module B where\nimport A\n".to_string(),
            },
        ],
        "import_cycle_transitive" => vec![
            ModuleText {
                name: "A".to_string(),
                source: "module A where\nimport B\n".to_string(),
            },
            ModuleText {
                name: "B".to_string(),
                source: "module B where\nimport C\n".to_string(),
            },
            ModuleText {
                name: "C".to_string(),
                source: "module C where\nimport A\n".to_string(),
            },
        ],
        "import_acyclic_chain" | "incremental_dependents" => vec![
            ModuleText {
                name: "A".to_string(),
                source: "module A where\nimport B\n".to_string(),
            },
            ModuleText {
                name: "B".to_string(),
                source: "module B where\nimport C\n".to_string(),
            },
            ModuleText {
                name: "C".to_string(),
                source: "module C where\npostulate X : Cat\n".to_string(),
            },
        ],
        _ => panic!("graph case source missing: {case_id}"),
    }
}

#[test]
fn import_resolution_case_matrix_is_complete_and_unique() {
    let rows = case_rows();
    assert!(!rows.is_empty());

    let mut seen = BTreeSet::new();
    let expected = [
        "duplicate_import_aliases",
        "overlapping_using_hiding",
        "invalid_renaming_source",
        "ambiguous_qualified_reference",
        "shadowing_between_imports",
        "renaming_valid_alias",
        "import_cycle_direct",
        "import_cycle_transitive",
        "import_acyclic_chain",
        "incremental_dependents",
    ]
    .into_iter()
    .collect::<BTreeSet<_>>();

    for row in rows {
        assert!(seen.insert(row.case_id.clone()), "duplicate case row");
        assert!(expected.contains(row.case_id.as_str()));
        assert!(matches!(row.stage.as_str(), "check" | "graph"));
        assert!(matches!(row.expected_outcome.as_str(), "accept" | "reject"));
    }
    assert_eq!(seen, expected.into_iter().map(str::to_string).collect());
}

#[test]
fn import_resolution_cases_enforce_accept_reject_contracts() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let tooling = ToolingEngine::default();
    for row in case_rows() {
        match row.stage.as_str() {
            "check" => {
                let source = check_case_source(&row.case_id);
                let parsed = syntax.parse_module(source).unwrap();
                match row.expected_outcome.as_str() {
                    "accept" => {
                        let typed = semantics.elaborate_module(&parsed).unwrap();
                        assert!(!typed.declarations.is_empty());
                    }
                    "reject" => {
                        let err = semantics.elaborate_module(&parsed).unwrap_err();
                        let bundle = err.into_diagnostics();
                        assert!(!bundle.diagnostics.is_empty());
                    }
                    _ => panic!("unsupported expected outcome"),
                }
            }
            "graph" => {
                let modules = graph_case_modules(&row.case_id);
                let graph = tooling.build_graph(&modules).unwrap();
                match row.expected_outcome.as_str() {
                    "accept" => {
                        assert!(
                            !graph.has_cycle(),
                            "case {} expected acyclic graph but cycle detected",
                            row.case_id
                        );
                    }
                    "reject" => {
                        assert!(
                            graph.has_cycle(),
                            "case {} expected cycle but graph is acyclic",
                            row.case_id
                        );
                    }
                    _ => panic!("unsupported expected outcome"),
                }
            }
            _ => panic!("unsupported stage"),
        }
    }
}
