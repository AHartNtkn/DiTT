use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

#[derive(Debug, Clone)]
struct CoverageRow {
    clause_id: String,
    contract_id: String,
    positive_fixture: String,
    negative_fixture: String,
    negative_stage: String,
}

fn coverage_rows() -> (Vec<String>, Vec<CoverageRow>) {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let body = fs::read_to_string(root.join("docs").join("SURFACE_SYNTAX_COVERAGE.csv")).unwrap();
    let mut lines = body.lines().filter(|line| !line.trim().is_empty());
    let header = lines
        .next()
        .unwrap_or_default()
        .split(',')
        .map(|s| s.trim().to_string())
        .collect::<Vec<_>>();

    let rows = lines
        .map(|line| {
            let cols = line
                .split(',')
                .map(|s| s.trim().to_string())
                .collect::<Vec<_>>();
            assert_eq!(cols.len(), 5, "bad surface syntax coverage row: {line}");
            CoverageRow {
                clause_id: cols[0].clone(),
                contract_id: cols[1].clone(),
                positive_fixture: cols[2].clone(),
                negative_fixture: cols[3].clone(),
                negative_stage: cols[4].clone(),
            }
        })
        .collect::<Vec<_>>();

    (header, rows)
}

fn expected_clause_ids() -> BTreeSet<&'static str> {
    [
        "module_header",
        "local_modules",
        "import_basic",
        "import_alias",
        "import_clauses",
        "reserved_words",
        "unicode_identifiers",
        "identifier_digit_start",
        "one_line_definition",
        "duplicate_top_level",
        "lambda_forms",
        "arrow_forms",
        "directed_hom_notation",
        "refl_term",
        "directed_j_eliminator",
        "end_coend_proof_operators",
        "opposite_notation",
        "tuple_projection",
        "let_forms",
        "let_chaining",
        "end_coend_quantifiers",
        "comments",
        "precedence_projection_application",
        "precedence_product_arrow",
        "arrow_right_associativity",
        "implicit_named_args",
        "binder_grouping",
        "no_where_blocks",
        "top_shared_bottom_forbidden",
        "annotated_patterns",
    ]
    .into_iter()
    .collect()
}

#[test]
fn surface_syntax_coverage_rows_are_complete_unique_and_well_formed() {
    let (header, rows) = coverage_rows();
    assert_eq!(
        header,
        vec![
            "clause_id",
            "contract_id",
            "positive_fixture",
            "negative_fixture",
            "negative_stage"
        ]
    );

    let expected = expected_clause_ids();
    assert_eq!(rows.len(), expected.len());

    let mut seen = BTreeSet::new();
    for row in rows {
        assert!(seen.insert(row.clause_id.clone()), "duplicate clause_id");
        assert!(expected.contains(row.clause_id.as_str()));
        assert!(matches!(row.negative_stage.as_str(), "parse" | "check"));
        assert!(!row.contract_id.is_empty());
        assert!(!row.positive_fixture.is_empty());
        assert!(!row.negative_fixture.is_empty());
    }
}

#[test]
fn surface_syntax_coverage_links_are_live() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let (_header, rows) = coverage_rows();

    for row in rows {
        let positive_path = root.join("tests").join(&row.positive_fixture);
        let negative_path = root.join("tests").join(&row.negative_fixture);
        assert!(positive_path.exists(), "missing positive fixture");
        assert!(negative_path.exists(), "missing negative fixture");

        let (path, symbol) = row
            .contract_id
            .split_once("::")
            .unwrap_or((row.contract_id.as_str(), ""));
        assert!(!symbol.is_empty(), "missing contract function symbol");

        let full_path = root.join(path);
        assert!(full_path.exists(), "missing contract file");
        let body = fs::read_to_string(full_path).unwrap();
        assert!(body.contains(symbol), "missing contract function symbol");
    }
}
