mod common;

use std::fs;
use std::path::PathBuf;

use common::conformance::parse_csv;

#[test]
fn paper_parity_rows_are_well_formed_and_linked_to_contracts() {
    let (header, rows) = parse_csv("conformance/semantics/paper_parity.csv");
    assert_eq!(
        header,
        vec!["section", "item", "contract_id", "status", "notes"]
    );

    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for row in rows {
        assert_eq!(row.len(), 5);
        let contract_id = &row[2];
        assert!(!contract_id.is_empty());
        let (path, symbol) = contract_id
            .split_once("::")
            .unwrap_or((contract_id.as_str(), ""));
        let full_path = root.join(path);
        assert!(full_path.exists(), "missing contract path: {path}");
        if !symbol.is_empty() {
            let body = fs::read_to_string(&full_path).unwrap();
            let needle = format!("fn {symbol}");
            assert!(
                body.contains(&needle),
                "missing contract function symbol: {contract_id}"
            );
        }
        assert!(matches!(row[3].as_str(), "covered" | "partial" | "missing"));
    }
}

#[test]
fn paper_parity_has_no_missing_rows() {
    let (_header, rows) = parse_csv("conformance/semantics/paper_parity.csv");
    assert!(
        rows.len() >= 32,
        "Expected at least 32 paper examples, found {}",
        rows.len()
    );
    let missing = rows
        .iter()
        .filter(|row| row.get(3).map(String::as_str) == Some("missing"))
        .count();
    assert_eq!(missing, 0, "paper parity still has missing coverage");
}
