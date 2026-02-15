use std::fs;
use std::path::PathBuf;

fn has_test_marker(path: &PathBuf) -> bool {
    let body = fs::read_to_string(path).unwrap_or_default();
    body.contains("#[test]") || body.contains("proptest!")
}

#[test]
fn every_test_matrix_row_has_at_least_one_executable_test_target() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let body = fs::read_to_string(root.join("docs").join("TEST_MATRIX.md")).unwrap();

    for raw in body.lines() {
        let line = raw.trim();
        if !line.starts_with('|') {
            continue;
        }
        if line.contains("| Area | Owner | Primary Contracts | Pass Criteria |") {
            continue;
        }
        if line.contains("|---|---|---|---|") {
            continue;
        }

        let cols = line
            .trim_matches('|')
            .split('|')
            .map(|s| s.trim())
            .collect::<Vec<_>>();
        if cols.len() != 4 {
            continue;
        }

        let area = cols[0];
        let contracts = cols[2];
        let mut found = false;

        for token in contracts.split(',').map(|s| s.trim().trim_matches('`')) {
            if !(token.starts_with("tests/") && token.ends_with(".rs")) {
                continue;
            }
            let path = root.join(token);
            if path.exists() && has_test_marker(&path) {
                found = true;
                break;
            }
        }

        assert!(
            found,
            "TEST_MATRIX row must reference at least one executable test target: {area}"
        );
    }
}
