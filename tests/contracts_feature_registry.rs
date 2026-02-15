use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

fn assert_contract_link_exists(contract_id: &str) {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let (path, symbol) = contract_id.split_once("::").unwrap_or((contract_id, ""));
    assert!(
        !symbol.is_empty(),
        "contract id missing symbol: {contract_id}"
    );
    let full_path = root.join(path);
    assert!(full_path.exists(), "missing contract file: {path}");
    let body = fs::read_to_string(full_path).unwrap();
    assert!(
        body.contains(&format!("fn {symbol}")) || body.contains(symbol),
        "missing contract symbol: {contract_id}"
    );
}

fn load_surface_clause_ids() -> BTreeSet<String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let body = fs::read_to_string(root.join("docs").join("SURFACE_SYNTAX_COVERAGE.csv")).unwrap();
    body.lines()
        .enumerate()
        .filter_map(|(idx, line)| {
            if idx == 0 || line.trim().is_empty() {
                return None;
            }
            Some(line.split(',').next().unwrap().trim().to_string())
        })
        .collect()
}

fn load_paper_rule_ids() -> BTreeSet<String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let body = fs::read_to_string(root.join("docs").join("PAPER_RULE_COVERAGE.csv")).unwrap();
    body.lines()
        .enumerate()
        .filter_map(|(idx, line)| {
            if idx == 0 || line.trim().is_empty() {
                return None;
            }
            Some(line.split(',').next().unwrap().trim().to_string())
        })
        .collect()
}

#[test]
fn feature_registry_is_complete_consistent_and_linked() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let body = fs::read_to_string(root.join("docs").join("FEATURE_REGISTRY.csv")).unwrap();
    let mut lines = body.lines().filter(|l| !l.trim().is_empty());
    let header = lines
        .next()
        .unwrap_or_default()
        .split(',')
        .map(|s| s.trim())
        .collect::<Vec<_>>();
    assert_eq!(
        header,
        vec!["feature_id", "clause_id", "fixture", "contract_id"]
    );

    let surface = load_surface_clause_ids();
    let paper = load_paper_rule_ids();
    let allowed_clause_ids = surface.union(&paper).cloned().collect::<BTreeSet<_>>();

    let mut seen_feature_ids = BTreeSet::new();
    let mut seen_clause_ids = BTreeSet::new();
    for row in lines {
        let cols = row.split(',').map(|s| s.trim()).collect::<Vec<_>>();
        assert_eq!(cols.len(), 4, "bad feature registry row: {row}");
        let feature_id = cols[0];
        let clause_id = cols[1];
        let fixture = cols[2];
        let contract_id = cols[3];

        assert!(
            seen_feature_ids.insert(feature_id.to_string()),
            "duplicate feature id: {feature_id}"
        );
        assert!(
            allowed_clause_ids.contains(clause_id),
            "unknown clause id in feature registry: {clause_id}"
        );
        seen_clause_ids.insert(clause_id.to_string());

        assert!(
            root.join("tests").join(fixture).exists(),
            "missing fixture from feature registry: {fixture}"
        );
        assert_contract_link_exists(contract_id);
    }

    for clause in surface {
        assert!(
            seen_clause_ids.contains(&clause),
            "surface clause missing from feature registry: {clause}"
        );
    }
    for rule in paper {
        assert!(
            seen_clause_ids.contains(&rule),
            "paper rule missing from feature registry: {rule}"
        );
    }
}
