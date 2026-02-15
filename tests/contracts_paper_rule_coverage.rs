mod common;

use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

#[derive(Debug, Clone)]
struct RuleRow {
    rule_id: String,
    judgment_kind: String,
    positive_contract_id: String,
    negative_contract_id: String,
}

fn paper_rule_rows() -> (Vec<String>, Vec<RuleRow>) {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let body = fs::read_to_string(root.join("docs").join("PAPER_RULE_COVERAGE.csv")).unwrap();
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
            assert_eq!(cols.len(), 4, "bad paper rule row: {line}");
            RuleRow {
                rule_id: cols[0].clone(),
                judgment_kind: cols[1].clone(),
                positive_contract_id: cols[2].clone(),
                negative_contract_id: cols[3].clone(),
            }
        })
        .collect::<Vec<_>>();

    (header, rows)
}

fn expected_rule_ids() -> BTreeSet<&'static str> {
    [
        "Figure8.CtxVarHere",
        "Figure8.CtxVarThere",
        "Figure9.PropCtxEmpty",
        "Figure9.PropCtxExtend",
        "Figure10.CovHom",
        "Figure10.CovProd",
        "Figure10.CovExp",
        "Figure10.Contra",
        "Figure10.Unused",
        "Figure11.Var",
        "Figure11.Wk",
        "Figure11.Top",
        "Figure11.Idx",
        "Figure11.Contr",
        "Figure11.Prod",
        "Figure11.Exp",
        "Figure11.End",
        "Figure11.Coend",
        "Figure11.CutDin",
        "Figure11.CutNat",
        "Figure11.Refl",
        "Figure11.JRule",
        "Figure11.JComp",
        "Figure11.JEq",
        "Figure13.UnusedVarNeq",
        "Figure13.UnusedTop",
        "Figure13.UnusedApp",
        "Figure13.UnusedPair",
        "Figure13.UnusedProj",
        "Figure13.UnusedLambda",
        "Figure13.UnusedOp",
        "Figure14.CovTopVariance",
        "Figure14.CovProdVariance",
        "Figure14.CovExpVariance",
        "Figure14.CovHomVariance",
        "Figure14.CovQuantifier",
        "Figure14.ContraVariance",
        "Figure15.AssocNatDinNat",
        "Figure15.CutCoherence",
        "Figure15.CutNatIdL",
        "Figure15.CutNatIdR",
        "Figure15.CutDinIdL",
        "Figure15.CutDinIdR",
        "Figure16.EndIntro",
        "Figure16.EndElim",
        "Figure16.CoendIntro",
        "Figure16.CoendElim",
        "Figure16.EndIsoL",
        "Figure16.EndIsoR",
        "Figure16.EndNatL",
        "Figure16.EndDinL",
        "Figure16.EndDinR",
        "Figure16.EndNatR",
        "Figure16.CoendIsoL",
        "Figure16.CoendIsoR",
        "Figure16.CoendNatL",
        "Figure16.CoendNatR",
        "Figure16.CoendDinL",
        "Figure16.CoendDinR",
        "Figure17.EndFunctoriality",
        "Figure17.CoendFunctoriality",
    ]
    .into_iter()
    .collect()
}

fn assert_contract_link_exists(contract_id: &str) {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let (path, symbol) = contract_id.split_once("::").unwrap_or((contract_id, ""));
    assert!(
        !symbol.is_empty(),
        "contract id missing symbol: {contract_id}"
    );

    let full_path = root.join(path);
    assert!(full_path.exists(), "contract file missing: {path}");
    let body = fs::read_to_string(full_path).unwrap();
    assert!(
        body.contains(symbol),
        "contract symbol missing: {contract_id}"
    );
}

#[test]
fn paper_rule_coverage_matrix_is_complete_unique_and_well_formed() {
    let (header, rows) = paper_rule_rows();
    assert_eq!(
        header,
        vec![
            "rule_id",
            "judgment_kind",
            "positive_contract_id",
            "negative_contract_id"
        ]
    );
    assert!(!rows.is_empty());

    let mut seen_rule_ids = BTreeSet::new();
    for row in rows {
        assert!(
            seen_rule_ids.insert(row.rule_id.clone()),
            "duplicate rule_id"
        );
        assert!(
            !row.judgment_kind.trim().is_empty(),
            "judgment_kind must be non-empty"
        );
        assert_contract_link_exists(&row.positive_contract_id);
        assert_contract_link_exists(&row.negative_contract_id);
    }

    let expected = expected_rule_ids()
        .into_iter()
        .map(|s| s.to_string())
        .collect::<BTreeSet<_>>();
    assert_eq!(seen_rule_ids, expected, "paper rule coverage is incomplete");
}
