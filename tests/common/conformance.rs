#![allow(dead_code)]

use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;

use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};

use super::support::entailment;

pub fn canonical_severity(severity: &Severity) -> &'static str {
    match severity {
        Severity::Error => "Error",
        Severity::Warning => "Warning",
        Severity::Info => "Info",
    }
}

pub fn fixture_path(relative: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join(relative)
}

pub fn read_fixture(relative: &str) -> String {
    fs::read_to_string(fixture_path(relative)).unwrap()
}

pub fn parse_kv_fixture(relative: &str) -> BTreeMap<String, String> {
    let body = read_fixture(relative);
    let mut map = BTreeMap::new();
    for raw_line in body.lines() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some((k, v)) = line.split_once('=') {
            map.insert(k.trim().to_string(), v.trim().to_string());
        }
    }
    map
}

pub fn parse_csv(relative: &str) -> (Vec<String>, Vec<Vec<String>>) {
    let body = read_fixture(relative);
    let mut lines = body.lines().filter(|l| !l.trim().is_empty());
    let header = lines
        .next()
        .unwrap_or_default()
        .split(',')
        .map(|s| s.trim().to_string())
        .collect::<Vec<_>>();
    let rows = lines
        .map(|line| {
            line.split(',')
                .map(|s| s.trim().to_string())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    (header, rows)
}

/// Categorizes a CSV rule name into one of: a derivation rule, a check judgment,
/// an equational law (normalizer), a variance rule, or a meta-property.
#[derive(Debug, Clone)]
pub enum RuleCategory {
    Derivation(InferenceRule),
    Check(Box<CheckJudgment>),
    Equational(&'static str),
    Variance(&'static str),
    MetaProperty(&'static str),
}

#[derive(Debug, Clone)]
pub struct JudgmentRow {
    pub name: String,
    pub category: RuleCategory,
    pub expected_derivable: bool,
}

pub fn parse_judgment_rows(relative: &str) -> Vec<JudgmentRow> {
    let body = read_fixture(relative);
    let mut rows = Vec::new();

    for (idx, raw) in body.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || idx == 0 {
            continue;
        }
        let parts: Vec<&str> = line.split(',').collect();
        assert_eq!(parts.len(), 3, "bad judgment csv line: {line}");
        rows.push(JudgmentRow {
            name: parts[0].trim().to_string(),
            category: parse_rule_category(parts[1].trim()),
            expected_derivable: parse_expected_derivable(parts[2].trim()),
        });
    }
    rows
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum PaperExampleId {
    Ex2_4DerivationPredicate,
    Ex2_10OppositePredicate,
    Ex3_1Composition,
    Ex3_2FunctorialAction,
    Ex3_3Transport,
    Ex3_4PairOfRewrites,
    Ex3_5HigherDimensionalRewriting,
    Ex3_6ExistenceOfSingletons,
    Ex3_7InternalNaturality,
    Ex3_8InternalDinaturality,
    Ex3_9EndCoendRulesWithTerms,
    Ex3_10NaturalDeductionCoends,
    Ex3_11ImplicationTransitivity,
    Ex6_1CoYonedaLemma,
    Ex6_2PresheavesCartesianClosed,
    Ex6_3PointwiseRightKan,
    Ex6_4FubiniRuleForEnds,
    Ex6_5ImplicationRespectsLimits,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum VarianceExampleId {
    Ex2_6Variance,
    Ex2_7VarianceFormal,
    Ex2_11ContravarianceFormal,
}

#[derive(Debug, Clone)]
pub struct PaperExampleRow {
    pub id: PaperExampleId,
    pub name: String,
    pub contract_id: String,
    pub expected_derivable: bool,
}

#[derive(Debug, Clone)]
pub struct VarianceExampleRow {
    pub id: VarianceExampleId,
    pub name: String,
    pub contract_id: String,
    pub expected_derivable: bool,
}

pub fn parse_paper_example_rows(relative: &str) -> Vec<PaperExampleRow> {
    let (header, rows) = parse_csv(relative);
    assert_eq!(header, vec!["id", "name", "contract_id", "expected"]);
    rows.into_iter()
        .map(|cols| {
            assert_eq!(cols.len(), 4, "bad paper examples csv row");
            PaperExampleRow {
                id: parse_paper_example_id(&cols[0]),
                name: cols[1].clone(),
                contract_id: cols[2].clone(),
                expected_derivable: parse_expected_derivable(&cols[3]),
            }
        })
        .collect()
}

pub fn parse_variance_example_rows(relative: &str) -> Vec<VarianceExampleRow> {
    let (header, rows) = parse_csv(relative);
    assert_eq!(header, vec!["id", "name", "contract_id", "expected"]);
    rows.into_iter()
        .map(|cols| {
            assert_eq!(cols.len(), 4, "bad variance examples csv row");
            VarianceExampleRow {
                id: parse_variance_example_id(&cols[0]),
                name: cols[1].clone(),
                contract_id: cols[2].clone(),
                expected_derivable: parse_expected_derivable(&cols[3]),
            }
        })
        .collect()
}

pub fn parse_rule_category(input: &str) -> RuleCategory {
    match input {
        // Figure 8: context formation → CheckJudgment
        "CtxVarHere" | "Figure8.CtxVarHere" => RuleCategory::Check(Box::new(
            CheckJudgment::VariableInContext(Context::default(), String::new(), CatType::Top),
        )),
        "CtxVarThere" | "Figure8.CtxVarThere" => RuleCategory::Check(Box::new(
            CheckJudgment::VariableInContext(Context::default(), String::new(), CatType::Top),
        )),
        // Figure 9: propositional context → CheckJudgment
        "PropCtxEmpty" | "Figure9.PropCtxEmpty" => RuleCategory::Check(Box::new(
            CheckJudgment::PropCtxWellFormed(Context::default(), vec![]),
        )),
        "PropCtxExtend" | "Figure9.PropCtxExtend" => RuleCategory::Check(Box::new(
            CheckJudgment::PropCtxWellFormed(Context::default(), vec![]),
        )),
        // Figure 11: entailment rules
        "Figure11.Var" | "Var" => RuleCategory::Derivation(InferenceRule::Var),
        "Figure11.Wk" | "Wk" => RuleCategory::Derivation(InferenceRule::Wk),
        "Figure11.Top" | "Top" => RuleCategory::Derivation(InferenceRule::Top),
        "Figure11.Idx" | "Idx" => RuleCategory::Derivation(InferenceRule::Idx),
        "Figure11.Contr" | "Contr" => RuleCategory::Derivation(InferenceRule::Contr),
        "Figure11.Prod" | "Prod" => RuleCategory::Derivation(InferenceRule::Prod),
        "Figure11.Exp" | "Exp" => RuleCategory::Derivation(InferenceRule::Exp),
        "Figure11.End" | "End" => RuleCategory::Derivation(InferenceRule::End),
        "Figure11.Coend" | "Coend" => RuleCategory::Derivation(InferenceRule::Coend),
        "Figure11.CutDin" | "CutDin" => RuleCategory::Derivation(InferenceRule::CutDin),
        "Figure11.CutNat" | "CutNat" => RuleCategory::Derivation(InferenceRule::CutNat),
        "Refl" | "Figure11.Refl" => RuleCategory::Derivation(InferenceRule::Refl),
        "JRule" | "Figure11.J" | "Figure11.JRule" => RuleCategory::Derivation(InferenceRule::JRule),
        // Figure 16: end/coend intro/elim
        "Figure16.EndIntro" | "EndIntro" => RuleCategory::Derivation(InferenceRule::EndIntro),
        "Figure16.EndElim" | "EndElim" => RuleCategory::Derivation(InferenceRule::EndElim),
        "Figure16.CoendElim" | "CoendElim" => RuleCategory::Derivation(InferenceRule::CoendElim),
        "Figure16.CoendIntro" | "CoendIntro" => RuleCategory::Derivation(InferenceRule::CoendIntro),
        // Equational laws (normalizer concern)
        "CutNatIdL" | "CutNatIdR" | "CutCoherence" | "AssocNatDinNat" => {
            RuleCategory::Equational("CutNat")
        }
        "CutDinIdL" | "CutDinIdR" => RuleCategory::Equational("CutDin"),
        "JComp" | "Figure11.JComp" | "JComputation" | "BetaLaw" | "EtaLaw" => {
            RuleCategory::Equational("JRule")
        }
        "JEq" | "Figure11.JEq" => RuleCategory::Equational("JRule"),
        "FunctorMapIdentity" | "FunctorMapComposition" => RuleCategory::Equational("Functor"),
        "TransportIdentity" | "TransportComposition" => RuleCategory::Equational("Transport"),
        "SubjectReduction" | "NormalizationCoherence" => RuleCategory::Equational("Coherence"),
        "EndCoendAdjunction" | "Yoneda" => RuleCategory::Equational("EndElim"),
        "CoYoneda" => RuleCategory::Equational("CoendElim"),
        "EndIntroElimIso" | "FubiniExchange" => RuleCategory::Equational("EndIntro"),
        "CoendIntroElimIso" => RuleCategory::Equational("CoendIntro"),
        "OpInvolution" => RuleCategory::Equational("Refl"),
        // Figure 16 equational rules (normalizer concern)
        "Figure16.EndIsoL" | "EndIsoL" => RuleCategory::Equational("EndIsoL"),
        "Figure16.EndIsoR" | "EndIsoR" => RuleCategory::Equational("EndIsoR"),
        "Figure16.EndNatL" | "EndNatL" => RuleCategory::Equational("EndNatL"),
        "Figure16.EndDinL" | "EndDinL" => RuleCategory::Equational("EndDinL"),
        "Figure16.EndDinR" | "EndDinR" => RuleCategory::Equational("EndDinR"),
        "Figure16.EndNatR" | "EndNatR" => RuleCategory::Equational("EndNatR"),
        "Figure16.CoendIsoL" | "CoendIsoL" => RuleCategory::Equational("CoendIsoL"),
        "Figure16.CoendIsoR" | "CoendIsoR" => RuleCategory::Equational("CoendIsoR"),
        "Figure16.CoendNatL" | "CoendNatL" => RuleCategory::Equational("CoendNatL"),
        "Figure16.CoendDinL" | "CoendDinL" => RuleCategory::Equational("CoendDinL"),
        "Figure16.CoendDinR" | "CoendDinR" => RuleCategory::Equational("CoendDinR"),
        "Figure16.CoendNatR" | "CoendNatR" => RuleCategory::Equational("CoendNatR"),
        "Figure17.EndFunctoriality" | "EndFunctoriality" => {
            RuleCategory::Equational("EndFunctoriality")
        }
        "Figure17.CoendFunctoriality" | "CoendFunctoriality" => {
            RuleCategory::Equational("CoendFunctoriality")
        }
        // Variance rules (VarianceChecker concern)
        "Figure10.CovHom" | "CovHom" => RuleCategory::Variance("CovHom"),
        "Figure10.CovProd" | "CovProd" => RuleCategory::Variance("CovProd"),
        "Figure10.CovExp" | "CovExp" => RuleCategory::Variance("CovExp"),
        "Figure10.Contra" | "Contra" => RuleCategory::Variance("Contra"),
        "Figure10.Unused" | "Unused" => RuleCategory::Variance("Unused"),
        "Figure13.UnusedVarNeq" | "UnusedVarNeq" => RuleCategory::Variance("UnusedVarNeq"),
        "Figure13.UnusedTop" | "UnusedTop" => RuleCategory::Variance("UnusedTop"),
        "Figure13.UnusedApp" | "UnusedApp" => RuleCategory::Variance("UnusedApp"),
        "Figure13.UnusedPair" | "UnusedPair" => RuleCategory::Variance("UnusedPair"),
        "Figure13.UnusedProj" | "UnusedProj" => RuleCategory::Variance("UnusedProj"),
        "Figure13.UnusedLambda" | "UnusedLambda" => RuleCategory::Variance("UnusedLambda"),
        "Figure13.UnusedOp" | "UnusedOp" => RuleCategory::Variance("UnusedOp"),
        "Figure14.CovTop" | "CovTopVariance" => RuleCategory::Variance("CovTop"),
        "Figure14.CovProd" | "CovProdVariance" => RuleCategory::Variance("CovProd"),
        "Figure14.CovExp" | "CovExpVariance" => RuleCategory::Variance("CovExp"),
        "Figure14.CovHom" | "CovHomVariance" => RuleCategory::Variance("CovHom"),
        "Figure14.CovQuantifier" | "CovQuantifier" => RuleCategory::Variance("CovQuantifier"),
        "Figure14.Contra" | "ContraVariance" => RuleCategory::Variance("Contra"),
        // Meta-properties
        "SymmetryNotDerivable" => RuleCategory::MetaProperty("SymmetryNotDerivable"),
        "DirectedCutRestriction" => RuleCategory::MetaProperty("DirectedCutRestriction"),
        "SubstitutionPreservesTyping" | "RenamingPreservesTyping" => {
            RuleCategory::MetaProperty("SubstitutionPreservesTyping")
        }
        "WeakeningAdmissible" => RuleCategory::MetaProperty("WeakeningAdmissible"),
        "ExchangeAdmissible" => RuleCategory::MetaProperty("ExchangeAdmissible"),
        "CongruenceForAllConstructors" => {
            RuleCategory::MetaProperty("CongruenceForAllConstructors")
        }
        _ => panic!("unknown rule category: {input}"),
    }
}

/// Map a RuleCategory to the nearest InferenceRule for boundary testing.
pub fn nearest_derivation_rule(category: &RuleCategory) -> InferenceRule {
    match category {
        RuleCategory::Derivation(rule) => *rule,
        RuleCategory::Check(_) => InferenceRule::Var,
        RuleCategory::Equational(s) => match *s {
            "CutNat" | "CutCoherence" => InferenceRule::CutNat,
            "CutDin" => InferenceRule::CutDin,
            "JRule" | "Functor" | "Transport" | "Coherence" => InferenceRule::JRule,
            "EndElim" | "EndIsoL" | "EndNatL" | "EndDinL" | "EndDinR" | "Yoneda" => {
                InferenceRule::EndElim
            }
            "EndIntro" | "EndIsoR" | "EndNatR" | "EndFunctoriality" => InferenceRule::EndIntro,
            "CoendElim" | "CoendIsoL" | "CoendNatL" | "CoendDinL" | "CoendDinR" | "CoYoneda" => {
                InferenceRule::CoendElim
            }
            "CoendIntro" | "CoendIsoR" | "CoendNatR" | "CoendFunctoriality" => {
                InferenceRule::CoendIntro
            }
            "Refl" => InferenceRule::Refl,
            _ => InferenceRule::JRule,
        },
        RuleCategory::Variance(_) => InferenceRule::Var,
        RuleCategory::MetaProperty(s) => match *s {
            "SymmetryNotDerivable" => InferenceRule::JRule,
            "DirectedCutRestriction" => InferenceRule::CutNat,
            "SubstitutionPreservesTyping" | "RenamingPreservesTyping" | "ExchangeAdmissible" => {
                InferenceRule::Var
            }
            "WeakeningAdmissible" => InferenceRule::Wk,
            "CongruenceForAllConstructors" => InferenceRule::Prod,
            _ => InferenceRule::JRule,
        },
    }
}

pub fn parse_expected_derivable(input: &str) -> bool {
    match input {
        "Derivable" => true,
        "NotDerivable" => false,
        _ => panic!("unknown expected derivable value: {input}"),
    }
}

pub fn derivation_root(source: &str, probe_name: &str, rule: InferenceRule) -> RuleApplication {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let parsed = syntax.parse_module(source).unwrap();
    let typed = semantics.elaborate_module(&parsed).unwrap();
    semantics
        .derive(&typed, &entailment(probe_name), rule)
        .unwrap_or_else(|e| panic!("expected derivable outcome with rule {rule}, got error: {e:?}"))
}

pub fn assert_derivation_rule_from_source(
    source: &str,
    probe_name: &str,
    expected_rule: InferenceRule,
) {
    let root = derivation_root(source, probe_name, expected_rule);
    assert_eq!(root.rule, expected_rule, "derivation root enum must match");
    assert!(
        !root.rule.paper_rule_id().trim().is_empty(),
        "derivable judgment must expose its originating paper rule id"
    );
}

pub fn assert_derivation_rule(
    proof: &RuleApplication,
    expected_rule: InferenceRule,
    context: &str,
) {
    assert_eq!(
        proof.rule, expected_rule,
        "{context}: wrong derivation root rule"
    );
}

pub fn parse_paper_example_id(input: &str) -> PaperExampleId {
    match input {
        "Ex2_4DerivationPredicate" => PaperExampleId::Ex2_4DerivationPredicate,
        "Ex2_10OppositePredicate" => PaperExampleId::Ex2_10OppositePredicate,
        "Ex3_1Composition" => PaperExampleId::Ex3_1Composition,
        "Ex3_2FunctorialAction" => PaperExampleId::Ex3_2FunctorialAction,
        "Ex3_3Transport" => PaperExampleId::Ex3_3Transport,
        "Ex3_4PairOfRewrites" => PaperExampleId::Ex3_4PairOfRewrites,
        "Ex3_5HigherDimensionalRewriting" => PaperExampleId::Ex3_5HigherDimensionalRewriting,
        "Ex3_6ExistenceOfSingletons" => PaperExampleId::Ex3_6ExistenceOfSingletons,
        "Ex3_7InternalNaturality" => PaperExampleId::Ex3_7InternalNaturality,
        "Ex3_8InternalDinaturality" => PaperExampleId::Ex3_8InternalDinaturality,
        "Ex3_9EndCoendRulesWithTerms" => PaperExampleId::Ex3_9EndCoendRulesWithTerms,
        "Ex3_10NaturalDeductionCoends" => PaperExampleId::Ex3_10NaturalDeductionCoends,
        "Ex3_11ImplicationTransitivity" => PaperExampleId::Ex3_11ImplicationTransitivity,
        "Ex6_1CoYonedaLemma" => PaperExampleId::Ex6_1CoYonedaLemma,
        "Ex6_2PresheavesCartesianClosed" => PaperExampleId::Ex6_2PresheavesCartesianClosed,
        "Ex6_3PointwiseRightKan" => PaperExampleId::Ex6_3PointwiseRightKan,
        "Ex6_4FubiniRuleForEnds" => PaperExampleId::Ex6_4FubiniRuleForEnds,
        "Ex6_5ImplicationRespectsLimits" => PaperExampleId::Ex6_5ImplicationRespectsLimits,
        _ => panic!("unknown paper example id: {input}"),
    }
}

pub fn parse_variance_example_id(input: &str) -> VarianceExampleId {
    match input {
        "Ex2_6Variance" => VarianceExampleId::Ex2_6Variance,
        "Ex2_7VarianceFormal" => VarianceExampleId::Ex2_7VarianceFormal,
        "Ex2_11ContravarianceFormal" => VarianceExampleId::Ex2_11ContravarianceFormal,
        _ => panic!("unknown variance example id: {input}"),
    }
}

pub fn paper_example_fixture(id: PaperExampleId) -> &'static str {
    match id {
        PaperExampleId::Ex2_4DerivationPredicate => "conformance/semantics/examples/ex2_4.spec",
        PaperExampleId::Ex2_10OppositePredicate => "conformance/semantics/examples/ex2_10.spec",
        PaperExampleId::Ex3_1Composition => "conformance/semantics/examples/ex3_1.spec",
        PaperExampleId::Ex3_2FunctorialAction => "conformance/semantics/examples/ex3_2.spec",
        PaperExampleId::Ex3_3Transport => "conformance/semantics/examples/ex3_3.spec",
        PaperExampleId::Ex3_4PairOfRewrites => "conformance/semantics/examples/ex3_4.spec",
        PaperExampleId::Ex3_5HigherDimensionalRewriting => {
            "conformance/semantics/examples/ex3_5.spec"
        }
        PaperExampleId::Ex3_6ExistenceOfSingletons => "conformance/semantics/examples/ex3_6.spec",
        PaperExampleId::Ex3_7InternalNaturality => "conformance/semantics/examples/ex3_7.spec",
        PaperExampleId::Ex3_8InternalDinaturality => "conformance/semantics/examples/ex3_8.spec",
        PaperExampleId::Ex3_9EndCoendRulesWithTerms => "conformance/semantics/examples/ex3_9.spec",
        PaperExampleId::Ex3_10NaturalDeductionCoends => {
            "conformance/semantics/examples/ex3_10.spec"
        }
        PaperExampleId::Ex3_11ImplicationTransitivity => {
            "conformance/semantics/examples/ex3_11.spec"
        }
        PaperExampleId::Ex6_1CoYonedaLemma => "conformance/semantics/examples/ex6_1.spec",
        PaperExampleId::Ex6_2PresheavesCartesianClosed => {
            "conformance/semantics/examples/ex6_2.spec"
        }
        PaperExampleId::Ex6_3PointwiseRightKan => "conformance/semantics/examples/ex6_3.spec",
        PaperExampleId::Ex6_4FubiniRuleForEnds => "conformance/semantics/examples/ex6_4.spec",
        PaperExampleId::Ex6_5ImplicationRespectsLimits => {
            "conformance/semantics/examples/ex6_5.spec"
        }
    }
}

pub fn paper_example_anchor(id: PaperExampleId) -> &'static str {
    match id {
        PaperExampleId::Ex2_4DerivationPredicate => "ex2_4_derivation_predicate",
        PaperExampleId::Ex2_10OppositePredicate => "ex2_10_opposite_predicate",
        PaperExampleId::Ex3_1Composition => "ex3_1_compose",
        PaperExampleId::Ex3_2FunctorialAction => "ex3_2_functorial_map",
        PaperExampleId::Ex3_3Transport => "ex3_3_transport",
        PaperExampleId::Ex3_4PairOfRewrites => "ex3_4_pair_rewrites",
        PaperExampleId::Ex3_5HigherDimensionalRewriting => "ex3_5_higher_dimensional_rewriting",
        PaperExampleId::Ex3_6ExistenceOfSingletons => "ex3_6_singleton_exists",
        PaperExampleId::Ex3_7InternalNaturality => "ex3_7_internal_naturality",
        PaperExampleId::Ex3_8InternalDinaturality => "ex3_8_internal_dinaturality",
        PaperExampleId::Ex3_9EndCoendRulesWithTerms => "ex3_9_end_elim",
        PaperExampleId::Ex3_10NaturalDeductionCoends => "ex3_10_coend_elim",
        PaperExampleId::Ex3_11ImplicationTransitivity => "ex3_11_implication_transitivity",
        PaperExampleId::Ex6_1CoYonedaLemma => "ex6_1_yoneda",
        PaperExampleId::Ex6_2PresheavesCartesianClosed => "ex6_2_tensor_hom",
        PaperExampleId::Ex6_3PointwiseRightKan => "ex6_3_right_kan_pointwise",
        PaperExampleId::Ex6_4FubiniRuleForEnds => "ex6_4_fubini_left",
        PaperExampleId::Ex6_5ImplicationRespectsLimits => "ex6_5_implication_respects_limits_left",
    }
}

pub fn paper_example_category(id: PaperExampleId) -> InferenceRule {
    match id {
        PaperExampleId::Ex2_4DerivationPredicate | PaperExampleId::Ex2_10OppositePredicate => {
            InferenceRule::JRule
        }
        PaperExampleId::Ex3_1Composition => InferenceRule::CutNat,
        PaperExampleId::Ex3_2FunctorialAction
        | PaperExampleId::Ex3_7InternalNaturality
        | PaperExampleId::Ex3_8InternalDinaturality => InferenceRule::JRule,
        PaperExampleId::Ex3_3Transport => InferenceRule::JRule,
        PaperExampleId::Ex3_4PairOfRewrites | PaperExampleId::Ex3_5HigherDimensionalRewriting => {
            InferenceRule::Prod
        }
        PaperExampleId::Ex3_6ExistenceOfSingletons | PaperExampleId::Ex6_1CoYonedaLemma => {
            InferenceRule::CoendElim
        }
        PaperExampleId::Ex3_9EndCoendRulesWithTerms
        | PaperExampleId::Ex3_10NaturalDeductionCoends => InferenceRule::EndElim,
        PaperExampleId::Ex3_11ImplicationTransitivity => InferenceRule::Exp,
        PaperExampleId::Ex6_2PresheavesCartesianClosed | PaperExampleId::Ex6_3PointwiseRightKan => {
            InferenceRule::EndElim
        }
        PaperExampleId::Ex6_4FubiniRuleForEnds => InferenceRule::EndIntro,
        PaperExampleId::Ex6_5ImplicationRespectsLimits => InferenceRule::EndIntro,
    }
}

pub fn variance_example_anchor(id: VarianceExampleId) -> &'static str {
    match id {
        VarianceExampleId::Ex2_6Variance => "ex2_6_covariant_hom",
        VarianceExampleId::Ex2_7VarianceFormal => "ex2_7_variance_formal_shape",
        VarianceExampleId::Ex2_11ContravarianceFormal => "ex2_11_contravariance_formal_shape",
    }
}

pub fn variance_example_category(id: VarianceExampleId) -> InferenceRule {
    match id {
        VarianceExampleId::Ex2_6Variance
        | VarianceExampleId::Ex2_7VarianceFormal
        | VarianceExampleId::Ex2_11ContravarianceFormal => InferenceRule::Var,
    }
}

pub fn check_accepts(source: &str) -> TypedModule {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let module = syntax.parse_module(source).unwrap();
    semantics.elaborate_module(&module).unwrap()
}

pub fn reject_once(source: &str, expected_category: &str) {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let module = syntax.parse_module(source).unwrap();
    match semantics.elaborate_module(&module) {
        Err(err) => {
            let diagnostics = err.into_diagnostics();
            assert!(
                diagnostics
                    .diagnostics
                    .iter()
                    .any(|d| d.category == expected_category),
                "negative fixture must include '{expected_category}' diagnostics, got: {diagnostics:?}"
            );
        }
        Ok(_) => panic!("negative fixture unexpectedly typechecked"),
    }
}

pub fn check_rejects(cases: &[&str], expected_category: &str) {
    for case in cases {
        reject_once(case, expected_category);
    }
}

pub fn check_rejects_derive(
    source: &str,
    cases: &[(&str, InferenceRule)],
    expected_category: &str,
) {
    assert!(
        !cases.is_empty(),
        "check_rejects_derive requires at least one judgment case"
    );

    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let module = syntax.parse_module(source).unwrap();
    let typed = match semantics.elaborate_module(&module) {
        Ok(typed) => typed,
        Err(err) => {
            let diagnostics = err.into_diagnostics();
            panic!(
                "negative semantic module unexpectedly failed elaboration; diagnostics: {diagnostics:?}"
            );
        }
    };

    for (name, rule) in cases {
        let err = semantics
            .derive(&typed, &entailment(name), *rule)
            .unwrap_err();
        let diagnostics = err.into_diagnostics();
        assert!(
            diagnostics
                .diagnostics
                .iter()
                .any(|d| d.category == expected_category),
            "negative semantic rejection for '{name}' must include '{expected_category}' diagnostics, got: {diagnostics:?}"
        );
    }
}

#[allow(clippy::too_many_arguments)]
pub fn assert_rule_semantic_boundary(
    syntax: &SyntaxEngine,
    semantics: &SemanticEngine,
    rule_id: &str,
    rule: InferenceRule,
    probe_name: &str,
    positive_source: &str,
    positive_expected_derivable: bool,
    negative_source: &str,
    negative_expected_derivable: bool,
    expected_category: Option<&str>,
) {
    let positive_parsed = syntax.parse_module(positive_source).unwrap();
    let positive_typed = semantics.elaborate_module(&positive_parsed).unwrap();

    let positive_result = semantics.derive(&positive_typed, &entailment(probe_name), rule);
    let positive_derivable = positive_result.is_ok();

    let parsed_negative = syntax.parse_module(negative_source).unwrap();
    let negative_derivable = match semantics.elaborate_module(&parsed_negative) {
        Ok(negative_typed) => semantics
            .derive(&negative_typed, &entailment(probe_name), rule)
            .is_ok(),
        Err(err) => {
            if let Some(category) = expected_category {
                panic!(
                    "negative boundary for {rule_id} failed at type-checking, not at judgment level; this may indicate a malformed negative fixture (expected diagnostic category: {category}, error: {err:?})"
                );
            }
            panic!(
                "negative boundary for {rule_id} failed at type-checking, not at judgment level; this may indicate a malformed negative fixture (error: {err:?})"
            );
        }
    };

    assert_eq!(
        positive_derivable, positive_expected_derivable,
        "positive boundary failed for {rule_id}: expected derivable={positive_expected_derivable}, got derivable={positive_derivable}"
    );
    assert_eq!(
        negative_derivable, negative_expected_derivable,
        "negative boundary failed for {rule_id}: expected derivable={negative_expected_derivable}, got derivable={negative_derivable}"
    );
    assert_ne!(
        positive_derivable, negative_derivable,
        "rule boundary collapsed for {rule_id}: both outcomes are derivable={positive_derivable}"
    );
}

pub fn check_semantic_boundary(
    rule_id: &str,
    rule: InferenceRule,
    probe_name: &str,
    positive_source: &str,
    negative_source: &str,
    expected_category: Option<&str>,
) {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    assert_rule_semantic_boundary(
        &syntax,
        &semantics,
        rule_id,
        rule,
        probe_name,
        positive_source,
        true,
        negative_source,
        false,
        expected_category,
    );
}

pub fn replace_once(source: &str, from: &str, to: &str, label: &str) -> String {
    assert!(
        source.contains(from),
        "custom negative case replacement '{label}' missing source token"
    );
    source.replacen(from, to, 1)
}
