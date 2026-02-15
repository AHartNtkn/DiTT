mod common;

use std::collections::BTreeSet;
use std::path::PathBuf;

use common::conformance::{
    PaperExampleId, paper_example_anchor, paper_example_category, paper_example_fixture,
    parse_paper_example_rows, read_fixture,
};
use common::engines::{compile_module, compile_with_engines};
use common::support::{entailment, is_trivial_forwarder, module_fingerprint};
use ditt_lang::api::*;

#[test]
fn paper_examples_fixture_is_complete_and_unique() {
    let rows = parse_paper_example_rows("conformance/semantics/paper_examples.csv");

    let required_ids: BTreeSet<PaperExampleId> = [
        PaperExampleId::Ex2_4DerivationPredicate,
        PaperExampleId::Ex2_10OppositePredicate,
        PaperExampleId::Ex3_1Composition,
        PaperExampleId::Ex3_2FunctorialAction,
        PaperExampleId::Ex3_3Transport,
        PaperExampleId::Ex3_4PairOfRewrites,
        PaperExampleId::Ex3_5HigherDimensionalRewriting,
        PaperExampleId::Ex3_6ExistenceOfSingletons,
        PaperExampleId::Ex3_7InternalNaturality,
        PaperExampleId::Ex3_8InternalDinaturality,
        PaperExampleId::Ex3_9EndCoendRulesWithTerms,
        PaperExampleId::Ex3_10NaturalDeductionCoends,
        PaperExampleId::Ex3_11ImplicationTransitivity,
        PaperExampleId::Ex6_1CoYonedaLemma,
        PaperExampleId::Ex6_2PresheavesCartesianClosed,
        PaperExampleId::Ex6_3PointwiseRightKan,
        PaperExampleId::Ex6_4FubiniRuleForEnds,
        PaperExampleId::Ex6_5ImplicationRespectsLimits,
    ]
    .into_iter()
    .collect();

    let mut ids = BTreeSet::new();
    let mut names = BTreeSet::new();
    for row in &rows {
        assert!(
            ids.insert(row.id),
            "duplicate paper example id: {:?}",
            row.id
        );
        assert!(
            names.insert(row.name.clone()),
            "duplicate paper example name: {}",
            row.name
        );
    }

    for required in &required_ids {
        assert!(
            ids.contains(required),
            "paper examples CSV is missing required id: {:?}",
            required
        );
    }
    assert_eq!(
        ids, required_ids,
        "paper examples CSV contains unexpected ids beyond the required set"
    );
}

#[test]
fn paper_example_fixture_mapping_is_total_and_one_to_one() {
    let rows = parse_paper_example_rows("conformance/semantics/paper_examples.csv");
    let mut seen_paths = BTreeSet::new();
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests");

    for row in rows {
        let rel = paper_example_fixture(row.id);
        assert!(
            seen_paths.insert(rel.to_string()),
            "duplicate fixture mapping path: {rel}"
        );
        assert!(
            root.join(rel).exists(),
            "missing mapped fixture file: {rel}"
        );
        let body = read_fixture(rel);
        let anchor = paper_example_anchor(row.id);
        assert!(
            body.contains(anchor),
            "fixture {} must contain example-specific anchor '{}'",
            rel,
            anchor
        );
    }
}

#[test]
fn paper_example_surface_fixtures_are_meaningfully_distinct() {
    let rows = parse_paper_example_rows("conformance/semantics/paper_examples.csv");
    let mut fingerprints = BTreeSet::new();

    for row in rows {
        let body = read_fixture(paper_example_fixture(row.id));
        let typed = compile_module(&body);
        let fingerprint = module_fingerprint(&typed);
        assert!(
            fingerprints.insert(fingerprint),
            "paper example fixtures must not be duplicate skeletons"
        );
    }
}

#[test]
fn paper_example_surface_fixtures_include_derivation_terms() {
    let rows = parse_paper_example_rows("conformance/semantics/paper_examples.csv");

    for row in rows {
        let rel = paper_example_fixture(row.id);
        let body = read_fixture(rel);
        let typed = compile_module(&body);
        assert!(
            typed.definitions().next().is_some(),
            "fixture {} must include at least one derivation term, not only proposition declarations",
            rel
        );
    }
}

#[test]
fn removed_rule_families_are_exercised_in_paper_examples_lane() {
    let ex3_2_src = read_fixture("conformance/semantics/examples/ex3_2.spec");
    let ex3_2 = compile_module(&ex3_2_src);
    assert!(
        ex3_2_src.contains("J "),
        "ex3_2 must derive functorial action via directed J"
    );
    assert!(
        ex3_2_src.contains("ex3_2_map_identity"),
        "ex3_2 must include the identity-mapping shape"
    );
    assert!(
        ex3_2_src.contains("ex3_2_map_composition"),
        "ex3_2 must include the composition-mapping shape"
    );
    assert!(
        !is_trivial_forwarder(&ex3_2, "ex3_2_functorial_map"),
        "ex3_2_functorial_map must not be a direct forwarding wrapper to a postulated witness"
    );

    let ex3_3_src = read_fixture("conformance/semantics/examples/ex3_3.spec");
    let ex3_3 = compile_module(&ex3_3_src);
    assert!(
        ex3_3_src.contains("J "),
        "ex3_3 must derive transport via directed J"
    );
    assert!(
        ex3_3_src.contains("ex3_3_transport_identity"),
        "ex3_3 must include transport-on-identity shape"
    );
    assert!(
        ex3_3_src.contains("ex3_3_transport_composition"),
        "ex3_3 must include transport-composition shape"
    );
    assert!(
        !is_trivial_forwarder(&ex3_3, "ex3_3_transport"),
        "ex3_3_transport must not be a direct forwarding wrapper to a postulated witness"
    );

    let ex3_9_src = read_fixture("conformance/semantics/examples/ex3_9.spec");
    assert!(
        ex3_9_src.contains("(g : Gamma) -> ∫ (x : C). P x x -> P (F g) (F g)"),
        "ex3_9 must keep the end-elimination shape from the paper"
    );
    assert!(
        ex3_9_src.contains("(g : Gamma) -> P (F g) (F g) -> ∫^ (x : C). P x x"),
        "ex3_9 must keep the coend-introduction shape from the paper"
    );
    assert!(
        ex3_9_src.contains("end⁻¹ ") || ex3_9_src.contains("end^-1 "),
        "ex3_9 must use the paper-style end^-1 operator in end elimination"
    );
    assert!(
        ex3_9_src.contains("coend "),
        "ex3_9 must use the paper-style coend operator in coend introduction"
    );

    let ex6_1_src = read_fixture("conformance/semantics/examples/ex6_1.spec");
    let ex6_1 = compile_module(&ex6_1_src);
    assert!(
        ex6_1_src.contains("end (x : C). ((a ->[C] x) -> P x)"),
        "ex6_1 must keep the Yoneda end shape"
    );
    assert!(
        ex6_1_src.contains("coend (x : C). ((x ->[C] a) * P x)"),
        "ex6_1 must keep the coYoneda coend shape"
    );
    assert!(
        ex6_1_src.contains("J "),
        "ex6_1 witnesses must use directed transport structure"
    );
    assert!(
        !is_trivial_forwarder(&ex6_1, "ex6_1_yoneda"),
        "ex6_1_yoneda must not be a direct forwarding wrapper to a postulated witness"
    );

    let ex6_4_src = read_fixture("conformance/semantics/examples/ex6_4.spec");
    let ex6_4 = compile_module(&ex6_4_src);
    assert!(
        ex6_4_src.contains("Phi -> end (x : C). end (y : D). P x y"),
        "ex6_4 must keep one nested-end order"
    );
    assert!(
        ex6_4_src.contains("Phi -> end (y : D). end (x : C). P x y"),
        "ex6_4 must keep the exchanged nested-end order"
    );
    assert!(
        !is_trivial_forwarder(&ex6_4, "ex6_4_fubini_left"),
        "ex6_4_fubini_left must not be a direct forwarding wrapper to a postulated witness"
    );
    assert!(
        !is_trivial_forwarder(&ex6_4, "ex6_4_fubini_right"),
        "ex6_4_fubini_right must not be a direct forwarding wrapper to a postulated witness"
    );
}

#[test]
fn advanced_paper_examples_are_not_direct_rule_forwarders() {
    let ex2_4_src = read_fixture("conformance/semantics/examples/ex2_4.spec");
    let ex2_4 = compile_module(&ex2_4_src);
    assert!(
        ex2_4_src.contains("(y ->[D] F x) -> P x"),
        "ex2_4 must keep the derivation-of-predicate shape"
    );
    assert!(
        !is_trivial_forwarder(&ex2_4, "ex2_4_derivation_predicate"),
        "ex2_4_derivation_predicate must not be a direct forwarding wrapper to a postulated witness"
    );

    let ex3_1_src = read_fixture("conformance/semantics/examples/ex3_1.spec");
    let ex3_1 = compile_module(&ex3_1_src);
    assert!(
        ex3_1_src.contains("J "),
        "ex3_1 must use directed J structure for composition"
    );
    assert!(
        !is_trivial_forwarder(&ex3_1, "ex3_1_compose"),
        "ex3_1_compose must not be a direct forwarding wrapper to a postulated witness"
    );

    let ex3_4_src = read_fixture("conformance/semantics/examples/ex3_4.spec");
    let ex3_4 = compile_module(&ex3_4_src);
    assert!(
        ex3_4_src.contains("((a, b) ->[(C * D)] (a2, b2))"),
        "ex3_4 must keep pair-rewrite target shape"
    );
    assert!(
        !is_trivial_forwarder(&ex3_4, "ex3_4_pair_rewrites"),
        "ex3_4_pair_rewrites must not be a direct forwarding wrapper to a postulated witness"
    );

    let ex3_5_src = read_fixture("conformance/semantics/examples/ex3_5.spec");
    let ex3_5 = compile_module(&ex3_5_src);
    assert!(
        ex3_5_src.contains("(e : F ->[C -> D] G) -> end (x : C). ((F x) ->[D] (G x))"),
        "ex3_5 must keep the higher-dimensional rewriting shape via hom in a functor category"
    );
    assert!(
        ex3_5_src.contains("J "),
        "ex3_5 witness must contract directed equality via J as in the paper derivation"
    );
    assert!(
        !is_trivial_forwarder(&ex3_5, "ex3_5_higher_dimensional_rewriting"),
        "ex3_5 witness must not be a direct forwarding wrapper to a postulated witness"
    );

    let ex3_6_src = read_fixture("conformance/semantics/examples/ex3_6.spec");
    let ex3_6 = compile_module(&ex3_6_src);
    assert!(
        ex3_6_src.contains("end (x : C). coend (y : C). (x ->[C] y)"),
        "ex3_6 must keep the singleton existence shape"
    );
    assert!(
        ex3_6_src.contains("coend^-1 ") || ex3_6_src.contains("coend⁻¹ "),
        "ex3_6 must exercise coend^-1 as in the singleton derivation"
    );
    assert!(
        !ex3_6_src.contains("coend_pack"),
        "ex3_6 must not use a postulated coend-pack shortcut"
    );
    assert!(
        !is_trivial_forwarder(&ex3_6, "ex3_6_singleton_exists"),
        "ex3_6 witness must not be a direct forwarding wrapper to a postulated witness"
    );

    let ex3_7_src = read_fixture("conformance/semantics/examples/ex3_7.spec");
    let ex3_7 = compile_module(&ex3_7_src);
    assert!(
        ex3_7_src.contains("J "),
        "ex3_7 must use directed transport structure"
    );
    assert!(
        !is_trivial_forwarder(&ex3_7, "ex3_7_internal_naturality"),
        "ex3_7 witness must not be a direct forwarding wrapper to a postulated witness"
    );

    let ex3_8_src = read_fixture("conformance/semantics/examples/ex3_8.spec");
    let ex3_8 = compile_module(&ex3_8_src);
    assert!(
        ex3_8_src.contains("J "),
        "ex3_8 must use directed transport structure"
    );
    assert!(
        !is_trivial_forwarder(&ex3_8, "ex3_8_internal_dinaturality"),
        "ex3_8 witness must not be a direct forwarding wrapper to a postulated witness"
    );

    let ex3_10_src = read_fixture("conformance/semantics/examples/ex3_10.spec");
    let ex3_10 = compile_module(&ex3_10_src);
    assert!(
        ex3_10_src.contains("∫^ (x : C). P x d"),
        "ex3_10 must keep the coend elimination premise shape"
    );
    assert!(
        ex3_10_src.contains("∫^ (x : C). S x d"),
        "ex3_10 must keep the coend introduction-with-term shape"
    );
    assert!(
        ex3_10_src.contains("∫^ (z : C). R z z"),
        "ex3_10 must keep the two-variable coend introduction shape"
    );
    assert!(
        ex3_10_src.contains("coend⁻¹ ") || ex3_10_src.contains("coend^-1 "),
        "ex3_10 must use the paper-style coend^-1 operator in elimination"
    );
    assert!(
        ex3_10_src.contains("coend "),
        "ex3_10 must use the paper-style coend operator in introductions"
    );
    assert!(
        !ex3_10_src.contains("_rule :"),
        "ex3_10 must not encode theorem obligations as *_rule postulates"
    );
    for def in [
        "ex3_10_coend_elim",
        "ex3_10_coend_intro_term",
        "ex3_10_coend_intro_two_vars",
    ] {
        assert!(
            !is_trivial_forwarder(&ex3_10, def),
            "{def} must not be a direct forwarding wrapper to a postulated witness"
        );
    }

    let ex6_2_src = read_fixture("conformance/semantics/examples/ex6_2.spec");
    let ex6_2 = compile_module(&ex6_2_src);
    assert!(
        ex6_2_src.contains("end (y : C). (((x ->[C] y) * A y) -> B y)"),
        "ex6_2 must keep the tensor/hom end shape"
    );
    assert!(
        !ex6_2_src.contains("_rule :"),
        "ex6_2 must not encode theorem obligations as *_rule postulates"
    );
    assert!(
        !is_trivial_forwarder(&ex6_2, "ex6_2_tensor_hom"),
        "ex6_2_tensor_hom must not be a direct forwarding wrapper to a postulated witness"
    );

    let ex6_3_src = read_fixture("conformance/semantics/examples/ex6_3.spec");
    let ex6_3 = compile_module(&ex6_3_src);
    assert!(
        ex6_3_src.contains("end (x : C). ((y ->[D] F x) -> P x)"),
        "ex6_3 must keep the pointwise right-Kan end shape"
    );
    assert!(
        !ex6_3_src.contains("_rule :"),
        "ex6_3 must not encode theorem obligations as *_rule postulates"
    );
    assert!(
        !is_trivial_forwarder(&ex6_3, "ex6_3_right_kan_pointwise"),
        "ex6_3_right_kan_pointwise must not be a direct forwarding wrapper to a postulated witness"
    );

    let ex6_5_src = read_fixture("conformance/semantics/examples/ex6_5.spec");
    let ex6_5 = compile_module(&ex6_5_src);
    assert!(
        ex6_5_src.contains("Phi -> (Q -> end (x : C). P x)"),
        "ex6_5 must keep the left implication/limit shape"
    );
    assert!(
        ex6_5_src.contains("Phi -> end (x : C). (P x -> Q)"),
        "ex6_5 must keep the right implication/limit shape"
    );
    assert!(
        !ex6_5_src.contains("_rule :"),
        "ex6_5 must not encode theorem obligations as *_rule postulates"
    );
    assert!(
        !is_trivial_forwarder(&ex6_5, "ex6_5_implication_respects_limits_left"),
        "ex6_5 left witness must not be a direct forwarding wrapper to a postulated witness"
    );
    assert!(
        !is_trivial_forwarder(&ex6_5, "ex6_5_implication_respects_limits_right"),
        "ex6_5 right witness must not be a direct forwarding wrapper to a postulated witness"
    );
}

#[test]
fn every_paper_example_anchor_definition_is_not_a_direct_postulate_forwarder() {
    let rows = parse_paper_example_rows("conformance/semantics/paper_examples.csv");
    for row in rows {
        let rel = paper_example_fixture(row.id);
        let body = read_fixture(rel);
        let typed = compile_module(&body);
        let anchor = paper_example_anchor(row.id);
        assert!(
            !is_trivial_forwarder(&typed, anchor),
            "paper example anchor {} in {} must not be a direct forwarding wrapper to a postulated witness",
            anchor,
            rel
        );
    }
}

#[test]
fn paper_examples_registry_entries_have_contract_links_and_total_judgment_mapping() {
    let rows = parse_paper_example_rows("conformance/semantics/paper_examples.csv");
    let mut ids = BTreeSet::new();

    for row in rows {
        assert!(ids.insert(row.id));
        assert!(!row.contract_id.trim().is_empty());
        assert!(!paper_example_anchor(row.id).trim().is_empty());
        let _ = paper_example_category(row.id);
    }
}

#[test]
fn paper_example_outcomes_match_fixture_expectations() {
    let rows = parse_paper_example_rows("conformance/semantics/paper_examples.csv");

    for row in rows {
        let source = read_fixture(paper_example_fixture(row.id));
        let (_syntax, semantics, typed) = compile_with_engines(&source);
        let anchor = paper_example_anchor(row.id);
        let rule = paper_example_category(row.id);
        let result = semantics.derive(&typed, &entailment(anchor), rule);
        assert_eq!(
            result.is_ok(),
            row.expected_derivable,
            "example {:?}: expected derivable={}, got derivable={}",
            row.id,
            row.expected_derivable,
            result.is_ok()
        );
    }
}
