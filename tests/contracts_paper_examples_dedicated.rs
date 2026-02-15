mod common;

use common::conformance::{
    PaperExampleId, paper_example_anchor, paper_example_category, parse_paper_example_rows,
    read_fixture, replace_once,
};
use common::engines::compile_with_engines;
use common::support::entailment;
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};

fn expected_derivable(id: PaperExampleId) -> bool {
    parse_paper_example_rows("conformance/semantics/paper_examples.csv")
        .into_iter()
        .find(|row| row.id == id)
        .unwrap_or_else(|| panic!("missing paper example row for {:?}", id))
        .expected_derivable
}

fn assert_rejects_surface(syntax: &SyntaxEngine, semantics: &SemanticEngine, source: &str) {
    let module = syntax.parse_module(source).unwrap_or_else(|e| {
        panic!("negative example mutant must parse and then fail typing: {e:?}")
    });
    match semantics.elaborate_module(&module) {
        Err(err) if !err.diagnostics().diagnostics.is_empty() => {}
        Err(other) => panic!("negative example mutant must fail in type checking: {other:?}"),
        Ok(_) => panic!("negative example mutant unexpectedly typechecked"),
    }
}

fn custom_negative_examples(id: PaperExampleId, source: &str) -> Vec<String> {
    match id {
        PaperExampleId::Ex2_4DerivationPredicate => vec![
            replace_once(
                source,
                "(y ->[D] F x)",
                "(F x ->[D] y)",
                "ex2_4.flip_polarity",
            ),
            replace_once(
                source,
                "\\x. \\y. \\u. refl x",
                "\\x. \\y. \\u. u",
                "ex2_4.bad_witness",
            ),
            replace_once(
                source,
                "\\x. \\y. \\u. refl x",
                "\\x. \\y. \\u. refl y",
                "ex2_4.bad_index",
            ),
        ],
        PaperExampleId::Ex2_10OppositePredicate => vec![
            replace_once(
                source,
                "(y ->[D] F x)",
                "(F x ->[D] y)",
                "ex2_10.flip_polarity",
            ),
            replace_once(
                source,
                "\\x. \\y. \\u. u",
                "\\x. \\y. \\u. refl x",
                "ex2_10.bad_witness",
            ),
            replace_once(source, "(y : D)", "(y : C)", "ex2_10.bad_binder_category"),
        ],
        PaperExampleId::Ex3_1Composition => vec![
            replace_once(source, "[f]) g", "[g]) g", "ex3_1.bad_j_edge"),
            replace_once(
                source,
                "(a ->[C] c)",
                "(c ->[C] a)",
                "ex3_1.reverse_result_hom",
            ),
            replace_once(source, "[f]) g", "[f]) f", "ex3_1.bad_composition_arg"),
        ],
        PaperExampleId::Ex3_2FunctorialAction => vec![
            replace_once(source, "[u]", "[x]", "ex3_2.bad_j_evidence"),
            replace_once(source, "refl z", "refl (F z)", "ex3_2.bad_identity_proof"),
            replace_once(
                source,
                "(ex3_2_functorial_map a b f)\n    (ex3_2_functorial_map b c g)",
                "(ex3_2_functorial_map b c g)\n    (ex3_2_functorial_map a b f)",
                "ex3_2.bad_comp_order",
            ),
        ],
        PaperExampleId::Ex3_3Transport => vec![
            replace_once(
                source,
                "P a -> P b",
                "P b -> P a",
                "ex3_3.reverse_transport",
            ),
            replace_once(source, "]) pa", "]) u", "ex3_3.apply_wrong_arg"),
            replace_once(source, "f g)", "g f)", "ex3_3.bad_compose_order"),
        ],
        PaperExampleId::Ex3_4PairOfRewrites => vec![
            replace_once(source, "(u, v)", "(v, u)", "ex3_4.swap_pair"),
            replace_once(source, "(a2, b2)", "(a, b)", "ex3_4.bad_target_pair"),
            replace_once(source, "(u, v)", "u", "ex3_4.not_a_pair"),
        ],
        PaperExampleId::Ex3_5HigherDimensionalRewriting => vec![
            replace_once(source, "(G x)", "(F x)", "ex3_5.bad_codom_family"),
            replace_once(source, "[e]", "[x]", "ex3_5.bad_j_evidence"),
            replace_once(source, "[e]", "[diag_eval F x]", "ex3_5.bad_j_subject"),
        ],
        PaperExampleId::Ex3_6ExistenceOfSingletons => vec![
            replace_once(source, "refl x", "refl y", "ex3_6.bad_diagonal"),
            replace_once(
                source,
                "coend (coend^-1 k)",
                "coend^-1 (coend k)",
                "ex3_6.bad_roundtrip",
            ),
            replace_once(
                source,
                "coend (\\y. refl x)",
                "coend^-1 (\\y. refl x)",
                "ex3_6.bad_intro",
            ),
        ],
        PaperExampleId::Ex3_7InternalNaturality => vec![
            replace_once(
                source,
                "P a -> Q b",
                "P b -> Q a",
                "ex3_7.reverse_transport",
            ),
            replace_once(source, "u) pa", "u) u", "ex3_7.apply_wrong_arg"),
            replace_once(source, "[u]", "[pa]", "ex3_7.bad_j_evidence"),
        ],
        PaperExampleId::Ex3_8InternalDinaturality => vec![
            replace_once(
                source,
                "P b a -> Q a b",
                "P a b -> Q a b",
                "ex3_8.flip_dinatural_side",
            ),
            replace_once(source, "u) pba", "u) u", "ex3_8.apply_wrong_arg"),
            replace_once(source, "[u]", "[pba]", "ex3_8.bad_j_evidence"),
        ],
        PaperExampleId::Ex3_9EndCoendRulesWithTerms => vec![
            replace_once(
                source,
                "(end^-1 alpha)",
                "alpha",
                "ex3_9.treat_end_as_function",
            ),
            replace_once(
                source,
                "coend (lift_at_F g k)",
                "coend^-1 (lift_at_F g k)",
                "ex3_9.bad_coend_intro",
            ),
            replace_once(source, "∫^ (x : C)", "∫ (x : C)", "ex3_9.swap_end_coend"),
        ],
        PaperExampleId::Ex3_10NaturalDeductionCoends => vec![
            replace_once(
                source,
                "coend (\\z. (coend⁻¹ h) z)",
                "coend⁻¹ h",
                "ex3_10.bad_coend_elim",
            ),
            replace_once(
                source,
                "coend (intro_term_lift d s)",
                "coend⁻¹ (intro_term_lift d s)",
                "ex3_10.bad_intro_term",
            ),
            replace_once(
                source,
                "coend (\\z. (J diag_branch [rxy]))",
                "coend (\\z. rxy)",
                "ex3_10.bad_two_var_intro",
            ),
        ],
        PaperExampleId::Ex3_11ImplicationTransitivity => vec![
            replace_once(
                source,
                "qr (pq pa)",
                "pq pa",
                "ex3_11.drop_second_implication",
            ),
            replace_once(source, "qr (pq pa)", "qr pa", "ex3_11.bad_middle_type"),
            replace_once(
                source,
                "(P a -> R a)",
                "(Q a -> R a)",
                "ex3_11.bad_statement",
            ),
        ],
        PaperExampleId::Ex6_1CoYonedaLemma => vec![
            replace_once(
                source,
                "phi_to_predicate_diag x ((phi_transport a x f) phi)",
                "phi_to_predicate_diag a phi",
                "ex6_1.drop_transport",
            ),
            replace_once(
                source,
                "predicate_to_phi_diag a ((predicate_transport x a pair.1) pair.2)",
                "predicate_to_phi_diag a pair.2",
                "ex6_1.bad_coyoneda_elim",
            ),
            replace_once(source, "-> Phi a", "-> P a", "ex6_1.bad_coyoneda_codomain"),
        ],
        PaperExampleId::Ex6_2PresheavesCartesianClosed => vec![
            replace_once(
                source,
                "(pair.2, (phi_transport x y pair.1) phi)",
                "((phi_transport x y pair.1) phi, pair.2)",
                "ex6_2.swap_pair_components",
            ),
            replace_once(
                source,
                "(pair.2, (phi_transport x y pair.1) phi)",
                "(pair.1, (phi_transport x y pair.1) phi)",
                "ex6_2.bad_first_projection",
            ),
            replace_once(source, "-> B y", "-> A y", "ex6_2.bad_statement_codomain"),
        ],
        PaperExampleId::Ex6_3PointwiseRightKan => vec![
            replace_once(
                source,
                "(phi_transport_D y (F x) f) phi",
                "(phi_transport_D (F x) y f) phi",
                "ex6_3.reverse_transport",
            ),
            replace_once(source, "(y ->[D] F x)", "(F x ->[D] y)", "ex6_3.flip_hom"),
            replace_once(
                source,
                "(phi_transport_D y (F x) f) phi",
                "phi",
                "ex6_3.drop_map",
            ),
        ],
        PaperExampleId::Ex6_4FubiniRuleForEnds => vec![
            replace_once(
                source,
                "ex6_4_fubini_left phi x y",
                "ex6_4_fubini_left phi y x",
                "ex6_4.swap_indices",
            ),
            replace_once(
                source,
                "seed x y phi",
                "seed y y phi",
                "ex6_4.bad_fiber_index",
            ),
            replace_once(
                source,
                "\\phi. \\x. fiber_y x phi",
                "\\phi. \\x. seed x x phi",
                "ex6_4.bad_left_map",
            ),
        ],
        PaperExampleId::Ex6_5ImplicationRespectsLimits => vec![
            replace_once(
                source,
                "\\phi. \\q. \\x. q",
                "\\phi. \\q. \\x. phi",
                "ex6_5.bad_left_witness",
            ),
            replace_once(
                source,
                "\\phi. \\x. \\px. px",
                "\\phi. \\x. \\px. x",
                "ex6_5.bad_right_witness",
            ),
            replace_once(
                source,
                "(P x -> Q)",
                "(Q -> P x)",
                "ex6_5.bad_right_statement",
            ),
        ],
    }
}

fn assert_custom_negatives_reject(
    syntax: &SyntaxEngine,
    semantics: &SemanticEngine,
    id: PaperExampleId,
    source: &str,
) {
    let negatives = custom_negative_examples(id, source);
    assert!(
        negatives.len() >= 3,
        "each paper example must have at least three custom negative variants"
    );
    for negative in negatives {
        assert_rejects_surface(syntax, semantics, &negative);
    }
}

fn assert_example_contract(file: &str, expected_id: PaperExampleId) {
    let source = read_fixture(file);
    let (syntax, semantics, typed) = compile_with_engines(&source);

    let anchor = paper_example_anchor(expected_id);
    let rule = paper_example_category(expected_id);
    let signature = format!("{}::{:?}", anchor, rule);
    assert!(!signature.trim().is_empty());

    let result = semantics.derive(&typed, &entailment(anchor), rule);
    let expect = expected_derivable(expected_id);
    assert_eq!(
        result.is_ok(),
        expect,
        "paper example outcome mismatch: expected derivable={}, got derivable={}",
        expect,
        result.is_ok()
    );

    // Enforce non-vacuous rejection boundaries with custom, example-specific negative variants.
    assert_custom_negatives_reject(&syntax, &semantics, expected_id, &source);
}

#[test]
/// Example 2.4: a derivation predicate transports along `y -> F x` and must return the `x`-indexed family.
fn ex2_4_derivation_predicate_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex2_4.spec",
        PaperExampleId::Ex2_4DerivationPredicate,
    );
}

#[test]
/// Example 2.10: opposite-predicate orientation is encoded by the directed hom shape `y -> F x`.
fn ex2_10_opposite_predicate_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex2_10.spec",
        PaperExampleId::Ex2_10OppositePredicate,
    );
}

#[test]
/// Example 3.1: composition is reconstructed through `J` with the first edge as the transport witness.
fn ex3_1_composition_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex3_1.spec",
        PaperExampleId::Ex3_1Composition,
    );
}

#[test]
/// Example 3.2: functorial action preserves directed identities/composition through `J`-based mapping.
fn ex3_2_functorial_action_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex3_2.spec",
        PaperExampleId::Ex3_2FunctorialAction,
    );
}

#[test]
/// Example 3.3: transport carries `P a` to `P b` along a directed edge `a -> b`.
fn ex3_3_transport_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex3_3.spec",
        PaperExampleId::Ex3_3Transport,
    );
}

#[test]
/// Example 3.4: product rewriting keeps component order and category assignment in paired edges.
fn ex3_4_pair_of_rewrites_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex3_4.spec",
        PaperExampleId::Ex3_4PairOfRewrites,
    );
}

#[test]
/// Example 3.5: higher-dimensional rewriting maps natural transformations to end witnesses pointwise.
fn ex3_5_higher_dimensional_rewriting_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex3_5.spec",
        PaperExampleId::Ex3_5HigherDimensionalRewriting,
    );
}

#[test]
/// Example 3.6: singleton existence is witnessed by diagonal coend introduction at each object.
fn ex3_6_existence_of_singletons_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex3_6.spec",
        PaperExampleId::Ex3_6ExistenceOfSingletons,
    );
}

#[test]
/// Example 3.7: internal naturality applies transported morphisms to premises at matching endpoints.
fn ex3_7_internal_naturality_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex3_7.spec",
        PaperExampleId::Ex3_7InternalNaturality,
    );
}

#[test]
/// Example 3.8: internal dinaturality requires the `P b a` input orientation in directed transport.
fn ex3_8_internal_dinaturality_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex3_8.spec",
        PaperExampleId::Ex3_8InternalDinaturality,
    );
}

#[test]
/// Example 3.9: term-level end elimination and coend introduction must use the proper constructors/eliminators.
fn ex3_9_end_coend_rules_with_terms_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex3_9.spec",
        PaperExampleId::Ex3_9EndCoendRulesWithTerms,
    );
}

#[test]
/// Example 3.10: coend intro/elim natural-deduction patterns must preserve diagonal typing constraints.
fn ex3_10_natural_deduction_coends_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex3_10.spec",
        PaperExampleId::Ex3_10NaturalDeductionCoends,
    );
}

#[test]
/// Example 3.11: implication transitivity composes `P -> Q` and `Q -> R` through the middle object.
fn ex3_11_implication_transitivity_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex3_11.spec",
        PaperExampleId::Ex3_11ImplicationTransitivity,
    );
}

#[test]
/// Example 6.1: (co)Yoneda transport must align edge direction with predicate/coend elimination.
fn ex6_1_coyoneda_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex6_1.spec",
        PaperExampleId::Ex6_1CoYonedaLemma,
    );
}

#[test]
/// Example 6.2: presheaf CCC tensor-hom shape preserves pair ordering and transported component typing.
fn ex6_2_presheaves_cartesian_closed_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex6_2.spec",
        PaperExampleId::Ex6_2PresheavesCartesianClosed,
    );
}

#[test]
/// Example 6.3: pointwise right Kan form transports `Phi y` along `y -> F x` in `D`.
fn ex6_3_pointwise_right_kan_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex6_3.spec",
        PaperExampleId::Ex6_3PointwiseRightKan,
    );
}

#[test]
/// Example 6.4: Fubini interchange for iterated ends preserves index order and fiber construction.
fn ex6_4_fubini_rule_for_ends_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex6_4.spec",
        PaperExampleId::Ex6_4FubiniRuleForEnds,
    );
}

#[test]
/// Example 6.5: implication/limit interaction keeps implications pointed at the original limit family.
fn ex6_5_implication_respects_limits_contract() {
    assert_example_contract(
        "conformance/semantics/examples/ex6_5.spec",
        PaperExampleId::Ex6_5ImplicationRespectsLimits,
    );
}
