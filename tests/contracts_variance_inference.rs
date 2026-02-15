mod common;

use std::collections::BTreeSet;

use common::conformance::{
    VarianceExampleId, check_accepts, check_rejects, parse_variance_example_rows, read_fixture,
    replace_once, variance_example_anchor, variance_example_category,
};
use common::engines::compile_with_engines;
use common::support::entailment;
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};

fn expected_derivable_for(id: VarianceExampleId) -> bool {
    parse_variance_example_rows("conformance/semantics/variance_examples.csv")
        .into_iter()
        .find(|row| row.id == id)
        .unwrap_or_else(|| panic!("missing variance example row for {:?}", id))
        .expected_derivable
}

fn assert_rejects_surface(syntax: &SyntaxEngine, semantics: &SemanticEngine, source: &str) {
    let module = syntax.parse_module(source).unwrap_or_else(|e| {
        panic!("negative variance mutant must parse and then fail typing: {e:?}")
    });
    match semantics.elaborate_module(&module) {
        Err(err) => {
            let diagnostics = err.into_diagnostics();
            assert!(
                diagnostics.diagnostics.iter().any(|d| {
                    d.category == "TypeTheory"
                        || d.category.to_ascii_lowercase().contains("variance")
                }),
                "variance negatives must include TypeTheory/variance diagnostics"
            );
        }
        Ok(_) => panic!("negative variance mutant unexpectedly typechecked"),
    }
}

fn custom_variance_negatives(id: VarianceExampleId, source: &str) -> Vec<String> {
    match id {
        VarianceExampleId::Ex2_6Variance => vec![
            replace_once(
                source,
                "(x ->[C] y)",
                "(y ->[C] x)",
                "ex2_6.flip_covariant_hom",
            ),
            replace_once(
                source,
                "(y ->[C] z))",
                "(z ->[C] y))",
                "ex2_6.flip_pair_second_component",
            ),
            replace_once(
                source,
                "((x ->[C] z) -> (z ->[C] x))",
                "((x ->[C] z) -> (x ->[C] z))",
                "ex2_6.collapse_polarity",
            ),
        ],
        VarianceExampleId::Ex2_7VarianceFormal => vec![
            replace_once(
                source,
                "((y ->[D] F x) -> P x)",
                "((F x ->[D] y) -> P x)",
                "ex2_7.flip_formal_hom",
            ),
            replace_once(
                source,
                "((y ->[D] F x) -> P x)",
                "((y ->[D] F x) -> P y)",
                "ex2_7.bad_family_index",
            ),
            replace_once(source, "(y : D)", "(y : C)", "ex2_7.bad_binder_category"),
        ],
        VarianceExampleId::Ex2_11ContravarianceFormal => vec![
            replace_once(
                source,
                "ex2_11_contravariance_formal_shape : Prop =\n  (x : C) -> (y : D) -> ((y ->[D] F x) -> P x)",
                "ex2_11_contravariance_formal_shape : Prop =\n  (x : C) -> (y : D) -> ((F x ->[D] y) -> P x)",
                "ex2_11.flip_contravariant_hom",
            ),
            replace_once(
                source,
                "ex2_11_contravariance_formal_shape : Prop =\n  (x : C) -> (y : D) -> ((y ->[D] F x) -> P x)",
                "ex2_11_contravariance_formal_shape : Prop =\n  (x : C) -> (y : D) -> ((y ->[D] F x) -> P y)",
                "ex2_11.bad_family_index",
            ),
            replace_once(
                source,
                "ex2_11_contravariance_formal_shape : Prop =\n  (x : C) -> (y : D) -> ((y ->[D] F x) -> P x)",
                "ex2_11_contravariance_formal_shape : Prop =\n  (x : C) -> (y : C) -> ((y ->[D] F x) -> P x)",
                "ex2_11.bad_binder_category",
            ),
        ],
    }
}

#[test]
/// Variance fixture must contain the paper's three core shapes: covariance, mixed variance, and formal polarity.
fn variance_context_fixture_tracks_paper_shapes() {
    let source = read_fixture("conformance/semantics/variance/context.ditt");
    assert!(
        source.contains("ex2_6_covariant_hom"),
        "variance fixture must include Example 2.6 covariant-hom shape"
    );
    assert!(
        source.contains("ex2_6_mixed_variance_pair"),
        "variance fixture must include Example 2.6 mixed-variance shape"
    );
    assert!(
        source.contains("ex2_6_polarized_implication"),
        "variance fixture must include Example 2.6 implication-variance shape"
    );
    assert!(
        source.contains("ex2_7_variance_formal_shape"),
        "variance fixture must include Example 2.7 formal covariance shape"
    );
    assert!(
        source.contains("ex2_11_contravariance_formal_shape"),
        "variance fixture must include Example 2.11 formal contravariance shape"
    );
    assert!(
        source.contains("(y ->[D] F x) -> P x"),
        "variance fixture must keep the key hom/implication pattern from Examples 2.4/2.7/2.11"
    );
}

fn assert_variance_contract(expected_id: VarianceExampleId) {
    let source = read_fixture("conformance/semantics/variance/context.ditt");
    let (syntax, semantics, typed) = compile_with_engines(&source);

    let anchor = variance_example_anchor(expected_id);
    let rule = variance_example_category(expected_id);
    let signature = format!("{}::{:?}", anchor, rule);
    assert!(!signature.trim().is_empty());

    let result = semantics.derive(&typed, &entailment(anchor), rule);
    let expect = expected_derivable_for(expected_id);
    assert_eq!(
        result.is_ok(),
        expect,
        "variance judgment outcome mismatch: expected derivable={}, got derivable={}",
        expect,
        result.is_ok()
    );

    let negatives = custom_variance_negatives(expected_id, &source);
    assert!(
        !negatives.is_empty(),
        "each variance example must have at least one negative variant"
    );
    for negative in negatives {
        assert_rejects_surface(&syntax, &semantics, &negative);
    }
}

fn expected_variance(id: VarianceExampleId) -> Variance {
    match id {
        VarianceExampleId::Ex2_6Variance => Variance::Covariant,
        VarianceExampleId::Ex2_7VarianceFormal => Variance::Covariant,
        VarianceExampleId::Ex2_11ContravarianceFormal => Variance::Contravariant,
    }
}

#[test]
/// Variance registry rows must each map to a concrete surface anchor and a total judgment category.
fn variance_examples_registry_has_total_anchor_and_category_mappings() {
    let rows = parse_variance_example_rows("conformance/semantics/variance_examples.csv");
    let mut expected = BTreeSet::new();

    for row in rows {
        assert!(expected.insert(row.id));
        assert!(!row.contract_id.trim().is_empty());
        assert!(!variance_example_anchor(row.id).trim().is_empty());
        let _ = variance_example_category(row.id);
    }
}

#[test]
/// Variance registry must stay complete and unique for the three paper-linked entries.
fn variance_examples_registry_is_complete_and_unique() {
    let rows = parse_variance_example_rows("conformance/semantics/variance_examples.csv");

    let required_ids: BTreeSet<VarianceExampleId> = [
        VarianceExampleId::Ex2_6Variance,
        VarianceExampleId::Ex2_7VarianceFormal,
        VarianceExampleId::Ex2_11ContravarianceFormal,
    ]
    .into_iter()
    .collect();

    let mut ids = BTreeSet::new();
    let mut names = BTreeSet::new();
    for row in &rows {
        assert!(
            ids.insert(row.id),
            "duplicate variance example id: {:?}",
            row.id
        );
        assert!(
            names.insert(row.name.clone()),
            "duplicate variance example name: {}",
            row.name
        );
    }

    for required in &required_ids {
        assert!(
            ids.contains(required),
            "variance examples CSV is missing required id: {:?}",
            required
        );
    }
    assert_eq!(
        ids, required_ids,
        "variance examples CSV contains unexpected ids beyond the required set"
    );
}

#[test]
/// Example 2.6 enforces covariance/mixed variance polarity in hom, product, and implication shapes.
fn ex2_6_variance_contract() {
    assert_variance_contract(VarianceExampleId::Ex2_6Variance);
}

#[test]
/// Example 2.7 enforces formal variance orientation in `(y -> F x) -> P x`.
fn ex2_7_variance_formal_contract() {
    assert_variance_contract(VarianceExampleId::Ex2_7VarianceFormal);
}

#[test]
/// Example 2.11 enforces formal contravariant orientation and index discipline at the same shape.
fn ex2_11_contravariance_formal_contract() {
    assert_variance_contract(VarianceExampleId::Ex2_11ContravarianceFormal);
}

#[test]
/// Variance analysis must expose the expected polarity classification for each anchored paper example.
fn variance_examples_compute_expected_polarities() {
    let source = read_fixture("conformance/semantics/variance/context.ditt");
    let (_syntax, semantics, typed) = compile_with_engines(&source);

    for example_id in [
        VarianceExampleId::Ex2_6Variance,
        VarianceExampleId::Ex2_7VarianceFormal,
        VarianceExampleId::Ex2_11ContravarianceFormal,
    ] {
        let predicate = variance_example_anchor(example_id);
        let aggregate = semantics
            .compute_variance_at_position(&typed, predicate, &[], "x")
            .unwrap();
        assert_eq!(
            aggregate,
            expected_variance(example_id),
            "unexpected aggregate variance for {}",
            variance_example_anchor(example_id)
        );

        // Verify that non-root positions are addressable for each example.
        // Position &[0] addresses the first structural child of the predicate body.
        let at_zero = semantics.compute_variance_at_position(&typed, predicate, &[0], "x");
        assert!(
            at_zero.is_ok(),
            "position [0] must be addressable for {}",
            variance_example_anchor(example_id)
        );
        let at_one = semantics.compute_variance_at_position(&typed, predicate, &[1], "x");
        assert!(
            at_one.is_ok(),
            "position [1] must be addressable for {}",
            variance_example_anchor(example_id)
        );
    }
}

#[test]
/// Positional variance must honor non-empty paths; domain and codomain queries cannot collapse.
fn variance_positional_queries_use_non_empty_paths() {
    let source = read_fixture("conformance/semantics/variance/context.ditt");
    let (_syntax, semantics, typed) = compile_with_engines(&source);
    let predicate = "ex2_6_polarized_implication";

    const DOMAIN: usize = 0;
    const CODOMAIN: usize = 1;

    let at_domain = semantics
        .compute_variance_at_position(&typed, predicate, &[DOMAIN], "x")
        .unwrap();
    let at_codomain = semantics
        .compute_variance_at_position(&typed, predicate, &[CODOMAIN], "x")
        .unwrap();

    assert_ne!(
        at_domain, at_codomain,
        "domain and codomain positional variance queries must remain distinguishable"
    );
}

#[test]
/// Full variance analysis must report variable-to-polarity entries, including dinaturality for mixed positions.
fn variance_examples_expose_full_analysis_rows() {
    let source = read_fixture("conformance/semantics/variance/context.ditt");
    let (_syntax, semantics, typed) = compile_with_engines(&source);
    let predicate = "ex2_6_polarized_implication";

    let analyses = semantics.all_variances(&typed, predicate).unwrap();
    let dinatural_entry = analyses
        .iter()
        .find(|a| a.variable == "x" && a.variance == Variance::Dinatural)
        .expect("mixed-polarity implication must classify x as dinatural");

    assert!(
        !dinatural_entry.occurrences.is_empty(),
        "dinatural classification must report at least one occurrence for variable x"
    );
    // x appears in both the domain and codomain of the implication
    // with opposite local variances, producing the dinatural classification.
    assert!(
        dinatural_entry
            .occurrences
            .iter()
            .any(|o| o.local_variance == Variance::Contravariant),
        "dinatural variable must have at least one contravariant occurrence"
    );
    assert!(
        dinatural_entry
            .occurrences
            .iter()
            .any(|o| o.local_variance == Variance::Covariant),
        "dinatural variable must have at least one covariant occurrence"
    );
    for occurrence in &dinatural_entry.occurrences {
        assert!(
            !occurrence.path.is_empty(),
            "each variance occurrence must have a non-empty path"
        );
    }
}

#[test]
/// Nested positional variance queries must preserve distinct paths (for example `[0,0]` vs `[0,1]`) on complex families.
fn variance_positional_queries_support_nested_paths() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Variance.NestedPaths where
postulate
  C : Cat
P (x : C) : Prop =
  (y : C) -> (((x ->[C] y) -> Top) -> (y ->[C] x))
"#,
    );

    let left_nested = semantics
        .compute_variance_at_position(&typed, "P", &[0, 0], "x")
        .unwrap();
    let right_nested = semantics
        .compute_variance_at_position(&typed, "P", &[0, 1], "x")
        .unwrap();

    assert_ne!(
        left_nested, right_nested,
        "nested position paths must remain semantically distinct"
    );
}

#[test]
/// Deeply nested constructor composition must preserve variance algebra at each depth.
fn variance_composition_across_three_nested_constructors() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Variance.NestedComposition where
postulate
  C : Cat
P (x : C) : Prop =
  (((y : C) -> ((x ->[C] y) -> Top)) -> Top) -> Top
"#,
    );

    let overall = semantics
        .compute_variance_at_position(&typed, "P", &[], "x")
        .unwrap();
    let outer_layer = semantics
        .compute_variance_at_position(&typed, "P", &[0], "x")
        .unwrap();
    let middle_layer = semantics
        .compute_variance_at_position(&typed, "P", &[0, 0], "x")
        .unwrap();
    let inner_layer = semantics
        .compute_variance_at_position(&typed, "P", &[0, 0, 0], "x")
        .unwrap();

    assert_eq!(
        inner_layer,
        Variance::Contravariant,
        "innermost hom source occurrence must be contravariant"
    );
    assert_eq!(
        middle_layer,
        Variance::Covariant,
        "wrapping the contravariant occurrence in a covariant context must preserve its orientation"
    );
    assert_eq!(
        outer_layer,
        Variance::Contravariant,
        "adding an outer contravariant constructor must compose back to contravariant"
    );
    assert_eq!(
        overall,
        Variance::Contravariant,
        "composed nested variance must be contravariant at the predicate boundary"
    );
}

#[test]
/// Polarity crossover in one hom-shaped family must reject mixed same-variable variance, while explicit dinatural orientation remains admissible.
fn polarity_crossover_same_variable_both_polarities() {
    check_accepts(
        r#"
module Variance.PolarityCrossover.Dinatural.Positive where
postulate
  C : Cat
P : (a : C^) -> (b : C) -> Prop =
  a ->[C] b
probe : (a : C^) -> (b : C) -> (e : a ->[C] b) -> P a b =
  \a. \b. \e. e
"#,
    );
    check_rejects(
        &[
            r#"
module Variance.PolarityCrossover.SameVariableBothPolarities.Negative where
postulate
  C : Cat
P (x : C) : Prop =
  (y : C) -> ((x ->[C] y) -> (y ->[C] x))
probe : (x : C) -> P x =
  \x. \y. \f. f
"#,
            r#"
module Variance.PolarityCrossover.SameVariableBothPolarities.Negative.BadBody where
postulate
  C : Cat
P (x : C) : Prop =
  (y : C) -> ((x ->[C] y) -> (y ->[C] x))
probe : (x : C) -> P x =
  \x. \y. \f. refl y
"#,
            r#"
module Variance.PolarityCrossover.SameVariableBothPolarities.Negative.BadWitnessIndex where
postulate
  C : Cat
P (x : C) : Prop =
  (y : C) -> ((x ->[C] y) -> (y ->[C] x))
probe : (x : C) -> P x =
  \x. \y. \f. refl x
"#,
        ],
        "TypeTheory",
    );
}

#[test]
/// Nested hom polarity crossover must reject mixed variance for one variable, while keeping a valid dinatural use path accepted.
fn polarity_crossover_in_nested_hom() {
    check_accepts(
        r#"
module Variance.PolarityCrossover.Nested.Positive where
postulate
  C : Cat
P : (a : C^) -> (b : C) -> Prop =
  (q : a ->[C] b) -> (a ->[C] b)
probe : (a : C^) -> (b : C) -> P a b =
  \a. \b. \q. q
"#,
    );
    check_rejects(
        &[
            r#"
module Variance.PolarityCrossover.Nested.Negative where
postulate
  C : Cat
P (x : C) : Prop =
  (y : C) -> (((x ->[C] y) -> Top) -> (y ->[C] x))
probe : (x : C) -> P x =
  \x. \y. \k. refl y
"#,
            r#"
module Variance.PolarityCrossover.Nested.Negative.BadBody where
postulate
  C : Cat
P (x : C) : Prop =
  (y : C) -> (((x ->[C] y) -> Top) -> (y ->[C] x))
probe : (x : C) -> P x =
  \x. \y. \k. k
"#,
            r#"
module Variance.PolarityCrossover.Nested.Negative.BadIndex where
postulate
  C : Cat
P (x : C) : Prop =
  (y : C) -> (((x ->[C] y) -> Top) -> (y ->[C] x))
probe : (x : C) -> P x =
  \x. \y. \k. refl x
"#,
        ],
        "TypeTheory",
    );
}

#[test]
/// Product positional variance must keep left/right components distinguishable.
fn variance_position_product_components_have_distinct_orientations() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Variance.Positional.Product where
postulate
  C : Cat
P (x : C) : Prop =
  ((y : C) -> (x ->[C] y)) * ((y : C) -> (y ->[C] x))
"#,
    );

    let left = semantics
        .compute_variance_at_position(&typed, "P", &[0], "x")
        .unwrap();
    let right = semantics
        .compute_variance_at_position(&typed, "P", &[1], "x")
        .unwrap();

    assert_eq!(left, Variance::Contravariant);
    assert_eq!(right, Variance::Covariant);
}

#[test]
/// Exponential positional variance must distinguish domain and codomain paths.
fn variance_position_exponential_domain_and_codomain_are_distinct() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Variance.Positional.Exponential where
postulate
  C : Cat
P (x : C) : Prop =
  ((y : C) -> (y ->[C] x)) -> ((y : C) -> (y ->[C] x))
"#,
    );

    let domain = semantics
        .compute_variance_at_position(&typed, "P", &[0], "x")
        .unwrap();
    let codomain = semantics
        .compute_variance_at_position(&typed, "P", &[1], "x")
        .unwrap();

    assert_eq!(domain, Variance::Contravariant);
    assert_eq!(codomain, Variance::Covariant);
}

#[test]
/// End quantifier positional variance must expose the body path.
fn variance_position_end_quantifier_body_is_addressable() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Variance.Positional.EndBody where
postulate
  C : Cat
P (x : C) : Prop =
  end (y : C). ((y ->[C] x) -> Top)
"#,
    );

    let body = semantics
        .compute_variance_at_position(&typed, "P", &[1], "x")
        .unwrap();
    assert_eq!(body, Variance::Contravariant);
}

#[test]
/// End-quantifier bodies with polarity crossover must classify as dinatural.
fn variance_position_end_quantifier_body_polarity_crossover_is_dinatural() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Variance.Positional.EndBody.PolarityCrossover where
postulate
  C : Cat
P (x : C) : Prop =
  end (y : C). ((y ->[C] x) -> (y ->[C] x))
"#,
    );

    let overall = semantics
        .compute_variance_at_position(&typed, "P", &[], "x")
        .unwrap();
    let body = semantics
        .compute_variance_at_position(&typed, "P", &[1], "x")
        .unwrap();
    assert_eq!(overall, Variance::Dinatural);
    assert_eq!(body, Variance::Dinatural);
}

#[test]
/// Coend quantifier positional variance must expose the body path.
fn variance_position_coend_quantifier_body_is_addressable() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Variance.Positional.CoendBody where
postulate
  C : Cat
P (x : C) : Prop =
  coend (y : C). (y ->[C] x)
"#,
    );

    let body = semantics
        .compute_variance_at_position(&typed, "P", &[1], "x")
        .unwrap();
    assert_eq!(body, Variance::Covariant);
}

#[test]
/// Hom positional variance must distinguish source and target positions.
fn variance_position_hom_source_and_target_are_distinct() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Variance.Positional.Hom where
postulate
  C : Cat
P (x : C) : Prop =
  (y : C) -> (x ->[C] x)
"#,
    );

    let source_position = semantics
        .compute_variance_at_position(&typed, "P", &[1, 1], "x")
        .unwrap();
    let target_position = semantics
        .compute_variance_at_position(&typed, "P", &[1, 2], "x")
        .unwrap();

    assert_eq!(source_position, Variance::Contravariant);
    assert_eq!(target_position, Variance::Covariant);
}

#[test]
fn variance_positional_out_of_bounds_produces_error() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Variance.OutOfBounds where
postulate
  C : Cat
P (x : C) : Prop = (y : C) -> (x ->[C] y)
"#,
    );
    let result = semantics.compute_variance_at_position(&typed, "P", &[99], "x");
    assert!(
        result.is_err(),
        "Out-of-bounds position path must produce an error"
    );
}

#[test]
fn variance_positional_nested_out_of_bounds_produces_consistent_error_diagnostics() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Variance.OutOfBounds.Nested where
postulate
  C : Cat
P (x : C) : Prop =
  (((y : C) -> ((x ->[C] y) -> Top)) -> Top) -> Top
"#,
    );

    let shallow = semantics
        .compute_variance_at_position(&typed, "P", &[99], "x")
        .unwrap_err()
        .into_diagnostics();
    let deep = semantics
        .compute_variance_at_position(&typed, "P", &[0, 0, 99], "x")
        .unwrap_err()
        .into_diagnostics();

    assert!(
        !shallow.diagnostics.is_empty(),
        "shallow out-of-bounds path must emit diagnostics"
    );
    assert!(
        !deep.diagnostics.is_empty(),
        "nested out-of-bounds path must emit diagnostics"
    );

    let shallow_categories = shallow
        .diagnostics
        .iter()
        .map(|d| d.category.clone())
        .collect::<BTreeSet<_>>();
    let deep_categories = deep
        .diagnostics
        .iter()
        .map(|d| d.category.clone())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        shallow_categories, deep_categories,
        "out-of-bounds positional errors must report consistent diagnostic categories"
    );
    assert!(
        deep.diagnostics.iter().any(|d| {
            d.category == "TypeTheory" || d.category.to_ascii_lowercase().contains("variance")
        }),
        "nested out-of-bounds path must produce TypeTheory/variance diagnostics"
    );

    for diagnostic in &deep.diagnostics {
        assert_eq!(diagnostic.severity, Severity::Error);
        assert!(!diagnostic.message.trim().is_empty());
    }
}

#[test]
fn variance_is_natural_classifies_all_four_modes() {
    assert!(
        Variance::Covariant.is_natural(),
        "Covariant must be natural (Definition 2.5)"
    );
    assert!(
        Variance::Contravariant.is_natural(),
        "Contravariant must be natural (Definition 2.5)"
    );
    assert!(
        !Variance::Dinatural.is_natural(),
        "Dinatural must not be natural (Definition 2.5)"
    );
    assert!(
        !Variance::Unused.is_natural(),
        "Unused must not be natural (Definition 2.5)"
    );
}
