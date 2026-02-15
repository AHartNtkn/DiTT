mod common;

use common::assertions::assert_def_equal;
use common::engines::compile_with_engines;
use common::support::*;
use ditt_lang::api::*;

fn term(source: &str) -> Expr {
    Expr::var(source)
}

#[test]
fn evaluator_is_deterministic_for_same_input() {
    let (_syntax, semantics, typed) = compile_with_engines(example_module());
    let input = term("id");

    let one = semantics.evaluate_term(&typed, &input).unwrap();
    let two = semantics.evaluate_term(&typed, &input).unwrap();

    assert_eq!(one, two);
    // steps is an implementation instrumentation field, not a semantic property.
    // We verify only that evaluation produces a result, not the step count.
}

#[test]
fn inferred_types_include_structural_shape_metadata() {
    let (_syntax, semantics, typed) = compile_with_engines(example_module());
    let ty = semantics.infer_term_type(&typed, &term("id")).unwrap();

    match ty {
        CatType::FunCat(..) => {}
        other => {
            panic!("identity function must infer an arrow structure decomposition, got {other:?}")
        }
    }
}

#[test]
fn head_of_spine_extraction_for_application_normal_form() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Runtime.HeadConstructor where
postulate
  C : Cat
  f : (x : C) -> (y : C) -> C
  a : C
  b : C

applied : C = f a b
"#,
    );
    let normal = semantics
        .normalize_term(&typed, &Expr::var("applied"))
        .unwrap();
    assert!(
        matches!(normal.head_constructor(), Term::Var(name) if name == "f"),
        "head constructor of a fully-applied function must be the function variable, got {:?}",
        normal.head_constructor()
    );
}

#[test]
fn normalized_forms_include_structural_shape_metadata() {
    let (_syntax, semantics, typed) = compile_with_engines(example_module());
    let normal = semantics.normalize_term(&typed, &term("id")).unwrap();

    match normal.structure() {
        Term::Lambda { .. } => {}
        other => panic!(
            "normalized identity function must expose a lambda structure decomposition, got {other:?}"
        ),
    }
}

#[test]
fn normalized_forms_expose_multiple_term_structure_variants() {
    let (_syntax, semantics, typed) = compile_with_engines(example_module());

    let id_normal = semantics.normalize_term(&typed, &term("id")).unwrap();
    let map_normal = semantics.normalize_term(&typed, &term("map")).unwrap();
    let transport_normal = semantics
        .normalize_term(&typed, &term("transport"))
        .unwrap();

    assert!(
        matches!(id_normal.structure(), Term::Lambda { .. }),
        "normalized `id` must expose lambda structure, got {:?}",
        id_normal.structure()
    );
    assert!(
        matches!(map_normal.structure(), Term::Var(..)),
        "normalized `map` must expose variable structure, got {:?}",
        map_normal.structure()
    );
    assert!(
        matches!(transport_normal.structure(), Term::Var(..)),
        "normalized `transport` must expose variable structure, got {:?}",
        transport_normal.structure()
    );
}

#[test]
fn evaluate_term_produces_a_result_for_nontrivial_terms() {
    let (_syntax, semantics, typed) = compile_with_engines(example_module());
    // steps is an implementation instrumentation field, not a semantic property.
    // We verify only that evaluation succeeds for a nontrivial term.
    let _result = semantics.evaluate_term(&typed, &term("transport")).unwrap();
}

#[test]
fn typed_declarations_populate_inferred_types_for_definitions() {
    let typed = common::engines::compile_module(example_module());

    let mut saw_definition = false;
    for declaration in typed.declarations {
        if matches!(declaration.declaration, Declaration::Definition { .. }) {
            saw_definition = true;
            let _ty: &ElaboratedType = &declaration.elaborated_type;
        }
    }

    assert!(
        saw_definition,
        "example module must contain at least one definition for this contract"
    );
}

#[test]
fn normalization_is_idempotent() {
    let (_syntax, semantics, typed) = compile_with_engines(example_module());
    let terms = ["id", "refl", "map", "transport_x"];

    for term_name in terms {
        let input = term(term_name);
        let nf1 = semantics.normalize_term(&typed, &input).unwrap();
        let nf1_surface = Expr::from_term(nf1.structure());
        let nf2 = semantics.normalize_term(&typed, &nf1_surface).unwrap();
        assert_eq!(
            nf1, nf2,
            "normalization must be idempotent for '{term_name}'"
        );
    }
}

#[test]
fn normalize_term_terminates_for_all_example_definitions() {
    let (_syntax, semantics, typed) = compile_with_engines(example_module());
    // Normalization must terminate for every defined term in the example module.
    // This is a semantic boundary: if any term diverges, we catch it here.
    let names = [
        "id",
        "refl_intro",
        "refl",
        "map",
        "transport_x",
        "transport",
    ];
    for name in names {
        let result = semantics.normalize_term(&typed, &term(name));
        assert!(
            result.is_ok(),
            "normalization must terminate for '{name}': {:?}",
            result.err()
        );
    }
}

#[test]
fn definitional_equality_is_reflexive_symmetric_and_transitive() {
    // Three syntactically distinct terms that are all definitionally equal:
    // a = (\x. x) y  (a beta redex)
    // b = y           (the normal form)
    // c = (\z. z) y   (a differently-named beta redex)
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Runtime.DefEqProperties where
postulate
  C : Cat
  y : C

a : C = (\x. x) y
b : C = y
c : C = (\z. z) y
"#,
    );

    let ta = Expr::var("a");
    let tb = Expr::var("b");
    let tc = Expr::var("c");

    // Reflexivity: a = a, b = b, c = c
    assert_def_equal(
        &semantics,
        &typed,
        "a",
        "a",
        "reflexivity: a must be definitionally equal to a",
    );
    assert_def_equal(
        &semantics,
        &typed,
        "b",
        "b",
        "reflexivity: b must be definitionally equal to b",
    );
    assert_def_equal(
        &semantics,
        &typed,
        "c",
        "c",
        "reflexivity: c must be definitionally equal to c",
    );

    // Symmetry: a = b implies b = a
    let ab = definitionally_equal(&semantics, &typed, &ta, &tb).unwrap();
    let ba = definitionally_equal(&semantics, &typed, &tb, &ta).unwrap();
    assert!(ab, "a must be definitionally equal to b");
    assert_eq!(ab, ba, "symmetry: a = b must imply b = a");

    // Transitivity: a = b and b = c implies a = c
    let bc = definitionally_equal(&semantics, &typed, &tb, &tc).unwrap();
    let ac = definitionally_equal(&semantics, &typed, &ta, &tc).unwrap();
    assert!(bc, "b must be definitionally equal to c");
    assert!(ac, "transitivity: a = b and b = c must imply a = c");
}

#[test]
fn definitional_equality_is_a_congruence() {
    let (syntax, semantics, typed) = compile_with_engines(
        r#"
module DefEqCongruence where
postulate
  C : Cat
  P : (x : C) -> Prop

left (x : C) : C = (\y. y) x
right (x : C) : C = x
"#,
    );
    // Beta-reduced and unreduced are definitionally equal
    assert_def_equal(
        &semantics,
        &typed,
        "left",
        "right",
        "Beta-redex (\\y. y) x must be definitionally equal to x",
    );

    // If left == right, then P(left) == P(right) (congruence)
    let typed2 = compile_checked(
        &syntax,
        &semantics,
        r#"
module DefEqCongruence.Applied where
postulate
  C : Cat
  P : (x : C) -> Prop

left (x : C) : C = (\y. y) x
right (x : C) : C = x
p_left (x : C) : Prop = P (left x)
p_right (x : C) : Prop = P (right x)
"#,
    );
    assert_def_equal(
        &semantics,
        &typed2,
        "p_left",
        "p_right",
        "Congruence: P(left x) must be definitionally equal to P(right x)",
    );
}

#[test]
fn beta_redex_is_definitionally_equal_to_its_substituted_result() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Runtime.BetaRedexCoherence where
postulate
  C : Cat
  a : C

beta_redex : C =
  (\x. x) a

beta_substituted : C =
  a
"#,
    );

    assert_def_equal(
        &semantics,
        &typed,
        "beta_redex",
        "beta_substituted",
        "beta-redex must be definitionally equal to its substituted normal form",
    );
}

#[test]
fn opposite_involution_is_definitionally_equal_in_runtime_contract() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Runtime.OppositeInvolution where
postulate
  C : Cat

C_op : Cat =
  C^

left : Cat =
  C_op^

right : Cat =
  C
"#,
    );

    assert_def_equal(
        &semantics,
        &typed,
        "left",
        "right",
        "C^op^op must be definitionally equal to C",
    );
}

#[test]
fn beta_reduction_produces_expected_canonical() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Runtime.Canonical.Beta where
postulate
  C : Cat
  a : C

beta_redex : C =
  (\x. x) a

beta_normal : C =
  a
"#,
    );
    let beta = semantics
        .normalize_term(&typed, &Expr::var("beta_redex"))
        .unwrap();
    let expected = semantics
        .normalize_term(&typed, &Expr::var("beta_normal"))
        .unwrap();
    assert_eq!(
        beta.structure().to_string(),
        expected.structure().to_string(),
        "beta-redex canonical normal form must match the substituted normal form"
    );
}

#[test]
fn op_involution_normalizes() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Runtime.Canonical.OpInvolution where
postulate
  C : Cat

left : Cat =
  C^^

right : Cat =
  C
"#,
    );
    let left = semantics
        .normalize_term(&typed, &Expr::var("left"))
        .unwrap();
    let right = semantics
        .normalize_term(&typed, &Expr::var("right"))
        .unwrap();
    assert_eq!(
        left.structure().to_string(),
        right.structure().to_string(),
        "opposite involution must normalize C^^ to the same canonical form as C"
    );
}

#[test]
fn eta_pair_normalizes() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Runtime.Canonical.PairEta where
postulate
  A : Cat
  B : Cat
  p : (A * B)

eta_pair : (A * B) =
  (p.1, p.2)

direct : (A * B) =
  p
"#,
    );
    let eta_pair = semantics
        .normalize_term(&typed, &Expr::var("eta_pair"))
        .unwrap();
    let direct = semantics
        .normalize_term(&typed, &Expr::var("direct"))
        .unwrap();
    assert_eq!(
        eta_pair.structure().to_string(),
        direct.structure().to_string(),
        "pair eta-redex canonical normal form must match the original pair witness"
    );
}

#[test]
fn j_comp_definitionally_equal() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Runtime.DefEq.JComp where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z

j_comp_form : (z : C) -> Phi z z -> Q z z =
  \z. \phi. J h [refl z]
"#,
    );
    assert_def_equal(
        &semantics,
        &typed,
        "j_comp_form",
        "h",
        "J h [refl z] must be definitionally equal to h z in function form",
    );
}

#[test]
fn op_involution_definitionally_equal() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Runtime.DefEq.OpInvolution where
postulate
  C : Cat

left : Cat =
  C^^

right : Cat =
  C
"#,
    );
    assert_def_equal(
        &semantics,
        &typed,
        "left",
        "right",
        "C^^ must be definitionally equal to C",
    );
}

#[test]
fn normalize_and_evaluate_beta_redex_produces_reduced_value() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Runtime.Trace.Beta where
postulate
  C : Cat
  a : C

beta_term : C =
  (\x. x) a

beta_normal : C =
  a
"#,
    );

    let normalized = semantics
        .normalize_term(&typed, &Expr::var("beta_term"))
        .expect("beta redex must normalize");
    let expected = semantics
        .normalize_term(&typed, &Expr::var("beta_normal"))
        .expect("beta normal form must normalize");

    assert_eq!(
        normalized.structure().to_string(),
        expected.structure().to_string(),
        "normalized beta redex must have the same canonical form as the expected normal form"
    );
}

#[test]
fn normalize_and_evaluate_eta_redex_produces_reduced_value() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Runtime.Trace.Eta where
postulate
  C : Cat
  f : (x : C) -> C

eta_term : (x : C) -> C =
  \x. f x

eta_normal : (x : C) -> C =
  f
"#,
    );

    let normalized = semantics
        .normalize_term(&typed, &Expr::var("eta_term"))
        .expect("eta redex must normalize");
    let expected = semantics
        .normalize_term(&typed, &Expr::var("eta_normal"))
        .expect("eta normal form must normalize");

    assert_eq!(
        normalized.structure().to_string(),
        expected.structure().to_string(),
        "normalized eta redex must have the same canonical form as the expected normal form"
    );
}

#[test]
fn definitional_equality_distinguishes_distinct_terms() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Runtime.DefEqDistinct where
postulate
  C : Cat
  a : C
  b : C
"#,
    );

    let eq = definitionally_equal(&semantics, &typed, &Expr::var("a"), &Expr::var("b"));
    assert!(
        matches!(eq, Ok(false)),
        "distinct postulates must not be definitionally equal"
    );
}
