use ditt_lang::api::*;

#[test]
fn cat_type_from_expr_maps_all_valid_surface_forms() {
    // Var
    let var_result = CatType::from_expr(&Expr::var("C"));
    assert_eq!(var_result.unwrap(), CatType::Var("C".to_string()));

    // Opposite
    let op_result = CatType::from_expr(&Expr::opposite(Expr::var("C")));
    assert_eq!(
        op_result.unwrap(),
        CatType::Opposite(Box::new(CatType::Var("C".to_string())))
    );

    // Product
    let prod_result = CatType::from_expr(&Expr::product(Expr::var("A"), Expr::var("B")));
    assert_eq!(
        prod_result.unwrap(),
        CatType::Product(
            Box::new(CatType::Var("A".to_string())),
            Box::new(CatType::Var("B".to_string()))
        )
    );

    // Arrow -> FunCat
    let arrow_result = CatType::from_expr(&Expr::arrow(Expr::var("A"), Expr::var("B")));
    assert_eq!(
        arrow_result.unwrap(),
        CatType::FunCat(
            Box::new(CatType::Var("A".to_string())),
            Box::new(CatType::Var("B".to_string()))
        )
    );

    // Top
    let top_result = CatType::from_expr(&Expr::Top);
    assert_eq!(top_result.unwrap(), CatType::Top);
}

#[test]
fn cat_type_from_expr_rejects_non_type_expressions() {
    let lambda = Expr::lambda(
        vec![TermBinder::explicit("x", CatType::base("C"))],
        Expr::var("x"),
    );
    assert!(
        CatType::from_expr(&lambda).is_err(),
        "Lambda expressions must not elaborate to CatType"
    );

    let app = Expr::app(Expr::var("f"), vec![Expr::var("x")]);
    assert!(
        CatType::from_expr(&app).is_err(),
        "Application expressions must not elaborate to CatType"
    );

    let refl = Expr::refl(Expr::var("x"));
    assert!(
        CatType::from_expr(&refl).is_err(),
        "Refl expressions must not elaborate to CatType"
    );
}

#[test]
fn term_from_expr_folds_multi_binder_lambda_right() {
    // λ(x:C)(y:D). body  →  Term::Lambda(x:C, Term::Lambda(y:D, body))
    let expr = Expr::lambda(
        vec![
            TermBinder::explicit("x", CatType::base("C")),
            TermBinder::explicit("y", CatType::base("D")),
        ],
        Expr::var("body"),
    );
    let term = Term::from_expr(&expr).unwrap();

    match &term {
        Term::Lambda {
            binder: outer,
            body,
        } => {
            assert_eq!(outer.name, "x");
            assert_eq!(*outer.ty, CatType::base("C"));
            match body.as_ref() {
                Term::Lambda {
                    binder: inner,
                    body: innermost,
                } => {
                    assert_eq!(inner.name, "y");
                    assert_eq!(*inner.ty, CatType::base("D"));
                    assert_eq!(*innermost.as_ref(), Term::Var("body".to_string()));
                }
                other => panic!("expected nested Lambda, got: {other:?}"),
            }
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn term_from_expr_flattens_multi_arg_application_left() {
    // f(a, b)  →  Term::App(Term::App(f, a), b)
    let expr = Expr::app(Expr::var("f"), vec![Expr::var("a"), Expr::var("b")]);
    let term = Term::from_expr(&expr).unwrap();

    match &term {
        Term::App { function, argument } => {
            assert_eq!(**argument, Term::Var("b".to_string()));
            match function.as_ref() {
                Term::App {
                    function: inner_func,
                    argument: inner_arg,
                } => {
                    assert_eq!(**inner_func, Term::Var("f".to_string()));
                    assert_eq!(**inner_arg, Term::Var("a".to_string()));
                }
                other => panic!("expected nested App, got: {other:?}"),
            }
        }
        other => panic!("expected App, got: {other:?}"),
    }
}

#[test]
fn predicate_from_expr_reclassifies_product_as_conjunction() {
    let expr = Expr::product(Expr::Top, Expr::Top);
    let pred = Predicate::from_expr(&expr).unwrap();
    assert!(
        matches!(pred, Predicate::Conj { .. }),
        "Expr::Product must elaborate to Predicate::Conj, got: {pred:?}"
    );
}

#[test]
fn predicate_from_expr_reclassifies_arrow_as_implication() {
    let expr = Expr::arrow(Expr::Top, Expr::Top);
    let pred = Predicate::from_expr(&expr).unwrap();
    assert!(
        matches!(pred, Predicate::Arrow { .. }),
        "Expr::Arrow must elaborate to Predicate::Arrow, got: {pred:?}"
    );
}

#[test]
fn proof_term_from_expr_maps_valid_proof_constructors() {
    // Var
    let var = ProofTerm::from_expr(&Expr::var("p")).unwrap();
    assert_eq!(var, ProofTerm::Var("p".to_string()));

    // Refl
    let refl = ProofTerm::from_expr(&Expr::refl(Expr::var("x"))).unwrap();
    match &refl {
        ProofTerm::Refl { term } => assert_eq!(*term, Term::Var("x".to_string())),
        other => panic!("expected ProofTerm::Refl, got: {other:?}"),
    }

    // JElim
    let j = ProofTerm::from_expr(&Expr::j_elim(Expr::var("t"), Expr::var("p"))).unwrap();
    assert!(matches!(j, ProofTerm::JElim { .. }));

    // Pair
    let pair = ProofTerm::from_expr(&Expr::pair(Expr::var("a"), Expr::var("b"))).unwrap();
    assert!(matches!(pair, ProofTerm::Pair { .. }));

    // Proj
    let proj = ProofTerm::from_expr(&Expr::proj(Expr::var("p"), ProjIndex::First)).unwrap();
    assert!(matches!(proj, ProofTerm::Proj { .. }));
}

#[test]
fn term_binder_implicit_sets_explicitness_to_implicit() {
    let binder = TermBinder::implicit("x", CatType::base("C"));
    assert_eq!(binder.name, "x");
    assert_eq!(*binder.ty, CatType::base("C"));
    assert_eq!(binder.explicitness, Explicitness::Implicit);
}

// =============================================================================
// Step 2: Expr end/coend structured variants
// =============================================================================

#[test]
fn expr_end_intro_factory_carries_binder_and_body() {
    let binder = Binder::new("z", CatType::base("C"));
    let body = Expr::var("pz");
    let expr = Expr::end_intro(binder, body);

    let (b, bod) = expr.as_end_intro().expect("should decompose as EndIntro");
    assert_eq!(b.name, "z", "binder name must be preserved");
    assert_eq!(*b.ty, CatType::base("C"), "binder type must be preserved");
    assert_eq!(*bod, Expr::var("pz"), "body must be preserved");
}

#[test]
fn expr_end_elim_factory_carries_proof_and_witness() {
    let expr = Expr::end_elim(Expr::var("e"), Expr::var("a"));

    let (proof, witness) = expr.as_end_elim().expect("should decompose as EndElim");
    assert_eq!(*proof, Expr::var("e"), "proof must be preserved");
    assert_eq!(*witness, Expr::var("a"), "witness must be preserved");
}

#[test]
fn expr_coend_intro_factory_carries_witness_and_body() {
    let expr = Expr::coend_intro(Expr::var("a"), Expr::var("pa"));

    let (witness, body) = expr
        .as_coend_intro()
        .expect("should decompose as CoendIntro");
    assert_eq!(*witness, Expr::var("a"), "witness must be preserved");
    assert_eq!(*body, Expr::var("pa"), "body must be preserved");
}

#[test]
fn expr_coend_elim_factory_carries_proof_binder_and_continuation() {
    let binder = Binder::new("z", CatType::base("C"));
    let expr = Expr::coend_elim(Expr::var("e"), binder, Expr::var("k"));

    let (proof, b, cont) = expr.as_coend_elim().expect("should decompose as CoendElim");
    assert_eq!(*proof, Expr::var("e"), "proof must be preserved");
    assert_eq!(b.name, "z", "binder name must be preserved");
    assert_eq!(*b.ty, CatType::base("C"), "binder type must be preserved");
    assert_eq!(*cont, Expr::var("k"), "continuation must be preserved");
}

#[test]
fn expr_end_coend_display_preserves_surface_syntax() {
    let end_intro = Expr::end_intro(Binder::new("z", CatType::base("C")), Expr::var("pz"));
    assert_eq!(
        format!("{end_intro}"),
        "end (z : C) . pz",
        "EndIntro display must match surface syntax"
    );

    let end_elim = Expr::end_elim(Expr::var("e"), Expr::var("a"));
    assert_eq!(
        format!("{end_elim}"),
        "end^-1 e a",
        "EndElim display must match surface syntax"
    );

    let coend_intro = Expr::coend_intro(Expr::var("a"), Expr::var("pa"));
    assert_eq!(
        format!("{coend_intro}"),
        "coend a pa",
        "CoendIntro display must match surface syntax"
    );

    let coend_elim = Expr::coend_elim(
        Expr::var("e"),
        Binder::new("z", CatType::base("C")),
        Expr::var("k"),
    );
    assert_eq!(
        format!("{coend_elim}"),
        "coend^-1 e (z : C) . k",
        "CoendElim display must match surface syntax"
    );
}

#[test]
fn expr_end_coend_structural_equality() {
    let a = Expr::end_intro(Binder::new("z", CatType::base("C")), Expr::var("pz"));
    let b = Expr::end_intro(Binder::new("z", CatType::base("C")), Expr::var("pz"));
    assert_eq!(a, b, "same fields must be equal");

    let c = Expr::end_intro(Binder::new("z", CatType::base("C")), Expr::var("qz"));
    assert_ne!(a, c, "different body must be not equal");
}

// =============================================================================
// Step 3: ProofTerm::from_expr completion
// =============================================================================

#[test]
fn proof_term_from_expr_converts_application() {
    let expr = Expr::app(Expr::var("f"), vec![Expr::var("a"), Expr::var("b")]);
    let pt = ProofTerm::from_expr(&expr).expect("App should convert to ProofTerm");

    let expected = ProofTerm::app(
        ProofTerm::app(ProofTerm::var("f"), ProofTerm::var("a")),
        ProofTerm::var("b"),
    );
    assert_eq!(pt, expected, "App should left-fold over arguments");
}

#[test]
fn proof_term_from_expr_converts_end_intro() {
    let binder = Binder::new("z", CatType::base("C"));
    let expr = Expr::end_intro(binder, Expr::var("pz"));
    let pt = ProofTerm::from_expr(&expr).expect("EndIntro should convert to ProofTerm");

    match &pt {
        ProofTerm::EndIntro { binder: b, body } => {
            assert_eq!(b.name, "z", "binder name must match");
            assert_eq!(*b.ty, CatType::base("C"), "binder type must match");
            assert_eq!(**body, ProofTerm::var("pz"), "body must match");
        }
        other => panic!("expected EndIntro, got {other:?}"),
    }
}

#[test]
fn proof_term_from_expr_converts_end_elim() {
    let expr = Expr::end_elim(Expr::var("e"), Expr::var("a"));
    let pt = ProofTerm::from_expr(&expr).expect("EndElim should convert to ProofTerm");

    match &pt {
        ProofTerm::EndElim { proof, witness } => {
            assert_eq!(**proof, ProofTerm::var("e"), "proof must match");
            assert_eq!(*witness, Term::var("a"), "witness must be a Term");
        }
        other => panic!("expected EndElim, got {other:?}"),
    }
}

#[test]
fn proof_term_from_expr_converts_coend_intro() {
    let expr = Expr::coend_intro(Expr::var("a"), Expr::var("pa"));
    let pt = ProofTerm::from_expr(&expr).expect("CoendIntro should convert to ProofTerm");

    match &pt {
        ProofTerm::CoendIntro { witness, body } => {
            assert_eq!(*witness, Term::var("a"), "witness must be a Term");
            assert_eq!(**body, ProofTerm::var("pa"), "body must match");
        }
        other => panic!("expected CoendIntro, got {other:?}"),
    }
}

#[test]
fn proof_term_from_expr_converts_coend_elim() {
    let binder = Binder::new("z", CatType::base("C"));
    let expr = Expr::coend_elim(Expr::var("e"), binder, Expr::var("k"));
    let pt = ProofTerm::from_expr(&expr).expect("CoendElim should convert to ProofTerm");

    match &pt {
        ProofTerm::CoendElim {
            proof,
            binder: b,
            continuation,
        } => {
            assert_eq!(**proof, ProofTerm::var("e"), "proof must match");
            assert_eq!(b.name, "z", "binder name must match");
            assert_eq!(*b.ty, CatType::base("C"), "binder type must match");
            assert_eq!(
                **continuation,
                ProofTerm::var("k"),
                "continuation must match"
            );
        }
        other => panic!("expected CoendElim, got {other:?}"),
    }
}

#[test]
fn proof_term_from_expr_rejects_lambda_with_clear_error() {
    let expr = Expr::lambda(
        vec![TermBinder::explicit("x", CatType::base("C"))],
        Expr::var("x"),
    );
    let result = ProofTerm::from_expr(&expr);
    assert!(
        result.is_err(),
        "Lambda is sort-ambiguous; ProofTerm::from_expr must reject it"
    );
}

#[test]
fn proof_term_from_expr_rejects_type_level_expressions() {
    let arrow = Expr::arrow(Expr::var("A"), Expr::var("B"));
    assert!(
        ProofTerm::from_expr(&arrow).is_err(),
        "Arrow elaborates to CatType/Predicate, not ProofTerm"
    );

    let product = Expr::product(Expr::var("A"), Expr::var("B"));
    assert!(
        ProofTerm::from_expr(&product).is_err(),
        "Product elaborates to CatType/Predicate, not ProofTerm"
    );

    assert!(
        ProofTerm::from_expr(&Expr::Top).is_err(),
        "Top elaborates to CatType/Predicate, not ProofTerm"
    );
}

// =============================================================================
// Step 7: unexpected_expr_error domain-level descriptions
// =============================================================================

#[test]
fn unexpected_expr_error_uses_domain_level_descriptions() {
    let lambda = Expr::lambda(
        vec![TermBinder::explicit("x", CatType::base("C"))],
        Expr::var("x"),
    );
    let err = CatType::from_expr(&lambda).unwrap_err();
    let diags = err.diagnostics();
    let diag = &diags.diagnostics[0];

    assert_eq!(
        diag.code, "unexpected_expression",
        "error code must be 'unexpected_expression', not an internal identifier"
    );
    assert!(
        diag.message.contains("category type"),
        "diagnostic message must describe the target as 'category type', not a Rust path; got: {}",
        diag.message
    );
}

#[test]
fn unexpected_expr_error_for_term_uses_term_description() {
    let err = Term::from_expr(&Expr::Top).unwrap_err();
    let diags = err.diagnostics();
    let diag = &diags.diagnostics[0];

    assert!(
        diag.message.contains("term"),
        "diagnostic message must describe the target as 'term'; got: {}",
        diag.message
    );
}

#[test]
fn unexpected_expr_error_for_proof_term_uses_proof_term_description() {
    let err = ProofTerm::from_expr(&Expr::Top).unwrap_err();
    let diags = err.diagnostics();
    let diag = &diags.diagnostics[0];

    assert!(
        diag.message.contains("proof term"),
        "diagnostic message must describe the target as 'proof term'; got: {}",
        diag.message
    );
}
