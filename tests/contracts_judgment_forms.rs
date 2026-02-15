mod common;

use common::engines::compile_with_engines;
use ditt_lang::api::*;

const COMPOUND_MODULE: &str = r#"
module Contracts.JudgmentForms where
postulate
  C : Cat
  D : Cat
"#;

fn compile_compound() -> (
    ditt_lang::runtime::SyntaxEngine,
    ditt_lang::runtime::SemanticEngine,
    TypedModule,
) {
    compile_with_engines(COMPOUND_MODULE)
}

// ---------------------------------------------------------------------------
// Group 1: Figure 13 — Unused-variable rules with compound Term constructors
// ---------------------------------------------------------------------------

#[test]
fn figure13_unused_lambda_with_compound_term() {
    let (_syntax, semantics, typed) = compile_compound();

    let term = Term::lambda(Binder::new("x", CatType::base("C")), Term::var("x"));
    let ty = CatType::fun_cat(CatType::base("C"), CatType::base("C"));
    let check = CheckJudgment::TermTyping(Context::default(), term, ty);
    semantics
        .check(&typed, &check)
        .expect("Idx with compound lambda term must be derivable");
}

#[test]
fn figure13_unused_app_with_compound_term() {
    let (_syntax, semantics, typed) = compile_compound();

    let term = Term::app(Term::var("f"), Term::var("x"));
    let ty = CatType::base("D");
    let check = CheckJudgment::TermTyping(Context::default(), term, ty);
    semantics
        .check(&typed, &check)
        .expect("Idx with compound app term must be derivable");
}

#[test]
fn figure13_unused_pair_with_compound_term() {
    let (_syntax, semantics, typed) = compile_compound();

    let term = Term::pair(Term::var("x"), Term::var("y"));
    let ty = CatType::product(CatType::base("C"), CatType::base("C"));
    let check = CheckJudgment::TermTyping(Context::default(), term, ty);
    semantics
        .check(&typed, &check)
        .expect("Prod with compound pair term must be derivable");
}

#[test]
fn figure13_unused_proj_with_compound_term() {
    let (_syntax, semantics, typed) = compile_compound();

    let term = Term::proj(Term::pair(Term::var("x"), Term::var("y")), ProjIndex::First);
    let ty = CatType::base("C");
    let check = CheckJudgment::TermTyping(Context::default(), term, ty);
    semantics
        .check(&typed, &check)
        .expect("Prod with compound proj(pair) term must be derivable");
}

// ---------------------------------------------------------------------------
// Group 2: Figure 10 — Variance rules with compound CatType
// ---------------------------------------------------------------------------

#[test]
fn figure10_cov_exp_with_fun_cat_type() {
    let (_syntax, semantics, typed) = compile_compound();

    let ctx = Context::default().extend(ContextBinding::new(
        "x",
        CatType::base("C"),
        Variance::Covariant,
    ));
    let term = Term::var("f");
    let ty = CatType::fun_cat(CatType::base("C"), CatType::base("D"));
    let check = CheckJudgment::TermTyping(ctx, term, ty);
    semantics
        .check(&typed, &check)
        .expect("Var with fun_cat type must be derivable");
}

#[test]
fn figure10_cov_prod_with_product_type() {
    let (_syntax, semantics, typed) = compile_compound();

    let ctx = Context::default()
        .extend(ContextBinding::new(
            "x",
            CatType::base("C"),
            Variance::Covariant,
        ))
        .extend(ContextBinding::new(
            "y",
            CatType::base("D"),
            Variance::Covariant,
        ));
    let term = Term::var("p");
    let ty = CatType::product(CatType::base("C"), CatType::base("D"));
    let check = CheckJudgment::TermTyping(ctx, term, ty);
    semantics
        .check(&typed, &check)
        .expect("Var with product type must be derivable");
}

// ---------------------------------------------------------------------------
// Group 3: Figure 11 — Entailment rules with compound ProofTerm and Predicate
// ---------------------------------------------------------------------------

#[test]
fn figure11_prod_intro_with_compound_proof_pair() {
    let (_syntax, semantics, typed) = compile_compound();

    let proof = ProofTerm::pair(ProofTerm::var("p"), ProofTerm::var("q"));
    let conclusion = Predicate::conj(Predicate::var("P"), Predicate::var("Q"));
    let prop_ctx = vec![Predicate::var("P"), Predicate::var("Q")];
    let ej = EntailmentJudgment {
        context: Context::default(),
        propositions: prop_ctx,
        proof_term: proof,
        goal: conclusion,
    };
    semantics
        .derive(&typed, &ej, InferenceRule::Prod)
        .expect("Prod intro with compound proof pair must be derivable");
}

#[test]
fn figure11_prod_elim_with_compound_proof_proj() {
    let (_syntax, semantics, typed) = compile_compound();

    let proof = ProofTerm::proj(ProofTerm::var("pq"), ProjIndex::First);
    let conclusion = Predicate::var("P");
    let prop_ctx = vec![Predicate::conj(Predicate::var("P"), Predicate::var("Q"))];
    let ej = EntailmentJudgment {
        context: Context::default(),
        propositions: prop_ctx,
        proof_term: proof,
        goal: conclusion,
    };
    semantics
        .derive(&typed, &ej, InferenceRule::Prod)
        .expect("Prod elim with compound proof proj must be derivable");
}

#[test]
fn figure11_exp_intro_with_compound_proof_lambda() {
    let (_syntax, semantics, typed) = compile_compound();

    let proof = ProofTerm::lambda(
        ProofBinder::new("h", Predicate::var("P")),
        ProofTerm::var("h"),
    );
    let conclusion = Predicate::arrow(Predicate::var("P"), Predicate::var("P"));
    let ej = EntailmentJudgment {
        context: Context::default(),
        propositions: vec![],
        proof_term: proof,
        goal: conclusion,
    };
    semantics
        .derive(&typed, &ej, InferenceRule::Exp)
        .expect("Exp intro with compound proof lambda must be derivable");
}

#[test]
fn figure11_exp_elim_with_compound_proof_app() {
    let (_syntax, semantics, typed) = compile_compound();

    let proof = ProofTerm::app(ProofTerm::var("f"), ProofTerm::var("a"));
    let conclusion = Predicate::var("Q");
    let prop_ctx = vec![
        Predicate::arrow(Predicate::var("P"), Predicate::var("Q")),
        Predicate::var("P"),
    ];
    let ej = EntailmentJudgment {
        context: Context::default(),
        propositions: prop_ctx,
        proof_term: proof,
        goal: conclusion,
    };
    semantics
        .derive(&typed, &ej, InferenceRule::Exp)
        .expect("Exp elim with compound proof app must be derivable");
}

#[test]
fn figure11_refl_with_compound_proof_term() {
    let (_syntax, semantics, typed) = compile_compound();

    let proof = ProofTerm::refl(Term::var("x"));
    let conclusion = Predicate::hom(CatType::base("C"), Term::var("x"), Term::var("x"));
    let ej = EntailmentJudgment {
        context: Context::default(),
        propositions: vec![],
        proof_term: proof,
        goal: conclusion,
    };
    semantics
        .derive(&typed, &ej, InferenceRule::Refl)
        .expect("Refl with compound proof term must be derivable");
}

#[test]
fn figure11_j_rule_with_compound_proof_term() {
    let source = r#"
module Contracts.JudgmentForms.JRule where
postulate
  C : Cat
  D : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);

    let proof = ProofTerm::j_elim(ProofTerm::var("transport"), ProofTerm::refl(Term::var("x")));
    let conclusion = Predicate::var("Q");
    let prop_ctx = vec![Predicate::hom(
        CatType::base("C"),
        Term::var("x"),
        Term::var("x"),
    )];
    let ej = EntailmentJudgment {
        context: Context::default(),
        propositions: prop_ctx,
        proof_term: proof,
        goal: conclusion,
    };
    semantics
        .derive(&typed, &ej, InferenceRule::JRule)
        .expect("JRule with compound j_elim proof term must be derivable");
}

// ---------------------------------------------------------------------------
// Group 4: Figure 16 — End/coend rules with compound proof terms
// ---------------------------------------------------------------------------

#[test]
fn figure16_end_intro_with_compound_proof_term() {
    let (_syntax, semantics, typed) = compile_compound();

    let binder = Binder::new("z", CatType::base("C"));
    let proof = ProofTerm::end_intro(binder.clone(), ProofTerm::var("pz"));
    let conclusion = Predicate::end_form(binder, Predicate::var("P"));
    let ej = EntailmentJudgment {
        context: Context::default(),
        propositions: vec![],
        proof_term: proof,
        goal: conclusion,
    };
    semantics
        .derive(&typed, &ej, InferenceRule::EndIntro)
        .expect("EndIntro with compound end_intro proof term must be derivable");
}

#[test]
fn figure16_end_elim_with_compound_proof_term() {
    let (_syntax, semantics, typed) = compile_compound();

    let binder = Binder::new("z", CatType::base("C"));
    let proof = ProofTerm::end_elim(ProofTerm::var("e"), Term::var("a"));
    let conclusion = Predicate::var("P_instantiated");
    let prop_ctx = vec![Predicate::end_form(binder, Predicate::var("P"))];
    let ej = EntailmentJudgment {
        context: Context::default(),
        propositions: prop_ctx,
        proof_term: proof,
        goal: conclusion,
    };
    semantics
        .derive(&typed, &ej, InferenceRule::EndElim)
        .expect("EndElim with compound end_elim proof term must be derivable");
}

#[test]
fn figure16_coend_intro_with_compound_proof_term() {
    let (_syntax, semantics, typed) = compile_compound();

    let binder = Binder::new("z", CatType::base("C"));
    let proof = ProofTerm::coend_intro(Term::var("a"), ProofTerm::var("pa"));
    let conclusion = Predicate::coend_form(binder, Predicate::var("P"));
    let ej = EntailmentJudgment {
        context: Context::default(),
        propositions: vec![],
        proof_term: proof,
        goal: conclusion,
    };
    semantics
        .derive(&typed, &ej, InferenceRule::CoendIntro)
        .expect("CoendIntro with compound coend_intro proof term must be derivable");
}

#[test]
fn figure16_coend_elim_with_compound_proof_term() {
    let (_syntax, semantics, typed) = compile_compound();

    let binder = Binder::new("z", CatType::base("C"));
    let proof = ProofTerm::coend_elim(ProofTerm::var("e"), binder.clone(), ProofTerm::var("k"));
    let conclusion = Predicate::var("R");
    let prop_ctx = vec![Predicate::coend_form(binder, Predicate::var("P"))];
    let ej = EntailmentJudgment {
        context: Context::default(),
        propositions: prop_ctx,
        proof_term: proof,
        goal: conclusion,
    };
    semantics
        .derive(&typed, &ej, InferenceRule::CoendElim)
        .expect("CoendElim with compound coend_elim proof term must be derivable");
}

// ---------------------------------------------------------------------------
// Group 5: EntailmentEquality — now a CheckJudgment variant
// ---------------------------------------------------------------------------

#[test]
fn figure11_j_comp_with_entailment_equality() {
    let source = r#"
module Contracts.JudgmentForms.JComp where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);

    let ctx = Context::default();
    let props = vec![Predicate::hom(
        CatType::base("C"),
        Term::var("z"),
        Term::var("z"),
    )];
    let lhs = ProofTerm::j_elim(ProofTerm::var("h"), ProofTerm::refl(Term::var("z")));
    let rhs = ProofTerm::var("result");
    let pred = Predicate::var("Q");
    let check = CheckJudgment::EntailmentEquality(ctx, props, lhs, rhs, pred);
    semantics
        .check(&typed, &check)
        .expect("JRule with EntailmentEquality form must be derivable");
}

#[test]
fn figure11_j_eq_with_entailment_equality() {
    let source = r#"
module Contracts.JudgmentForms.JEq where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);

    let ctx = Context::default();
    let props = vec![Predicate::hom(
        CatType::base("C"),
        Term::var("a"),
        Term::var("b"),
    )];
    let pt1 = ProofTerm::j_elim(ProofTerm::var("h"), ProofTerm::var("e"));
    let pt2 = ProofTerm::var("direct");
    let pred = Predicate::var("Q");
    let check = CheckJudgment::EntailmentEquality(ctx, props, pt1, pt2, pred);
    semantics
        .check(&typed, &check)
        .expect("JRule with EntailmentEquality form must be derivable");
}

// ---------------------------------------------------------------------------
// Group 6: Predicate::app coverage
// ---------------------------------------------------------------------------

#[test]
fn figure11_entailment_with_applied_predicate() {
    let (_syntax, semantics, typed) = compile_compound();

    let applied = Predicate::app(Predicate::var("P"), vec![Term::var("x")]);
    let proof = ProofTerm::var("witness");
    let prop_ctx = vec![applied.clone()];
    let ej = EntailmentJudgment {
        context: Context::default(),
        propositions: prop_ctx,
        proof_term: proof,
        goal: applied,
    };
    semantics
        .derive(&typed, &ej, InferenceRule::Var)
        .expect("Var rule with applied predicate must be derivable");
}

// ---------------------------------------------------------------------------
// Group 7: Figure 8 — VariableInContext judgment form
// ---------------------------------------------------------------------------

#[test]
fn figure8_ctx_var_here_finds_variable_at_head() {
    let (_syntax, semantics, typed) = compile_compound();

    // Gamma = [x : C], looking up x : C -- should match via CtxVarHere
    let ctx = Context::default().extend(ContextBinding::new(
        "x",
        CatType::base("C"),
        Variance::Covariant,
    ));
    let check = CheckJudgment::VariableInContext(ctx, "x".to_string(), CatType::base("C"));
    semantics
        .check(&typed, &check)
        .expect("CtxVarHere must derive when variable is at head of context");
}

#[test]
fn figure8_ctx_var_there_finds_variable_past_later_binding() {
    let (_syntax, semantics, typed) = compile_compound();

    // Gamma = [x : C, y : D], looking up x : C -- must skip past y via CtxVarThere
    let ctx = Context::default()
        .extend(ContextBinding::new(
            "x",
            CatType::base("C"),
            Variance::Covariant,
        ))
        .extend(ContextBinding::new(
            "y",
            CatType::base("D"),
            Variance::Covariant,
        ));
    let check = CheckJudgment::VariableInContext(ctx, "x".to_string(), CatType::base("C"));
    semantics
        .check(&typed, &check)
        .expect("CtxVarThere must derive when variable is past a later binding");
}

#[test]
fn figure8_ctx_var_rejects_absent_variable() {
    let (_syntax, semantics, typed) = compile_compound();

    // Gamma = [x : C], looking up z : C -- z is not in context
    let ctx = Context::default().extend(ContextBinding::new(
        "x",
        CatType::base("C"),
        Variance::Covariant,
    ));
    let check = CheckJudgment::VariableInContext(ctx, "z".to_string(), CatType::base("C"));
    let diagnostics = semantics
        .check(&typed, &check)
        .unwrap_err()
        .into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "absent variable in context must produce TypeTheory diagnostics, got: {diagnostics:?}"
    );
}

// ---------------------------------------------------------------------------
// Group 8: Figure 9 — PropCtxWellFormed judgment form
// ---------------------------------------------------------------------------

#[test]
fn figure9_prop_ctx_empty_is_well_formed() {
    let (_syntax, semantics, typed) = compile_compound();

    // Empty propositional context is well-formed
    let check = CheckJudgment::PropCtxWellFormed(Context::default(), vec![]);
    semantics
        .check(&typed, &check)
        .expect("PropCtxEmpty must derive for empty propositional context");
}

#[test]
fn figure9_prop_ctx_extend_with_well_formed_predicate() {
    let (_syntax, semantics, typed) = compile_compound();

    // Extending [P, Q] via PropCtxExtend
    let prop_ctx = vec![Predicate::var("P"), Predicate::var("Q")];
    let check = CheckJudgment::PropCtxWellFormed(Context::default(), prop_ctx);
    semantics.check(&typed, &check).expect(
        "PropCtxExtend must derive for non-empty propositional context with well-formed predicates",
    );
}

#[test]
fn figure9_prop_ctx_extend_rejects_predicate_over_absent_category() {
    let (_syntax, semantics, typed) = compile_compound();

    // PropCtxExtend requires each predicate to reference categories present in the
    // term context. Referencing absent category variable E must be rejected.
    let prop_ctx = vec![Predicate::hom(
        CatType::base("E"),
        Term::var("x"),
        Term::var("y"),
    )];
    let check = CheckJudgment::PropCtxWellFormed(Context::default(), prop_ctx);
    let diagnostics = semantics
        .check(&typed, &check)
        .unwrap_err()
        .into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "predicate over absent category must produce TypeTheory diagnostics, got: {diagnostics:?}"
    );
}

// ---------------------------------------------------------------------------
// Group 9: Figure 11 — Contr, End, Coend dedicated derive tests
// ---------------------------------------------------------------------------

#[test]
fn figure11_contr_with_duplicated_hypothesis() {
    let (_syntax, semantics, typed) = compile_compound();

    // Contraction: [Gamma] P |- (p, p) : P x P -- uses hypothesis P twice
    let proof = ProofTerm::pair(ProofTerm::var("p"), ProofTerm::var("p"));
    let conclusion = Predicate::conj(Predicate::var("P"), Predicate::var("P"));
    let prop_ctx = vec![Predicate::var("P")];
    let ej = EntailmentJudgment {
        context: Context::default(),
        propositions: prop_ctx,
        proof_term: proof,
        goal: conclusion,
    };
    semantics
        .derive(&typed, &ej, InferenceRule::Contr)
        .expect("Contr with duplicated hypothesis must be derivable");
}

#[test]
fn figure11_end_rule_with_end_predicate_conclusion() {
    let (_syntax, semantics, typed) = compile_compound();

    // End rule: [Gamma] Phi |- end_intro(pz) : end_{z:C} P(z_bar, z)
    let binder = Binder::new("z", CatType::base("C"));
    let proof = ProofTerm::end_intro(binder.clone(), ProofTerm::var("pz"));
    let conclusion = Predicate::end_form(binder, Predicate::var("P"));
    let prop_ctx = vec![Predicate::var("P")];
    let ej = EntailmentJudgment {
        context: Context::default(),
        propositions: prop_ctx,
        proof_term: proof,
        goal: conclusion,
    };
    semantics
        .derive(&typed, &ej, InferenceRule::End)
        .expect("End rule with end predicate conclusion must be derivable");
}

#[test]
fn figure11_coend_rule_with_coend_predicate_conclusion() {
    let (_syntax, semantics, typed) = compile_compound();

    // Coend rule: [Gamma] Phi |- coend_intro(a, pa) : coend^{z:C} P(z_bar, z)
    let binder = Binder::new("z", CatType::base("C"));
    let proof = ProofTerm::coend_intro(Term::var("a"), ProofTerm::var("pa"));
    let conclusion = Predicate::coend_form(binder, Predicate::var("P"));
    let prop_ctx = vec![Predicate::var("P")];
    let ej = EntailmentJudgment {
        context: Context::default(),
        propositions: prop_ctx,
        proof_term: proof,
        goal: conclusion,
    };
    semantics
        .derive(&typed, &ej, InferenceRule::Coend)
        .expect("Coend rule with coend predicate conclusion must be derivable");
}

// ---------------------------------------------------------------------------
// Group 10: Type-safe judgment API
// ---------------------------------------------------------------------------

#[test]
fn entailment_judgment_carries_context_propositions_proof_and_goal() {
    let ej = EntailmentJudgment {
        context: Context::default(),
        propositions: vec![Predicate::top()],
        proof_term: ProofTerm::var("p"),
        goal: Predicate::top(),
    };
    assert!(ej.propositions.len() == 1);
    assert_eq!(ej.goal, Predicate::top());
}

#[test]
fn check_judgment_covers_all_well_formedness_forms() {
    // Verify each CheckJudgment variant is constructible with appropriate types.
    let _twf = CheckJudgment::TypeWellFormed(CatType::base("C"));
    let _teq = CheckJudgment::TypeEquality(CatType::base("C"), CatType::base("D"));
    let _cwf = CheckJudgment::ContextWellFormed(Context::default());
    let _vic = CheckJudgment::VariableInContext(
        Context::default().extend(ContextBinding::new(
            "x",
            CatType::base("C"),
            Variance::Covariant,
        )),
        "x".to_string(),
        CatType::base("C"),
    );
    let _pwf = CheckJudgment::PredicateWellFormed(Context::default(), Predicate::top());
    let _pcwf = CheckJudgment::PropCtxWellFormed(Context::default(), vec![Predicate::top()]);
    let _tt = CheckJudgment::TermTyping(Context::default(), Term::var("x"), CatType::base("C"));
    let _ee = CheckJudgment::EntailmentEquality(
        Context::default(),
        vec![],
        ProofTerm::var("p"),
        ProofTerm::var("q"),
        Predicate::top(),
    );
}

#[test]
fn derive_returns_rule_application_for_well_formed_entailment() {
    let (_syntax, semantics, typed) = compile_compound();

    let ej = EntailmentJudgment {
        context: Context::default(),
        propositions: vec![Predicate::top()],
        proof_term: ProofTerm::var("p"),
        goal: Predicate::top(),
    };
    let proof = semantics
        .derive(&typed, &ej, InferenceRule::Idx)
        .expect("Idx rule must derive for Top hypothesis matching Top goal");
    assert_eq!(
        proof.rule,
        InferenceRule::Idx,
        "derivation root must report the Idx rule"
    );
}

#[test]
fn check_verifies_type_well_formedness_for_postulated_base() {
    let (_syntax, semantics, typed) = compile_compound();

    let check = CheckJudgment::TypeWellFormed(CatType::base("C"));
    semantics
        .check(&typed, &check)
        .expect("TypeWellFormed must pass for postulated base type C");
}
