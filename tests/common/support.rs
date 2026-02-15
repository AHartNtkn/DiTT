#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};

use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};

pub fn example_module() -> &'static str {
    r#"
module Contracts.Example where

postulate C : Cat

id (x : C) : x ->[C] x = refl x
refl_intro (x : C) : x ->[C] x = refl x
refl (x : C) : x ->[C] x = refl_intro x
map (x : C) : C = x
transport_x (x : C) : C = map x
transport (x : C) : C = transport_x x
"#
}

pub fn invalid_module() -> &'static str {
    r#"
module Contracts.Invalid where
broken (x : C : x ->[C] x = refl x
"#
}

pub fn directed_theory_module() -> &'static str {
    r#"
module Contracts.Directed where

postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z
  Pred : (x : C) -> Prop

diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k

compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [f]) g

refl_intro (x : C) : x ->[C] x =
  refl x

j_comp (z : C) (phi : Phi z z) : Q z z =
  J h [refl z]

j_dep (a : C^) (b : C) (e : a ->[C] b) (phi : Phi b a) : Q a b =
  J h [e]

comp_left_id (a : C) (b : C) (f : a ->[C] b) : a ->[C] b =
  compose_via_j a a b (refl a) f

comp_right_id (a : C) (b : C) (f : a ->[C] b) : a ->[C] b =
  compose_via_j a b b f (refl b)

comp_assoc (a : C) (b : C) (c : C) (d : C) (f : a ->[C] b) (g : b ->[C] c) (k : c ->[C] d) : a ->[C] d =
  compose_via_j a c d (compose_via_j a b c f g) k

symmetry (a : C) (b : C) (requires_symmetry : (a ->[C] b) -> (b ->[C] a)) (e : a ->[C] b) : b ->[C] a =
  requires_symmetry e

restricted_cut (a : C) (all : end (x : C). Pred x) : Pred a =
  all a

subst_ty (x : C) : D =
  (\y. F y) x

rename_ty (x : C) : D =
  (\renamed. F renamed) x

weakening (x : C) (y : D) : C =
  x

exchange (x : C) (y : D) : (D * C) =
  (y, x)

C_op : Cat =
  C^

C_op_op : Cat =
  C_op^

op_involution (x : C) : x ->[C_op_op] x =
  refl x

beta (x : C) : C =
  (\y. y) x

eta (f : (x : C) -> C) : (x : C) -> C =
  \x. f x

congruence (a : C) (a2 : C) (b : D) (b2 : D) (u : a ->[C] a2) (v : b ->[D] b2) : (a, b) ->[(C * D)] (a2, b2) =
  (u, v)

norm_coherence (x : C) : C =
  (\u. u) ((\v. v) x)
"#
}

pub fn compile_checked(
    syntax: &SyntaxEngine,
    semantics: &SemanticEngine,
    source: &str,
) -> TypedModule {
    let parsed = syntax.parse_module(source).unwrap();
    semantics.elaborate_module(&parsed).unwrap()
}

pub fn entailment(name: &str) -> EntailmentJudgment {
    EntailmentJudgment {
        context: Context::default(),
        propositions: vec![],
        proof_term: ProofTerm::var(name),
        goal: Predicate::Top,
    }
}

pub fn entailment_in_context(name: &str, context: Context) -> EntailmentJudgment {
    EntailmentJudgment {
        context,
        propositions: vec![],
        proof_term: ProofTerm::var(name),
        goal: Predicate::Top,
    }
}

/// Returns true if the named definition is a trivial forwarder:
/// its body (after peeling lambdas) is just `postulate_name arg1 arg2 ...`
/// where all args are the lambda-bound variables.
pub fn is_trivial_forwarder(module: &TypedModule, def_name: &str) -> bool {
    let postulate_names: BTreeSet<&str> = module
        .postulates()
        .map(|td| td.declaration.name())
        .collect();

    let Some(typed_decl) = module.lookup_declaration(def_name) else {
        return false;
    };
    let Some(binders) = typed_decl.declaration.definition_binders() else {
        return false;
    };
    let Some(value) = typed_decl.declaration.definition_value() else {
        return false;
    };

    let mut binder_names: BTreeSet<&str> = binders.iter().map(|b| b.name.as_str()).collect();

    let mut body = value;
    while let Some((lambda_binders, lambda_body)) = body.as_lambda() {
        for b in lambda_binders {
            binder_names.insert(&b.name);
        }
        body = lambda_body;
    }

    let Some((func, args)) = body.as_app() else {
        return false;
    };
    let Some(head) = func.as_var() else {
        return false;
    };
    if !postulate_names.contains(head) {
        return false;
    }
    if args.is_empty() {
        return false;
    }
    args.iter()
        .all(|arg| arg.as_var().is_some_and(|v| binder_names.contains(v)))
}

/// Produces a structural fingerprint of a module's declarations using Expr Display.
/// Two modules with identical declaration structure produce the same fingerprint
/// regardless of surface formatting differences.
pub fn module_fingerprint(module: &TypedModule) -> String {
    module
        .declarations
        .iter()
        .map(|td| {
            let name = td.declaration.name();
            let ty = td.declaration.type_annotation();
            match td.declaration.definition_value() {
                Some(val) => format!("def {name} : {ty} = {val}"),
                None => format!("postulate {name} : {ty}"),
            }
        })
        .collect::<Vec<_>>()
        .join(" | ")
}

/// Checks definitional equality by normalizing both terms and comparing canonical forms.
pub fn definitionally_equal(
    semantics: &SemanticEngine,
    module: &TypedModule,
    left: &Expr,
    right: &Expr,
) -> Result<bool, LanguageError> {
    semantics.definitionally_equal(module, left, right)
}

pub fn assert_format_contracts(text: &str) {
    assert!(
        text.ends_with('\n'),
        "formatted module must end with trailing newline"
    );

    for line in text.lines() {
        assert!(!line.contains('\t'), "tabs are not allowed");
        assert_eq!(line, line.trim_end(), "trailing whitespace is not allowed");
    }
}

pub fn invocation(args: &[&str], stdin: &str) -> CliInvocation {
    CliInvocation {
        args: args.iter().map(|s| s.to_string()).collect(),
        stdin: stdin.to_string(),
        env: BTreeMap::new(),
    }
}
