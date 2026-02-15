# DiTT Surface Syntax Contract

This document defines the user-facing concrete syntax contract.
It specifies accepted source forms and canonical printed forms.
Machine-checked clause-to-test map: `docs/SURFACE_SYNTAX_COVERAGE.csv`.

## Normative Clause Registry

- `[clause:module_header]` File module header requires `module A.B where`.
- `[clause:local_modules]` Local module declarations are accepted with explicit `where`.
- `[clause:import_basic]` Import basic form `import X`.
- `[clause:import_alias]` Import alias form `import X as Y`.
- `[clause:import_clauses]` Import clauses `using/hiding/renaming`.
- `[clause:reserved_words]` Reserved words cannot be identifiers.
- `[clause:unicode_identifiers]` Unicode identifiers are accepted.
- `[clause:identifier_digit_start]` Identifiers may not start with digits.
- `[clause:one_line_definition]` Top-level definitions are one-line typed definitions.
- `[clause:duplicate_top_level]` Duplicate top-level names are rejected.
- `[clause:lambda_forms]` Lambda forms `\x. t` and `λx. t`.
- `[clause:arrow_forms]` Arrow forms `->` and `→`.
- `[clause:directed_hom_notation]` Directed hom notation `a ->[C] b` / `a →[C] b`.
- `[clause:refl_term]` Reflexivity proof term form `refl t`.
- `[clause:directed_j_eliminator]` Directed elimination proof term form `J h [e]`.
- `[clause:end_coend_proof_operators]` (Co)end proof operators `end α`, `end⁻¹ β`, `coend α`, `coend⁻¹ β`.
- `[clause:opposite_notation]` Opposite notation `C^`.
- `[clause:tuple_projection]` Tuple/projection forms `(a, b)`, `p.1`, `p.2`.
- `[clause:annotated_patterns]` Patterns may carry type annotations `(p : A)`.
- `[clause:let_forms]` Let forms with typed/untyped binder.
- `[clause:let_chaining]` Let chaining and canonical multi-binding form.
- `[clause:end_coend_quantifiers]` (Co)end quantifier forms and binder requirements.
- `[clause:comments]` C-style line/block comments.
- `[clause:precedence_projection_application]` Projection binds tighter than application.
- `[clause:precedence_product_arrow]` Product binds tighter than arrow.
- `[clause:arrow_right_associativity]` Arrow is right-associative.
- `[clause:implicit_named_args]` Explicit implicit arguments use named form `{x = t}`.
- `[clause:binder_grouping]` Binder grouping and canonical binder splitting.
- `[clause:no_where_blocks]` `where` blocks are not part of expression syntax.
- `[clause:top_shared_bottom_forbidden]` Shared top/unit allowed; bottom excluded.

## Scope

- This is a concrete syntax contract for user code, fixtures, and examples.
- Kernel/internal representation is not part of this contract.
- Core/debug pretty-printing may use disambiguating notation (for example, category variables rendered as `'x`); that notation is internal and is not part of accepted surface syntax.
- The theory remains first-order directed type theory as in the referenced paper.
- Size stratification is a semantic/meta constraint; there is no surface universe syntax.
- There is no user-facing propositional equality connective/type in surface syntax.
- Judgmental equality is observed through convertibility at type-check time (a term of inferred form `B` is accepted where form `A` is required when `A` and `B` are judgmentally equal).

## File and Module Forms

- Package/module files must start with:
  - `module A.B where`
- Local modules are allowed inside modules:
  - `module Outer where`
  - `module Inner where`
  - `  postulate C : Cat`
- Snippets/REPL cells may omit a module header.
- Source module path separator is `.`.
- Top-level declarations are newline-separated; no semicolon terminator.

## Imports

- Import form:
  - `import X`
  - `import X as Y`
- Optional clauses:
  - `using (f, g)`
  - `hiding (f, g)`
  - `renaming (f to g)`
- Clauses are composable on one import.
- `using`/`hiding` entries are names only (no mixfix/operator entries).
- Qualified reference form is `Y.f`.
- In REPL snippets, imports are command-level (not source-level), e.g. `:import X as Y`.

## Reserved Words

Reserved words are:

- `module`
- `where`
- `import`
- `as`
- `using`
- `hiding`
- `renaming`
- `postulate`
- `let`
- `in`
- `end`
- `coend`

## Identifiers

- Unicode identifiers are allowed.
- ASCII identifiers are valid.
- Digits are allowed after the first character, not as first character.

## Declarations and Definitions

- Category/type assumptions use `postulate`:
  - `postulate C : Cat`
- Postulate blocks are accepted:
  - `postulate`
  - `  C : Cat`
  - `  D : Cat`
- Canonical print groups consecutive postulates into a block.
- In this corpus, `postulate` is for base parameters/ambient assumptions only; derivable judgment obligations must be checked via contracts, not assumed as postulates.

- Top-level value definitions are one-line typed definitions:
  - `id (x : C) : C = x`
  - `id : C -> C = \x. x`
  - `id : C -> C = λx. x`
- In definitions, `=` is a declaration separator between type annotation and defining term.
- `=` is not a user-level proposition former.

- Every top-level definition requires an explicit type annotation.
- Duplicate top-level names are an error.
- No standalone top-level equation declaration form.

## Binders and Application

- Explicit binder: `(x : A)`
- Implicit binder: `{x : A}`
- Quantifier binders are explicit only.
- Application is juxtaposition only:
  - `f x y`
- Explicit implicits are named:
  - `f {x = t}`

- Binder grouping accepts:
  - `(x : A) (y : A)`
  - `(x y : A)`
- Canonical print uses one binder per group:
  - `(x : A) (y : A)`

- Explicit/implicit binder order is parser-permissive.
- Canonical print preserves author order (no binder-class reordering).

## Lambdas and Arrows

- Lambda forms:
  - Unicode: `λx. t`
  - ASCII: `\x. t`

- Arrow forms:
  - Unicode: `A → B`
  - ASCII: `A -> B`

- `→`/`->` is reused for function and implication notation.

## Directed Equality (Hom-Type) Notation

- Morphism type:
  - Unicode: `a →[C] b`
  - ASCII: `a ->[C] b`
- Parser accepts spacing variants.
- Canonical print:
  - Unicode: `a →[C] b`
  - ASCII: `a ->[C] b`

- Opposite notation:
  - `C^`

## Proof Terms

- Reflexivity proof term:
  - `refl t`
  - `refl (t)`
- Directed `J` eliminator:
  - `J h [e]`
  - `J (h) [e]`
- The eliminator argument in brackets is required.
- (Co)end proof operators:
  - `end α`
  - `end⁻¹ β` (ASCII fallback: `end^-1 β`)
  - `coend α`
  - `coend⁻¹ β` (ASCII fallback: `coend^-1 β`)
  - Parentheses may still be used for grouping complex arguments, e.g. `end (\x. body)` and `coend (coend^-1 h)`.

## Products, Tuples, and Projections

- Product/conjunction symbols:
  - Unicode: `×`
  - ASCII: `*`
- `×`/`*` is reused across type and proposition layers.
- Tuple constructor:
  - `(a, b)`
- Projections:
  - `p.1`
  - `p.2`

- Tuple patterns are supported in:
  - function parameters
  - `let` bindings

- Annotated patterns carry a type annotation:
  - `(p : A)` where `p` is any pattern
  - Extends the paper's typed binders (`Γ, x : C`) to pattern positions.
  - Annotation is checked against the inferred type; mismatch is an error.

## Let Expressions

- Accepted:
  - `let x : A = t in u`
  - `let x = t in u`
- Inference failure for untyped `let` bindings is an error.

- Chaining accepts both:
  - nested `let`
  - multi-binding `let x = ...; y = ... in ...`
- Canonical print uses multi-binding form.

- `where` blocks are not part of the surface syntax.

## Quantifiers via (Co)Ends

- Unicode/default:
  - `∫ (x : C). P`
  - `∫^ (x : C). P`
- ASCII alternatives:
  - `end (x : C). P`
  - `coend (x : C). P`

- Parser accepts nested and multi-binder forms.
- Canonical print uses multi-binder form:
  - `∫ (x : C) (y : D). P`
  - `∫^ (x : C) (y : D). P`

- Binder parentheses are required.

## Top/Unit and Bottom

- Shared top/unit:
  - Unicode: `⊤`
  - ASCII: `Top`

- Bottom is not part of the surface language.

## Comments

- Line comments:
  - `// ...`
- Block comments:
  - `/* ... */`

## Precedence and Associativity

- Projections (`.1`, `.2`) bind tighter than application.
- Application binds tighter than infix operators.
- `*` / `×` bind tighter than `->` / `→`.
- `->` / `→` are right-associative.
