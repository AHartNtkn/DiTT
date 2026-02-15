# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What This Is

DiTT is a contract-first implementation of the first-order directed type theory from:

> Andrea Laretto, Fosco Loregian, Niccolo Veltri, *Di- is for Directed: First-Order Directed Type Theory via Dinaturality* (POPL 2026)

The paper PDF is at `References/2409.13237v2.pdf`. The paper is the specification — every API surface must trace to a paper rule, judgment form, or syntactic clause. If something has no paper grounding, it must be justified by implementation necessity (tooling, user interaction) or removed.

The repository is in **red-phase TDD**: all runtime methods are `unimplemented!(...)`. The product surface is specified entirely by tests and fixtures under `tests/`. Tests are expected to fail with `unimplemented` panics; they define the contracts that a future implementation must satisfy.

## Red Phase Mandate: Finalize the API Now

The purpose of the red phase is to **finalize every API surface before implementation begins.** Once implementation starts, refactoring becomes dramatically harder — you are dragging yourself out of mud. Every structural defect, every type mismatch, every unprincipled design choice that survives into green phase becomes entrenched.

This means:
1. **API defects are urgent in red phase.** A monolithic god object, a structural mismatch between related types, a missing field on a core struct — these are not "design concerns to consider later." They are defects that must be fixed now, while the cost is low.
2. **"It's just the contract phase" is not an excuse.** If two API surfaces that must interoperate have incompatible structures (e.g., `Expr` variants that cannot elaborate to their `ProofTerm` counterparts), that is a bug in the API, not an acceptable intermediate state.
3. **Red phase is harder than green phase.** Getting the API right requires more design discipline than filling in implementations. Do not treat red phase as a rough draft.

## Build and Test Commands

```bash
cargo check --tests          # Type-check everything including tests
cargo test --no-fail-fast    # Full suite (all tests panic with unimplemented in red phase)
cargo test <test_name>       # Run a single test by name
cargo test --test <file>     # Run all tests in a specific test file (e.g. --test contracts_runtime)
cargo clippy --tests         # Lint (must be zero warnings)
cargo fmt                    # Format
cargo fmt --check            # Check formatting without modifying
bash scripts/check_red_phase.sh  # Red-phase provenance gate (verifies every failure is from unimplemented!())
```

Rust edition is 2024. No runtime dependencies; dev-dependencies are `proptest`, `regex`, and `serde_json`.

## Architecture

### Crate Structure (`src/`)

```
src/
├── lib.rs                      # Crate root: pub mod api; pub mod runtime;
├── api/
│   ├── mod.rs                  # Re-exports all API modules (glob re-exports with pub use *)
│   ├── foundation.rs           # ~1700 lines: ALL domain types
│   ├── syntax.rs               # Traits: Lexer, Parser, Formatter, AstEquivalence
│   ├── semantics.rs            # Traits: TypeChecker, VarianceChecker, Normalizer, Evaluator, DerivationArtifacts
│   ├── tooling.rs              # Traits: ModuleSystem, Cli, Repl, NotebookKernel, LanguageServer
│   └── interaction.rs          # CLI/REPL/LSP/notebook data types (CliInvocation, SemanticToken, etc.)
└── runtime/
    ├── mod.rs                  # Re-exports: SyntaxEngine, SemanticEngine, ToolingEngine
    ├── syntax.rs               # SyntaxEngine: implements Lexer, Parser, Formatter, AstEquivalence
    ├── semantics.rs            # SemanticEngine: implements TypeChecker, VarianceChecker, Normalizer, Evaluator, DerivationArtifacts
    └── tooling.rs              # ToolingEngine: implements ModuleSystem, Cli, Repl, NotebookKernel, LanguageServer
```

**`ditt_lang::api::*`** is the public API surface. All domain types live in `foundation.rs`. The traits in `syntax.rs`, `semantics.rs`, and `tooling.rs` define the behavioral contracts.

The runtime is split into three subsystem engines, each implementing only the traits for its domain. All methods are `unimplemented!()` stubs in red phase. Tests import the engine(s) they need:
- `use ditt_lang::runtime::SyntaxEngine;` — parsing, formatting, AST equivalence
- `use ditt_lang::runtime::SemanticEngine;` — type checking, normalization, evaluation, derivation
- `use ditt_lang::runtime::ToolingEngine;` — module system, CLI, REPL, notebook, LSP

### foundation.rs Domain Model

The key type hierarchies, mapping to paper concepts:

- **`Expr`** — Surface expression AST spanning Figures 8/9/11/16 plus surface sugar. Variants: `Var`, `Lambda`, `App`, `Arrow`, `Hom`, `Product`, `Pair`, `Proj`, `Opposite`, `Top`, `End`, `Coend`, `Refl`, `JElim`, `EndIntro`, `EndElim`, `CoendIntro`, `CoendElim`. The end/coend intro/elim variants carry structured fields (binders, witnesses, continuations) sufficient for elaboration to `ProofTerm`. Has factory constructors (`Expr::var()`, `Expr::lambda()`, ...) and decomposition accessors (`as_var()`, `as_lambda()`, ...).
- **`CatType`** — Category-level types (Figure 7): `α | B | C^op | [C,D] | Top | C × D`. Variants: `Base` (Σ_B signature symbols), `Var` (bound category variables), `FunCat`, `Product`, `Opposite`, `Top`.
- **`Predicate`** — Predicate forms (Figure 9). Variants: `Top`, `Conj`, `Hom`, `End`, `Coend`, `Opposite`, `Var`, `App`, `Arrow`.
- **`ProofTerm`** — Proof term constructors (Figures 11/16 entailment rules). Variants: `Var`, `Lambda`, `App`, `Pair`, `Proj`, `Refl`, `JElim`, `EndIntro`, `EndElim`, `CoendIntro`, `CoendElim`. `ProofTerm::from_expr` handles App (left-fold) and all end/coend variants; Lambda is intentionally unhandled (sort-ambiguous between term and proof level; the elaborator disambiguates).
- **`Term`** — Core term syntax (Figure 8).
- **`Binder`** — `{ name: String, ty: Box<CatType> }`. Used in lambdas, ends/coends, and term/proof binders.
- **`Context` / `ContextBinding`** — Typing contexts. `ContextBinding` carries `name: String`, `ty: CatType`, and `variance: Variance`. `Context::opposite()` flips covariant↔contravariant and applies `CatType::Opposite` with double-opposite reduction.
- **`EntailmentJudgment`** — The central derivation form `[Γ] Φ ⊢ α : P` as a flat struct: `{ context, propositions, proof_term, goal }`.
- **`CheckJudgment`** — Judgment forms checked without proof terms: `TypeWellFormed`, `TypeEquality`, `ContextWellFormed`, `VariableInContext`, `PredicateWellFormed`, `PropCtxWellFormed`, `TermTyping`, `EntailmentEquality`.
- **`InferenceRule`** — 17-variant enum covering proof-term-constructing rules (Figures 11, 16). Equational rules handled by `Normalizer`; variance rules by `VarianceChecker`.
- **`Variance`** — `Covariant`, `Contravariant`, `Dinatural`, `Unused` (Figure 10/13/14).
- **Error types** — `LanguageError` with variants for each phase (`Syntax`, `StaticSemantics`, `DynamicSemantics`, `ModuleSystem`, `Interaction`, `DerivationArtifact`), each wrapping a `DiagnosticBundle`. Error descriptions use domain-level language (e.g., `"unexpected_expression"`, `"category type"`) not internal Rust paths.

### Test Architecture (`tests/`)

79 test files. Two test support modules used via Rust's integration test `mod` mechanism:

- **`support.rs`** — Used by 28 test files (`mod support;`). Provides `compile_checked(&SyntaxEngine, &SemanticEngine, source)`, `entailment(name)`, `entailment_in_context(name, context)`, `definitionally_equal(&SemanticEngine, module, left, right)`, fixture module strings.
- **`conformance_support.rs`** — Used by 36 test files (`mod conformance_support;`). Provides `read_fixture()`, `fixture_path()`, `check_accepts()`, `check_rejects()`, `assert_rule_semantic_boundary()`, CSV parsing. Uses `RuleCategory` enum to classify rules as derivations, checks, equational laws, variance rules, or meta-properties.

These are independent modules (Rust integration tests compile each `.rs` as a separate crate). Many test files import both. They cannot cross-import due to the module system.

### Conformance Fixtures (`tests/conformance/`)

Declarative fixture corpus organized by concern:
- `syntax/positive/`, `syntax/negative/` — Surface syntax accept/reject fixtures per clause
- `semantics/` — Judgment outcome fixtures, paper example `.spec` files, `.ditt` modules
- `semantics/examples/` — Paper example specs (e.g., `ex3_2.spec`, `ex6_2.spec`)
- `semantics/variance/` — Variance analysis fixtures
- `parser/` — Parse + recovery fixtures (`.ditt` files), format constraints
- `diagnostics/` — Diagnostic category/ordering fixtures
- `cli/`, `notebook/`, `lsp/` — Protocol-level JSON-RPC transcript fixtures
- `stdlib/` — Standard library module registry
- `modules/` — Import/resolution edge cases (e.g., `package_linear/`)
- `derivations/` — Schema compatibility fixtures
- `quality/` — Quality gate fixtures

### Test Naming Convention

Test files follow the pattern `contracts_<domain>.rs`. Paper-rule tests use `contracts_paper_rules_figure<N>.rs`. Tests within files are verbose and descriptive (e.g., `figure16_end_iso_r_rule_has_semantic_boundary_in_ends_coends_suite`).

### Scripts (`scripts/`)

- `check_red_phase.sh` — Delegates to `check_red_phase_provenance.sh`; verifies every failing test fails due to `unimplemented!()`, not compile errors or spec gaps.
- `run_full_contract_suite.sh` — Runs `cargo test --no-fail-fast`.
- `check_paper_parity.sh`, `check_schema_compat.sh`, `check_mutation_gate.sh` — Additional verification gates.
- `fuzz_smoke.sh`, `run_perf_contracts.sh`, `run_quality_contracts_live.sh` — Specialized test lanes.
- `regenerate_corpus_lock.sh` — Regenerates the corpus lock file.

### Documentation (`docs/`)

- `SURFACE_SYNTAX_CONTRACT.md` / `SURFACE_SYNTAX_COVERAGE.csv` — Surface language grammar spec and coverage.
- `PAPER_RULE_COVERAGE.csv` / `PAPER_PROVENANCE.csv` — Paper rule traceability.
- `PAPER_PARITY.md` — Paper-to-implementation parity tracking.
- `DIAGNOSTICS_SCHEMA.md` — Diagnostic structure specification.
- `FEATURE_REGISTRY.csv` — Language feature registry.
- `TEST_MATRIX.md` — Test organization matrix.
- `CLI_CONTRACT_COVERAGE.csv` — CLI command coverage.
- `CORPUS_LOCK.csv` — Corpus drift detection lock.
- `GREEN_PHASE_READINESS.md` — Checklist for transitioning to green phase.
- `RULE_TRACEABILITY.md` — End-to-end rule traceability.

## Design Standard

This codebase aims for correctness and elegance, not pragmatism. Every API surface, every type, every test must be the principled version — not the version that "works for now."

1. **The paper is the specification.** Every API surface must trace to a paper rule, judgment form, or syntactic clause.
2. **Separate concerns cleanly.** If the paper distinguishes two concepts, the API must distinguish them at the type level.
3. **Never dismiss a valid design issue as "current design works."** If it's unprincipled, fix it.
4. **Never defer a fix because it's large.** If the right thing requires touching 50 files, touch 50 files.
5. **API contracts are phase-invariant**: the public API must be finalized in red phase and must not change when switching to green phase.

## Product Direction (Locked)

1. DiTT is a proof-oriented programming language based on the paper's directed type theory.
2. The core theory is fixed to the paper: do not add new type constructors beyond what the theory already provides (including impredicative encodings via (co)ends).
3. Use judgment-oriented language terminology; do not reframe as a natural-deduction theorem prover.
4. No effects in core language contracts.
5. Required language features: local modules, implicit arguments, tuple pattern matching for product structure.
6. Syntax is Agda-like with built-ins for directed constructs and (co)ends.
7. Paper notation mapping: `[C, D]` → `C -> D` (or `C → D`); `hom_C(a, b)` → `a ->[C] b` (or `a →[C] b`); `∫`/`∫^` accepted as unicode and as ASCII `end`/`coend`.

## Contract-First Rules

1. Tests specify semantic behavior and interface contracts, not algorithms or backend choices.
2. Surface-language behavior is the contract boundary; paper examples should be tested as surface programs.
3. Formatting contracts must be equivalence-preserving and constraint-based, not exact byte snapshots.
4. Diagnostics contracts focus on category, severity, message quality, and span validity/order.
5. Failures should come from `unimplemented!(...)`, not incomplete specs.
6. Error contracts must be explicit and complete at the API boundary.
7. Public domain-model structures (`Expr`, `Declaration`, `SurfacePattern`, `SurfaceLetExpr`, `TermBinder`, etc.) are part of the API contract. Internal engine representation is not user-facing.

## Architecture Guardrails

1. `tests/` defines verification only; `src/` defines implementation architecture.
2. Keep testing vocabulary (`contract`, `stub`, `fallback`, `red_phase`) out of `src/` module structure.
3. `src/` must be organized by implementation domains (syntax, semantics, tooling), not by testing phase.
4. Never couple `src/` modules to conformance corpus structure, parity CSVs, or test registry mechanics.
5. Missing behavior must fail hard and loudly — no graceful-degradation/fallback execution paths.
6. Each subsystem engine (`SyntaxEngine`, `SemanticEngine`, `ToolingEngine`) implements only its own traits. No engine implements traits from another subsystem.

## EDICT: No "Pre-existing" Dismissals

**NEVER describe a bug, issue, or problem as "pre-existing."** It does not matter when a bug was introduced. What matters is whether it is fixed. Labeling something "pre-existing" is a way of implying it's not your responsibility, which is irrelevant — if you see it, deal with it. Do not use the words "pre-existing", "pre existing", "already existed", "was already broken", or any synonym to characterize a problem. Just describe the problem and fix it or flag it.

## When Confronted About a Mistake

**NEVER reflexively agree.** When the user points out a problem:

1. **Check the facts first.** Re-read what you actually did before responding.
2. **Do not say "You're right" unless you have verified the claim is true.**
3. **Do not fabricate explanations.** If you don't know why something went wrong, say so.
4. **Do not assume what the user is claiming.** If unclear, ask.
5. **Answer questions literally.** If asked "Did you do X?", check whether you did X and answer yes or no.
