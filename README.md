# DiTT

DiTT is a contract-first implementation of the first-order directed type theory from:

- Andrea Laretto, Fosco Loregian, Niccolo Veltri, *Di- is for Directed: First-Order Directed Type Theory via Dinaturality* (POPL 2026)
- PDF in this repo: `References/2409.10237v2.pdf`

## Current Status

This repository is in **red-phase TDD**.

- The runtime subsystem APIs in `src/runtime/{syntax,semantics,tooling}.rs` are intentionally `Unimplemented("...")`.
- The expected failing mode is enforced by `scripts/check_red_phase.sh`.
- The product surface is specified by tests and fixtures under `tests/`.

So today, this repo defines the intended language/contracts; it does not yet provide a working implementation.

## What Is Specified Today

## 1. Surface language contract

Concrete syntax and coverage are specified in:

- `docs/SURFACE_SYNTAX_CONTRACT.md`
- `docs/SURFACE_SYNTAX_COVERAGE.csv`
- `tests/conformance/syntax/*`

Including proof-term forms:

- `refl t`
- `J h [e]`
- `end alpha`, `end^-1 beta`
- `coend alpha`, `coend^-1 beta`
- quantifier forms `end (x : C). P` / `coend (x : C). P` (and unicode variants)

Judgmental equality model (user-facing contract):

- DiTT does not expose a propositional equality type for users to inhabit.
- `=` in source code is a definition separator (`name : A = term`), not an equality proposition.
- Paper equations (for example, cut coherence and end adjoint isomorphism equations) are enforced as judgmental convertibility: a term inferred at form `B` must be accepted when a context asks for form `A` exactly when the checker establishes `A` and `B` as judgmentally equal.

Paper-to-surface notation mapping used in this repo:

- Paper function/functor constructor `[C, D]` is written in surface form as `C -> D` (unicode: `C → D`).
- Paper hom `hom_C(a, b)` is written as `a ->[C] b` (unicode: `a →[C] b`).
- Paper ends/coends `∫` / `∫^` are accepted as unicode and as ASCII `end` / `coend`.

## 2. Paper examples corpus

Paper examples are tracked as dedicated fixtures/contracts:

- registry: `tests/conformance/semantics/paper_examples.csv`
- appendix registry: `tests/conformance/semantics/paper_appendix_examples.csv`
- fixtures: `tests/conformance/semantics/examples/ex*.spec`
- dedicated contracts: `tests/contracts_paper_examples_dedicated.rs`
- appendix contracts: `tests/contracts_paper_appendix_examples.rs`
- structural/API fidelity checks: `tests/contracts_paper_examples_api.rs`

Covered examples include 2.4, 2.10, 3.1-3.11, 6.1-6.5, variance examples 2.6/2.7/2.11, and appendix examples B.1-B.5, C.1-C.3, D.1-D.3.

## 3. Rule and provenance tracking

Paper rule/example provenance and registry constraints are tracked in:

- `docs/PAPER_RULE_COVERAGE.csv`
- `docs/PAPER_PROVENANCE.csv`
- `tests/contracts_paper_rule_coverage.rs`
- `tests/contracts_paper_provenance.rs`

Rule coverage includes:

- Figure 10 variance-side-condition contracts (`f10_cov_*`, `f10_contra`, `f10_unused`)
- Figure 13 unused-variable rule contracts (`f13_*`)
- Figure 14 full variance-side-condition family contracts (`f14_*`)
- Figure 15 cut equational-family contracts (`f15_*`)
- Figure 16/17 end adjoint-form + functoriality contracts (`f16_*`, `f17_*`)
- Figure 11 entailment/equality contracts (`var` through `j_eq`)

## Running The Contract Suite

Common commands:

- Red-phase provenance gate:
  - `bash scripts/check_red_phase.sh`
- Full test suite:
  - `cargo test --no-fail-fast`

In red phase, failures are expected; they must be attributable to `Unimplemented("...")` boundaries.

## Important Scope Boundaries

- `tests/` and `docs/` define the language/API contract.
- `src/` defines implementation architecture; currently stubbed.
- No effects are part of the core language contracts.
- Core theory is locked to the paper (directed equality, dinaturality, (co)ends-as-quantifiers).
