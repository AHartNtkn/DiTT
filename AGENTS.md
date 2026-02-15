# AGENTS Policy

This repository is strict TDD/spec-first.

## Non-Negotiable Rules

1. Placeholders are forbidden in tests, fixtures, and spec docs.
2. If a requirement is unclear, ask the user; do not leave unresolved marker text or "future work" notes.
3. Implementations may be placeholders during the contract-first stage, but tests must represent the intended final behavior and interfaces.
4. Contract tests must assert semantics at the API boundary, not internal implementation details.
5. Any added fixture must be executable by existing test wiring (not metadata-only naming).
6. Do not blindly trust user assertions about paper semantics. If a request conflicts with the paper, existing contracts, or formal definitions, explicitly call out the conflict and ask for clarification instead of silently following it.
7. If you detect a clear defect while executing the requested work, fix it immediately without asking for additional approval. Only stop to ask the user when requirements are genuinely ambiguous or the action is destructive/out-of-scope.
8. API contracts are phase-invariant: the public API (including the full error interface) must be finalized in red phase and must not change when switching between red and green phases.

## Compatibility Policy

1. Backward compatibility is forbidden as a design goal.
2. NEVER add compatibility shims, aliases, fallback paths, or dual APIs solely to preserve older interfaces.
3. When a more principled design conflicts with existing interfaces, perform a direct breaking change and update contracts/docs in the same change.
4. Technical debt reduction and semantic clarity take priority over preserving legacy call patterns.

## Product Direction (Locked)

1. DiTT is a proof-oriented programming language based on the paper's directed type theory.
2. The core theory is fixed to the paper: do not add new type constructors beyond what the theory already provides (including impredicative encodings via (co)ends).
3. Do not reframe the system as a natural-deduction theorem prover; use judgment-oriented language terminology.
4. No effects in core language contracts.
5. Required language features include local modules, implicit arguments, and tuple pattern matching for product structure.
6. Syntax should stay Agda-like with built-ins for directed constructs and (co)ends.
7. Internal kernel/core representation is an implementation detail and must not be a user-facing contract surface. Public domain-model structures that represent the surface language itself (for example `Expr`, `Declaration`, `SurfacePattern`, `SurfaceLetExpr`, `Binder`, and typed declaration/type structure) are part of the API contract and are not treated as internal kernel representation.

## Contract Style

1. Tests must specify semantic behavior and interface contracts, not algorithms or backend choices.
2. Surface-language behavior is the contract boundary; paper examples should be tested as surface programs.
3. Formatting contracts must be equivalence-preserving and constraint-based (line length, indentation, whitespace rules), not exact byte snapshots.
4. Diagnostics contracts should focus on category, severity, message quality, and span validity/order; stable diagnostic codes are not required.
5. CLI contracts must include both run modes:
   - entrypoint evaluation (`run --entry ...`)
   - normalization rendering (`run --normalize ...`)
6. Keep the contract-first property: failures should come from `Unimplemented(...)`, not incomplete specs.
7. Error contracts must be explicit and complete at the API boundary; avoid placeholder/generic error buckets that defer classification to implementation phase.

## Contract-First Expectation

- Contract suites should fail because behavior is unimplemented, not because the spec corpus is incomplete.

## Architecture Guardrails (Session-Critical)

1. Follow user intent, not literal loopholes. If wording and intent diverge, stop and resolve the intent explicitly before editing.
2. Do not treat test scaffolding as product architecture. `tests/` defines verification only; `src/` defines implementation architecture.
3. Keep testing vocabulary out of implementation module structure. Do not organize `src/` around terms like `contract`, `stub`, `fallback`, `red_phase`, or similar process labels.
4. `src/` must be organized by implementation domains (e.g., syntax, core, elaboration, runtime, tooling), not by testing phase.
5. Do not introduce graceful-degradation/fallback execution paths in core implementation architecture. Missing behavior must fail hard and loudly.
6. Never couple implementation modules to conformance corpus structure, parity CSVs, or test registry mechanics.
7. If asked to define interfaces, design them to be implementable as real subsystems, not as a monolithic test harness surface.
8. Before major refactors, check for architecture smell explicitly: god modules, god objects, phase-labeled modules, and test-term leakage into `src/`.
9. When a user calls out architectural mismatch, prioritize structural correction over incremental patching.
10. If a user assertion is incorrect on semantics, say so immediately and explain the conflict with concrete paper/system references.
