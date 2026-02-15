# DiTT Test Matrix

## Completion Criteria

The corpus is feature-complete only when:
- all required non-ignored contracts pass in green phase;
- no paper-parity row is `missing`;
- diagnostics schema, artifact compatibility, and deterministic-output contracts pass;
- quality gates (perf/mutation/fuzz) satisfy their thresholds.

Current repository phase:
- `red`: contracts are expected to fail with `Unimplemented(...)`.
- enforced by `.github/workflows/ci.yml` + `scripts/check_red_phase.sh`.

## Ownership

| Area | Owner | Primary Contracts | Pass Criteria |
|---|---|---|---|
| Paper parity | `Language Core` | `tests/contracts_paper_parity.rs`, `tests/contracts_paper_examples_api.rs`, `tests/contracts_paper_examples_dedicated.rs`, `tests/contracts_paper_appendix_examples.rs`, `tests/contracts_variance_inference.rs`, `tests/contracts_paper_rule_coverage.rs`, `tests/conformance/semantics/paper_parity.csv`, `tests/conformance/semantics/paper_examples.csv`, `tests/conformance/semantics/paper_appendix_examples.csv`, `tests/conformance/semantics/variance_examples.csv`, `tests/conformance/semantics/examples/*.spec`, `tests/conformance/semantics/variance/*.ditt`, `docs/PAPER_RULE_COVERAGE.csv` | 0 missing rows, valid contract links, full numbered-example registry, executable fixture per parity row (surface or variance API), one dedicated test per numbered example, and full rule matrix coverage |
| Paper provenance | `Language Core` | `tests/contracts_paper_provenance.rs`, `docs/PAPER_PROVENANCE.csv` | every rule/example in coverage registries carries explicit section/page/label provenance metadata |
| Core semantics | `Type Theory` | `tests/contracts_type_theory.rs`, `tests/contracts_negative_semantics.rs`, `tests/contracts_implicit_args.rs`, `tests/contracts_tuple_patterns.rs`, `tests/contracts_ends_coends.rs`, `tests/contracts_elaboration.rs`, `tests/contracts_judgment_forms.rs`, `tests/contracts_finite_model_oracle.rs` | directed rules hold; forbidden judgments rejected; implicit arguments and tuple/product matching obey contracts; end/coend surface forms are supported; surface-to-core elaboration maps valid forms correctly and rejects invalid ones; compound-term judgment forms exercise all factory constructors through derive |
| Meta-theory | `Type Theory` | `tests/contracts_meta_theory.rs` | substitution/renaming/weakening/exchange and coherence laws |
| Frontend | `Frontend` | `tests/contracts_frontend.rs`, parser fixtures in `tests/conformance/parser/` | deterministic parse/recovery + equivalence-preserving formatting under declarative constraints |
| Surface syntax matrix | `Frontend` | `tests/contracts_surface_syntax_matrix.rs`, `tests/contracts_surface_syntax_coverage.rs`, `tests/contracts_surface_syntax_doc_sync.rs`, `tests/contracts_surface_precedence.rs`, `tests/contracts_surface_ascii_unicode_equivalence.rs`, `tests/contracts_surface_formatter_canonicalization.rs`, `tests/contracts_surface_recovery_determinism.rs`, `tests/contracts_surface_roundtrip_corpus.rs`, `tests/contracts_surface_diagnostics_corpus.rs`, `tests/contracts_import_clauses.rs`, `tests/contracts_import_clause_conflicts.rs`, `tests/contracts_identifiers_reserved.rs`, `tests/conformance/syntax/*`, `tests/conformance/syntax/negative_expectations.csv`, `docs/SURFACE_SYNTAX_COVERAGE.csv` | every surface clause has positive+negative fixtures, linked contract IDs, doc/csv sync, deterministic recovery coverage, corpus-wide roundtrip/idempotence, and diagnostics category/span contracts |
| Surface formatting corpus | `Frontend` | `tests/contracts_surface_formatting_corpus.rs` | objective formatting constraints hold across full non-negative corpus while preserving semantics |
| No postulated obligations guard | `Type Theory` | `tests/contracts_no_postulated_obligations.rs` | conformance fixtures do not reintroduce judgment obligations as postulates |
| Frontend surface parity | `Tooling` | `tests/contracts_surface_frontend_parity.rs`, full syntax fixtures in `tests/conformance/syntax/positive/*.ditt` and `tests/conformance/syntax/negative/*.ditt` | parser/CLI/REPL/notebook/LSP accept/reject identical snippets consistently for full syntax corpus |
| Fixture hygiene | `Conformance` | `tests/contracts_fixture_hygiene.rs` | fixtures and spec docs contain no unresolved marker tokens |
| Derivation artifacts | `Derivation Infrastructure` | `tests/contracts_derivation_artifacts.rs`, `tests/contracts_derivation_compatibility.rs`, `tests/conformance/derivations/*` | derivation export/normalize/validate shape contracts + compatibility across fixture encodings |
| Runtime | `Runtime` | `tests/contracts_runtime.rs`, `tests/contracts_limits.rs` | determinism/progress/subject reduction + limit handling |
| Tooling surfaces | `Tooling` | `tests/contracts_tooling.rs`, `tests/contracts_protocol_state.rs`, `tests/contracts_cli_repl_notebook.rs`, `tests/contracts_cli_command_surface.rs` | stable CLI/REPL/notebook/LSP behavior including build/fmt/repl/lsp/notebook command surfaces, explicit human-vs-json CLI mode contracts, and LSP definition/rename/semantic tokens |
| Protocol transcripts | `Tooling` | `tests/contracts_protocol_jsonrpc_corpus.rs`, `tests/conformance/lsp/jsonrpc_*.jsonl`, `tests/conformance/notebook/jsonrpc_*.jsonl` | protocol envelopes, request/response ordering, id coherence, cancellation behavior, error envelope shape, initialize handshake, method-not-found handling, invalid-params handling, and method-specific request/response payload-shape contracts hold |
| Module-system edges | `Tooling` | `tests/contracts_module_system_edges.rs`, `tests/contracts_module_resolution_exhaustive.rs`, `tests/conformance/modules/import_resolution_cases.csv` | duplicate names, import cycles, alias/using/hiding/renaming conflicts, and transitive ambiguities are rejected with structured errors |
| Cross-surface consistency | `Tooling` | `tests/contracts_cross_surface_consistency.rs`, `tests/contracts_run_consistency.rs` | API/CLI/LSP agreement on semantic outcomes and run/check/normalize consistency, including cross-surface semantic alignment of value/normal-form rendering across API, CLI, REPL, and notebook |
| Cross-surface diagnostics parity | `Tooling` | `tests/contracts_cross_surface_diagnostics_parity.rs` | parser/CLI/REPL/notebook/LSP align on diagnostic count/order/category/severity, span ordering/presence, and message-quality signatures for shared failing inputs |
| Conformance corpus | `Conformance` | `tests/contracts_conformance.rs` | fixture-backed semantic outcomes and reproducibility |
| Artifact/migration | `Build Systems` | `tests/contracts_derivation_artifacts.rs`, artifact fixtures | stable digest + version migration policy |
| Diagnostics schema | `Diagnostics` | `tests/contracts_diagnostics_schema.rs`, `tests/contracts_surface_diagnostics_corpus.rs`, `tests/conformance/diagnostics/catalog.csv`, `tests/conformance/syntax/negative_message_expectations.csv` | category/message/span contracts, key message-fragment quality constraints for negative fixtures, and deterministic report ordering |
| Error API surface | `Release Engineering` | `tests/contracts_error_api_surface.rs`, `src/api/foundation.rs` | public `LanguageError` surface remains explicit and does not regress to generic error buckets |
| Cross-platform | `Platform` | `tests/contracts_cross_platform.rs` | LF/CRLF, URI/path, Unicode normalization invariance |
| Determinism stress lane | `Runtime` | `tests/contracts_determinism_stress_lane.rs` | repeated randomized-order runs preserve deterministic outputs for parse/recovery/CLI pathways |
| Security/sandbox | `Security` | `tests/contracts_security.rs`, `tests/contracts_no_effects_boundary.rs` | no unintended side effects in hostile inputs; effect-like surface constructs are rejected |
| Differential oracle | `Type Theory` | `tests/contracts_differential_oracle.rs` | implementation outcomes align with reference oracle for all judgment kinds |
| Property contracts | `Verification` | `tests/contracts_properties.rs`, `tests/contracts_metamorphic.rs`, `tests/contracts_metamorphic_semantic_pack.rs` | proptests enforce alpha/import/local-module/implicit/tuple/end-coend/whitespace/binder/lambda/let equivalence invariants across generated cases |
| Standard library | `Language Core` | `tests/contracts_stdlib.rs`, `tests/conformance/stdlib/*`, `tests/conformance/stdlib/api_lock.csv` | required stdlib modules are registry-backed, API-locked, parse/typecheck, and compose in acyclic dependency graph |
| Release workflow | `Release Engineering` | `tests/contracts_release_workflow.rs` | end-to-end workflow contract remains coherent |
| Performance | `Performance` | `tests/contracts_performance.rs` | budgets met in perf lane |
| Mutation/Fuzz | `Verification` | `tests/contracts_quality_gate_registry.rs`, `scripts/check_mutation_gate.sh`, `scripts/fuzz_smoke.sh`, `scripts/run_perf_contracts.sh`, `scripts/run_quality_contracts_live.sh` | thresholds met, and live quality reports satisfy executable contracts when produced |
| Red-phase provenance | `Release Engineering` | `tests/contracts_red_phase_provenance_gate.rs`, `scripts/check_red_phase.sh`, `scripts/check_red_phase_provenance.sh` | every red-phase failing test is attributable to `Unimplemented(...)` boundaries |
| CLI contract exhaustiveness | `Tooling` | `tests/contracts_cli_exhaustiveness.rs`, `docs/CLI_CONTRACT_COVERAGE.csv` | declared CLI command forms/options are all mapped to executable contract coverage |
| Registry closure | `Release Engineering` | `tests/contracts_registry_closure.rs` | every executable contract test is tracked by at least one registry or matrix reference, and registry contract IDs resolve to executable tests |
| Src architecture guardrails | `Release Engineering` | `tests/contracts_src_architecture_guardrails.rs` | implementation source tree avoids test/process-artifact naming and does not couple to test/conformance corpus paths |
| Corpus drift lock | `Release Engineering` | `tests/contracts_corpus_drift_lock.rs`, `docs/CORPUS_LOCK.csv`, `scripts/regenerate_corpus_lock.sh` | fixture/registry/doc digest manifest (SHA-256 + size) matches repository state and target set |
| Green-phase readiness | `Release Engineering` | `tests/contracts_green_phase_readiness.rs`, `docs/GREEN_PHASE_READINESS.md` | ignored readiness contracts define exact criteria for switching from red-phase to pass-all green-phase gating |
| Fixture traceability | `Conformance` | `tests/contracts_fixture_traceability.rs` | every fixture is referenced by at least one executable contract path and coverage rows are non-orphaned |
| Feature registry | `Release Engineering` | `tests/contracts_feature_registry.rs`, `docs/FEATURE_REGISTRY.csv` | single source of truth maps features to clauses, fixtures, and executable contracts without gaps |
| Test matrix traceability | `Release Engineering` | `tests/contracts_test_matrix_traceability.rs` | every matrix row references at least one executable test target |

## CI Mapping

- Required red-phase CI: `.github/workflows/ci.yml`
- Manual advanced gates: `.github/workflows/quality-gates.yml`
- Scheduled advanced gates: `.github/workflows/nightly-quality.yml`
