# Conformance Corpus

This directory contains fixture-driven executable specifications for the language interfaces.

- `parser/`: parse + recovery fixtures.
- `syntax/`: clause-by-clause surface syntax positive/negative fixtures used by `docs/SURFACE_SYNTAX_COVERAGE.csv`.
- `syntax/negative_expectations.csv`: expected parser/check stage + diagnostic category for every negative syntax fixture.
- `syntax/negative_message_expectations.csv`: required message fragments for key negative fixtures.
- `semantics/`: judgment outcomes and negative rule-boundary cases.
- `semantics/paper_parity.csv`: machine-readable mapping from paper examples/sections to contract IDs.
- `semantics/paper_examples.csv`: numbered paper examples with surface-language manifestations.
- `semantics/variance_examples.csv`: numbered paper examples exercised through variance-inference API contracts.
- `semantics/examples/*.spec`: executable surface-language fixtures for paper examples with surface manifestation.
- `semantics/variance/*.ditt`: executable ambient modules used by variance-inference API contracts.
- `diagnostics/`: diagnostic category/ordering fixtures.
- `cli/`: machine-readable CLI input/output snapshots.
- `notebook/`: notebook session protocol flow fixtures.
- `lsp/`: incremental language-server lifecycle fixtures.
- `lsp/jsonrpc_*.jsonl`: protocol-level LSP JSON-RPC request/response transcript fixtures.
- `notebook/jsonrpc_*.jsonl`: protocol-level notebook JSON-RPC request/response transcript fixtures.
- `stdlib/`: required standard-library module registry and canonical surface modules.
- `modules/`: import/module-resolution edge-case matrix for alias/hiding/renaming/cycle behavior.
- `modules/package_linear/`: filesystem-backed package fixture set.
- `quality/`: sample mutation/fuzz/perf gate reports used by executable quality-threshold contracts.
- `derivations/`: derivation artifact compatibility fixtures across encodings/versions.
