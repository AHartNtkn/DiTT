# Diagnostics Schema

Canonical diagnostics catalog is stored in:
- `tests/conformance/diagnostics/catalog.csv`

Each diagnostic record includes:
- `category`: subsystem classification (`Parser`, `TypeTheory`, `Artifacts`, ...)
- `severity`: `Error | Warning | Info`
- `summary`: concise semantic meaning
- `source` (optional): document identity (for example, a file URI) for multi-document reporting

## Contract Requirements

- Catalog rows must be unique and well-formed.
- Diagnostics emitted by language surfaces must use cataloged categories.
- Report ordering is stable and deterministic for repeated runs by the declared ordering key.
- Dedup behavior is deterministic and fixture-backed.
- Key negative syntax fixtures must include required message fragments that explain the failure cause.

## Compatibility Policy

- Diagnostic messages, categories, and spans are contract surfaces.
- Numeric/string diagnostic codes may change across releases.
