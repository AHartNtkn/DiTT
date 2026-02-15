# Paper Parity

This document tracks parity between `References/2409.10237v2.pdf` and executable contracts in this repository.

Primary machine-readable source:
- `tests/conformance/semantics/paper_parity.csv`
- `tests/conformance/semantics/paper_examples.csv` (numbered examples with surface manifestation)
- `tests/conformance/semantics/variance_examples.csv` (numbered examples expressed via variance-inference API)

## Coverage Rules

- Every major rule family or judgment pattern in the paper must have a `contract_id`.
- Every numbered example in the paper must appear in either `paper_examples.csv` or
  `variance_examples.csv`.
- `status` must be one of:
  - `covered`: directly enforced by one or more tests.
  - `partial`: partially enforced; gap documented in notes.
  - `missing`: no contract yet.
- Feature-complete corpus requires:
  - zero `missing` rows
  - zero `partial` rows without a linked follow-up issue

## Intended Usage

- During spec evolution: update parity CSV first.
- During implementation: keep contract IDs stable to preserve traceability.
- During review: reject semantic PRs that introduce untracked paper deltas.
