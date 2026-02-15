# Green Phase Readiness

These criteria define when the repository can move from red phase to green phase.

## Required Conditions

1. No interface method remains stubbed with `LanguageError::Unimplemented(...)`.
2. CI no longer uses `scripts/check_red_phase.sh` as the required gate.
3. The full contract suite passes with no ignored required contracts.
4. Quality gates are run with real tool outputs and validated by executable contracts.

## Operational Checklist

1. Replace stubbed interface implementations with concrete behavior.
2. Remove red-phase-only CI requirements and switch to pass-all contract enforcement.
3. Ensure `cargo test --no-fail-fast` succeeds in CI.
4. Produce live mutation/fuzz/perf reports and validate them through contract tests.
