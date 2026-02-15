#!/usr/bin/env bash
set -euo pipefail

REPORT_DIR="${QUALITY_REPORT_DIR:-target/quality-reports}"
mkdir -p "$REPORT_DIR"

RUN_MUTATION="${RUN_MUTATION:-1}"
RUN_FUZZ="${RUN_FUZZ:-1}"
RUN_PERF="${RUN_PERF:-1}"

if [[ "$RUN_MUTATION" == "1" ]]; then
  QUALITY_REPORT_DIR="$REPORT_DIR" MUTATION_REPORT_PATH="$REPORT_DIR/mutation_report.json" \
    bash scripts/check_mutation_gate.sh
fi

if [[ "$RUN_FUZZ" == "1" ]]; then
  QUALITY_REPORT_DIR="$REPORT_DIR" FUZZ_REPORT_PATH="$REPORT_DIR/fuzz_report.txt" \
    bash scripts/fuzz_smoke.sh
fi

if [[ "$RUN_PERF" == "1" ]]; then
  QUALITY_REPORT_DIR="$REPORT_DIR" PERF_REPORT_PATH="$REPORT_DIR/perf_report.txt" \
    bash scripts/run_perf_contracts.sh
fi

DITT_QUALITY_REPORT_DIR="$REPORT_DIR" DITT_REQUIRE_LIVE_REPORTS=1 \
  cargo test --test contracts_quality_gate_registry quality_gate_live_reports_if_present_satisfy_thresholds -- --nocapture
