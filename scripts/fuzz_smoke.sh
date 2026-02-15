#!/usr/bin/env bash
set -euo pipefail

REPORT_DIR="${QUALITY_REPORT_DIR:-}"
REPORT_PATH="${FUZZ_REPORT_PATH:-}"
if [[ -z "$REPORT_PATH" && -n "$REPORT_DIR" ]]; then
  REPORT_PATH="$REPORT_DIR/fuzz_report.txt"
fi

write_report_line() {
  if [[ -n "$REPORT_PATH" ]]; then
    mkdir -p "$(dirname "$REPORT_PATH")"
    printf "%s\n" "$1" >>"$REPORT_PATH"
  fi
}

if [[ -n "$REPORT_PATH" ]]; then
  : >"$REPORT_PATH"
fi

if ! command -v cargo-fuzz >/dev/null 2>&1; then
  if [[ "${FUZZ_REQUIRED:-0}" == "1" ]]; then
    echo "cargo-fuzz is required for fuzz smoke"
    exit 2
  fi
  echo "cargo-fuzz not installed; skipping fuzz smoke"
  write_report_line "target=all"
  write_report_line "status=skipped"
  write_report_line "executions=0"
  write_report_line "crashes=0"
  write_report_line "timeouts=0"
  write_report_line ""
  exit 0
fi

if [[ ! -d fuzz ]]; then
  if [[ "${FUZZ_REQUIRED:-0}" == "1" ]]; then
    echo "fuzz/ directory not found; initialize with: cargo fuzz init"
    exit 3
  fi
  echo "fuzz/ directory not found; skipping fuzz smoke"
  write_report_line "target=all"
  write_report_line "status=skipped"
  write_report_line "executions=0"
  write_report_line "crashes=0"
  write_report_line "timeouts=0"
  write_report_line ""
  exit 0
fi

targets=("${@:-parser cli_protocol lsp_protocol}")

for target in "${targets[@]}"; do
  echo "running fuzz smoke for target: $target"
  if cargo fuzz run "$target" -- -max_total_time=10 -runs=0; then
    write_report_line "target=$target"
    write_report_line "status=ok"
    write_report_line "executions=1"
    write_report_line "crashes=0"
    write_report_line "timeouts=0"
    write_report_line ""
  else
    write_report_line "target=$target"
    write_report_line "status=error"
    write_report_line "executions=0"
    write_report_line "crashes=1"
    write_report_line "timeouts=0"
    write_report_line ""
    exit 1
  fi
done
