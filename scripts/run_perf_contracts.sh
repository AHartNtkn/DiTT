#!/usr/bin/env bash
set -euo pipefail

REPORT_DIR="${QUALITY_REPORT_DIR:-}"
REPORT_PATH="${PERF_REPORT_PATH:-}"
if [[ -z "$REPORT_PATH" && -n "$REPORT_DIR" ]]; then
  REPORT_PATH="$REPORT_DIR/perf_report.txt"
fi

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

set +e
cargo test --test contracts_performance -- --ignored --nocapture >"$tmp" 2>&1
status=$?
set -e

cat "$tmp"
if [[ "$status" -ne 0 ]]; then
  exit "$status"
fi

if [[ -n "$REPORT_PATH" ]]; then
  mkdir -p "$(dirname "$REPORT_PATH")"
  : >"$REPORT_PATH"
  awk '
  /PERF_METRIC/ {
    metric=""; value=""; budget="";
    for (i = 1; i <= NF; i++) {
      if ($i ~ /^metric=/) { split($i,a,"="); metric=a[2]; }
      if ($i ~ /^value=/)  { split($i,a,"="); value=a[2]; }
      if ($i ~ /^budget=/) { split($i,a,"="); budget=a[2]; }
    }
    if (metric != "" && value != "" && budget != "") {
      printf "metric=%s\nvalue=%s\nbudget=%s\n\n", metric, value, budget;
    }
  }' "$tmp" >"$REPORT_PATH"
fi
