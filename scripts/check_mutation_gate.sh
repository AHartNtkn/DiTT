#!/usr/bin/env bash
set -euo pipefail

THRESHOLD="${MUTATION_SCORE_THRESHOLD:-80}"
REPORT_DIR="${QUALITY_REPORT_DIR:-}"
REPORT_PATH="${MUTATION_REPORT_PATH:-}"
if [[ -z "$REPORT_PATH" && -n "$REPORT_DIR" ]]; then
  REPORT_PATH="$REPORT_DIR/mutation_report.json"
fi

if ! command -v cargo-mutants >/dev/null 2>&1; then
  echo "cargo-mutants is required for mutation gate"
  exit 2
fi

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

cargo mutants --list >/dev/null
cargo mutants --json >"$tmp"

score="$(awk -F: '/"mutation_score"/ {gsub(/[ ,]/,"",$2); print int($2); exit}' "$tmp")"
if [[ -z "${score:-}" ]]; then
  echo "could not extract mutation_score from cargo-mutants json output"
  exit 3
fi

if [[ -n "$REPORT_PATH" ]]; then
  mkdir -p "$(dirname "$REPORT_PATH")"
  cat >"$REPORT_PATH" <<EOF
{
  "mutation_score": $score,
  "threshold": $THRESHOLD
}
EOF
fi

echo "mutation score: $score (threshold: $THRESHOLD)"
if (( score < THRESHOLD )); then
  echo "mutation gate failed"
  exit 1
fi
