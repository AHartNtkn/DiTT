#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="$ROOT/docs/CORPUS_LOCK.csv"

hash_file() {
  local file="$1"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$file" | awk '{print $1}'
    return
  fi
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$file" | awk '{print $1}'
    return
  fi
  echo "missing sha256 hashing tool (sha256sum or shasum)" >&2
  exit 1
}

emit_row() {
  local rel="$1"
  local abs="$ROOT/$rel"
  local digest
  local size
  digest="$(hash_file "$abs")"
  size="$(wc -c <"$abs" | tr -d '[:space:]')"
  printf "%s,%s,%s\n" "$rel" "$digest" "$size"
}

{
  echo "path,sha256,size"

  find "$ROOT/tests/conformance" -type f \
    | sed "s#^$ROOT/##" \
    | sort \
    | while read -r rel; do
        emit_row "$rel"
      done

  find "$ROOT/docs" -maxdepth 1 -type f \( -name "*.csv" -o -name "*.md" \) \
    | sed "s#^$ROOT/##" \
    | grep -v "^docs/CORPUS_LOCK.csv$" \
    | sort \
    | while read -r rel; do
        emit_row "$rel"
      done
} >"$OUT"

echo "wrote $OUT"
