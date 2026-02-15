#!/usr/bin/env bash
set -euo pipefail

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

set +e
cargo test --no-fail-fast >"$tmp" 2>&1
status=$?
set -e

cat "$tmp"

if [[ "$status" -eq 0 ]]; then
  echo "red-phase provenance check failed: contract suite unexpectedly passed"
  exit 1
fi

if grep -q "could not compile" "$tmp"; then
  echo "red-phase provenance check failed: compile errors detected"
  exit 1
fi

if ! grep -q 'not implemented:' "$tmp"; then
  echo "red-phase provenance check failed: expected unimplemented contract failures were not observed"
  exit 1
fi

if ! awk '
function flush_block() {
  if (in_block && !has_unimplemented) {
    print block_name;
    bad = 1;
  }
  in_block = 0;
  has_unimplemented = 0;
  block_name = "";
}

/^---- .* stdout ----$/ {
  flush_block();
  in_block = 1;
  block_name = $0;
  next;
}

in_block && /not implemented:/ {
  has_unimplemented = 1;
}

/^failures:$/ || /^test result:/ {
  flush_block();
}

END {
  flush_block();
  exit bad;
}
' "$tmp"; then
  echo "red-phase provenance check failed: at least one failing test did not show unimplemented provenance"
  exit 1
fi

echo "red-phase provenance check passed: every failing test is attributable to unimplemented interfaces"
