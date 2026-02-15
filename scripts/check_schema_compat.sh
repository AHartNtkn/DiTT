#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
fixtures_dir="$root/tests/conformance/artifacts"

latest="${SCHEMA_LATEST_VERSION:-1}"

status=0
for f in "$fixtures_dir"/build_record_v*.txt; do
  [[ -e "$f" ]] || continue
  version="$(awk -F= '/^schema_version=/{print $2}' "$f")"
  if [[ -z "$version" ]]; then
    echo "missing schema_version in $f"
    status=1
    continue
  fi
  if (( version > latest )); then
    echo "fixture $f uses future schema version $version > $latest"
    status=1
  fi
done

exit "$status"
