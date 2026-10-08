#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

lake build

for source_file in TNumbersLean/*.lean; do
  lake env lean -DwarningAsError=true "$source_file"
done

audit_log="$(mktemp -t tnumbers-audit.XXXXXX)"
trap 'rm -f "$audit_log"' EXIT

lake env lean -DwarningAsError=true scripts/Audit.lean | tee "$audit_log"

if grep -q 'sorryAx' "$audit_log"; then
  echo 'ERROR: a listed theorem depends on an unproved placeholder.' >&2
  exit 1
fi

echo 'Build and listed-theorem placeholder checks passed.'
echo 'Inspect the printed axioms and the mathematical statements as well.'
