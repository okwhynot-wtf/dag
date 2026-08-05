#!/usr/bin/env bash
# Rebuild every package and regenerate formal/AXIOMS.md from the output.
#
#   bash formal/tools/audit.sh
#
# Run gen_audit.py first if any theorem has been added or renamed:
#
#   python3 formal/tools/gen_audit.py
set -euo pipefail

cd "$(dirname "$0")/../.."
log="$(mktemp)"
trap 'rm -f "$log"' EXIT

for d in spine ledger bridge dictionary experimental; do
  echo "##PKG $d" >> "$log"
  (cd "formal/$d" && lake build) >> "$log" 2>&1
done

python3 formal/tools/gen_axioms_md.py "$log" formal/AXIOMS.md
