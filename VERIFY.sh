#!/usr/bin/env bash
# VERIFY.sh — Diagonal Archive Geometry hybrid check
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

echo "== DAG VERIFY =="

echo "-- spine --"
(cd formal/spine && lake build)

echo "-- ledger --"
(cd formal/ledger && lake build)

echo "-- bridge --"
(cd formal/bridge && lake build)

echo "-- dictionary --"
(cd formal/dictionary && lake build)

echo "-- experimental (quarantined) --"
(cd formal/experimental && lake build)

echo "-- quintom exhibit --"
python3 exhibits/quintom/integrate.py

echo "-- wave period exhibit (experimental) --"
python3 exhibits/wave/periods.py

echo "== DAG VERIFY OK =="
