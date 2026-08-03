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

echo "-- quintom exhibit --"
python exhibits/quintom/integrate.py

echo "== DAG VERIFY OK =="
