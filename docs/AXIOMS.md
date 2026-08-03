# Axiom footprints (DAG)

Target: spine and bridge results empty `#print axioms` where claimed.
Ledger inherits AG's existing allowlist exceptions on Obs satellites.

Regenerate after builds:

```bash
# spine audit (vendored tools)
python formal/tools/gen_audit.py   # if pointed at spine Audit.lean
(cd formal/spine && lake build)
(cd formal/bridge && lake build)
(cd formal/dictionary && lake build)
```

Policy: `sorry` forbidden; no Mathlib; dictionary exhibits are not Lean.
