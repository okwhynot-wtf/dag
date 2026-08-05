# Diagonal Archive Geometry (DAG)

Hybrid Lean corpus: **Diagonal Monism** (spine) + **Archive Geometry** (ledger)
+ dictionary exhibits.

```
Layer 2  DICTIONARY   formal/dictionary + exhibits/*
Layer 1  LEDGER       formal/ledger
Layer 0  SPINE        formal/spine
```

Downward imports only. Bridge theorems live in `formal/bridge/`.
Quarantined probes live in `formal/experimental/`; nothing cited by the
paper imports them.

- Paper draft: [`docs/paper/jmp_draft.pdf`](docs/paper/jmp_draft.pdf)
  ([`.tex`](docs/paper/jmp_draft.tex))
- Plain-English reading: [`docs/plain_english.pdf`](docs/plain_english.pdf)
  ([`.tex`](docs/plain_english.tex))
- Symbolic law: [`docs/DAG_SYMBOLIC.txt`](docs/DAG_SYMBOLIC.txt)
- Axiom audit: [`formal/AXIOMS.md`](formal/AXIOMS.md)

## Verify

Requires [elan](https://github.com/leanprover/elan) (the pinned Lean
toolchain installs on first build) and Python 3. No Mathlib; no `sorry`.

```bash
bash VERIFY.sh      # or .\VERIFY.ps1 on Windows
```

Builds all five packages and runs the quintom and wave exhibits.

## Axiom audit

Every theorem's axiom footprint is recorded in
[`formal/AXIOMS.md`](formal/AXIOMS.md). To regenerate after adding or
renaming theorems:

```bash
python3 formal/tools/gen_audit.py   # regenerate per-package Audit.lean
bash formal/tools/audit.sh          # rebuild and rewrite formal/AXIOMS.md
```

## License

[Apache-2.0](LICENSE).
