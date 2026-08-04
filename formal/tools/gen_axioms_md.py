#!/usr/bin/env python3
"""Generate `formal/AXIOMS.md` from `lake build` output.

Reads `#print axioms` verdicts from each package `Audit.lean`. Reports kernel
vs declared axioms per module.

Usage (from the repository root):

    python formal/tools/gen_audit.py
    bash formal/tools/audit.sh
"""
from __future__ import annotations

import re
import sys
import pathlib
import collections

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from gen_audit import PACKAGES, FORMAL, ROOT, qualified_theorems  # noqa: E402

KERNEL = ("propext", "Quot.sound", "Classical.choice")

# Lean identifiers may end in `'`, so the name is matched lazily up to the
# quote that precedes the verdict text rather than as a quote-free run.
PAT = re.compile(r"info: ([^:]+\.lean):\d+:\d+: '(.+?)' "
                 r"(does not depend on any axioms|depends on axioms: \[(.*)\])")


def read_verdicts(log: pathlib.Path) -> dict[str, list[str]]:
    """theorem name -> axiom list. `#print axioms` wraps long lists over
    several lines; rejoin before parsing."""
    raw = log.read_text(encoding="utf-8", errors="replace")
    merged, buf = [], None
    for ln in raw.splitlines():
        if buf is not None:
            buf += " " + ln.strip()
            if ln.rstrip().endswith("]"):
                merged.append(buf)
                buf = None
            continue
        if "depends on axioms: [" in ln and not ln.rstrip().endswith("]"):
            buf = ln
            continue
        merged.append(ln)
    if buf:
        merged.append(buf)

    out: dict[str, list[str]] = {}
    for ln in merged:
        m = PAT.search(ln)
        if not m:
            continue
        _, name, kind, lst = m.groups()
        ax = [] if kind.startswith("does not") else \
             [a.strip() for a in lst.split(",") if a.strip()]
        # `#print axioms` inside a namespace prints unqualified names; the
        # Audit files sit outside every namespace so their verdicts are
        # canonical. Prefer a longer (qualified) key when both appear.
        if name not in out or len(ax) > len(out[name]):
            out[name] = ax
    return out


def classify(ax: list[str]) -> str:
    kern = [a for a in ax if a in KERNEL]
    decl = [a for a in ax if a not in KERNEL]
    if decl:
        return "declared"
    if not kern:
        return "clean"
    return " + ".join(sorted(kern, key=KERNEL.index))


def main() -> int:
    log = pathlib.Path(sys.argv[1])
    dest = pathlib.Path(sys.argv[2])
    verdicts = read_verdicts(log)

    w = []
    add = w.append
    add("# Axiom footprints")
    add("")
    add("Generated from `lake build` via each package `Audit.lean`.")
    add("")
    add("```bash")
    add("python formal/tools/gen_audit.py")
    add("bash formal/tools/audit.sh")
    add("```")
    add("")
    add("Legend:")
    add("")
    add("- **clean** — no axioms.")
    add("- **propext**, **propext + Quot.sound** — Lean kernel axioms (`funext` / quotients).")
    add("- **declared** — declared postulates (the spine declares none).")
    add("")
    add("The spine target is a zero-axiom footprint for every result.")
    add("")

    total = clean_n = 0
    missing_names: list[str] = []
    reached: set[str] = set()
    for pkg, modules in PACKAGES.items():
        add(f"## `formal/{pkg}/`")
        add("")
        add("| Module | results | clean | propext | propext + Quot.sound | declared |")
        add("|---|---:|---:|---:|---:|---:|")
        for mod in modules:
            src = FORMAL / pkg / (mod.replace(".", "/") + ".lean")
            thms = qualified_theorems(src)
            buckets = collections.Counter()
            for t in thms:
                if t not in verdicts:
                    missing_names.append(f"{pkg}/{mod}: {t}")
                    continue
                ax = verdicts[t]
                buckets[classify(ax)] += 1
                total += 1
                if not ax:
                    clean_n += 1
                for a in ax:
                    if a not in KERNEL:
                        reached.add(a.split(".")[-1])
            add(f"| `{mod}` | {len(thms)} | {buckets['clean'] or ''} "
                f"| {buckets['propext'] or ''} "
                f"| {buckets['propext + Quot.sound'] or ''} "
                f"| {buckets['declared'] or ''} |")
        add("")

    add(f"Totals: {total} audited results; {clean_n} clean.")
    if missing_names:
        add("")
        add(f"({len(missing_names)} theorems missing from the build log; "
            "rerun `gen_audit.py`.)")
    add("")

    dest.write_text("\n".join(w) + "\n", encoding="utf-8")
    print(f"wrote {dest}: {total} results, {clean_n} clean, "
          f"{len(missing_names)} missing")
    for name in missing_names:
        print(f"  missing: {name}", file=sys.stderr)
    return 1 if missing_names else 0


if __name__ == "__main__":
    sys.exit(main())
