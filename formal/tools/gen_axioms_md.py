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
    add("- **clean**: no axioms.")
    add("- **propext**: propositional extensionality alone.")
    add("- **Quot.sound**: quotient soundness alone; in this corpus it enters")
    add("  through `funext`, so a bare `Quot.sound` entry reads as function")
    add("  extensionality.")
    add("- **propext + Quot.sound**: both kernel axioms together, typically")
    add("  propositional reasoning combined with `funext` or kernel-decided")
    add("  `Decidable` instances.")
    add("- **declared**: declared postulates (the spine declares none).")
    add("")
    add("The spine target is a zero-axiom footprint for every result.")
    add("")
    add("Named funext flagging. Function extensionality is invoked directly by")
    add("`Bridge.WaveDynamics.reverse_step` and")
    add("`Bridge.Recurrence.wave_recurrence_bounded`;")
    add("`Bridge.WaveDynamics.step_lossless`, `Bridge.Recurrence.wave_recurrence`,")
    add("and `Bridge.Recurrence.wave_recurrence_pow` inherit that footprint.")
    add("Outside the promoted dynamics arc, `Bridge.Dil` applies `funext` in two")
    add("internal steps, the experimental `Experimental.Wave.waveFactor`")
    add("witness lifts its involution laws with `funext`, and the experimental")
    add("`Experimental.CouplingGauge.flip_conjugacy_of_four_dvd` packages its")
    add("pointwise conjugacy with `funext`, a footprint inherited by")
    add("`coupling_flip_dichotomy` and `flip_conjugate_four`. Every other")
    add("`Quot.sound` entry in the tables arrives through library lemmas, `omega`,")
    add("or `Decidable` instances; none of those entries makes a direct")
    add("`funext` step.")
    add("")
    add("Architectural (non-Lean) audited residue, inventoried in the paper's")
    add("status section (Open, refused, and philosophical): existence of a")
    add("non-degenerate pointed act. Lean records a Bool *model*")
    add("(`Facticity.exists_nondegenerate_pointed_act_model`) and refuses")
    add("discharge as world-from-Bool; it does not declare a kernel axiom.")
    add("")

    total = clean_n = 0
    missing_names: list[str] = []
    reached: set[str] = set()
    for pkg, modules in PACKAGES.items():
        add(f"## `formal/{pkg}/`")
        add("")
        if pkg == "experimental":
            add("Experimental (quarantined): exploratory results, not part of "
                "the audited spine/ledger/bridge/dictionary chain.")
            add("")
        add("| Module | results | clean | propext | Quot.sound | propext + Quot.sound | declared |")
        add("|---|---:|---:|---:|---:|---:|---:|")
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
                f"| {buckets['Quot.sound'] or ''} "
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
