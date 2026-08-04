#!/usr/bin/env python3
"""Generate a `#print axioms` Audit.lean for each Lean package.

Each package Audit imports every module and prints the axiom footprint of
every theorem. Regenerate `formal/AXIOMS.md` from the build output afterwards.

Usage (from the repository root):

    python3 formal/tools/gen_audit.py
    (cd formal/spine && lake build)
"""
from __future__ import annotations

import re
import sys
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
FORMAL = ROOT / "formal"

PACKAGES = {
    "spine": ["Orbit", "TwoCycle", "Diagonal", "Tower", "Ladder",
              "Cause", "Branch", "Limit", "Revision", "SEM",
              "Interior", "Monism", "Apophasis", "Canon",
              "Information", "Observer", "Faces", "Density",
              "NonCommencement", "OmegaDuration", "SelfReference"],
}

# Lean identifiers admit `'`, `!`, `?` and unicode letters/subscripts after the
# first character. `\w` under Python's unicode rules already covers Greek and
# subscript digits; `?` and `!` have to be added explicitly, or `get?_mem`
# silently truncates to `get` and the generated audit fails to compile.
IDENT = r"[^\W\d][\w'’!?]*"
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+)?theorem\s+"
                  rf"({IDENT}(?:\.{IDENT})*)")
NS_OPEN = re.compile(rf"^\s*namespace\s+({IDENT}(?:\.{IDENT})*)")
NS_END = re.compile(rf"^\s*end\s+({IDENT}(?:\.{IDENT})*)\s*$")


def qualified_theorems(path: pathlib.Path) -> list[str]:
    """Fully-qualified theorem names in source order.

    Tracks the `namespace` / `end` stack. `end <name>` pops only when it
    matches the open namespace, so `end` closing a `section` is ignored.
    Comment blocks are stripped first: `/-! ... -/` docstrings routinely
    contain the word `theorem` at the start of a line.
    """
    src = path.read_text(encoding="utf-8")
    src = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"),
                 src, flags=re.S)
    stack: list[str] = []
    out: list[str] = []
    for line in src.splitlines():
        m = NS_OPEN.match(line)
        if m:
            stack.append(m.group(1))
            continue
        m = NS_END.match(line)
        if m:
            if stack and stack[-1] == m.group(1):
                stack.pop()
            continue
        m = DECL.match(line)
        if m:
            name = m.group(1)
            full = ".".join(stack + [name]) if stack else name
            if full not in out:          # a duplicate print is noise, not data
                out.append(full)
    return out


def generate(pkg: str, modules: list[str]) -> tuple[pathlib.Path, int]:
    pkg_dir = FORMAL / pkg
    entries: list[tuple[str, list[str]]] = []
    for mod in modules:
        path = pkg_dir / (mod.replace(".", "/") + ".lean")
        if not path.exists():
            raise SystemExit(f"missing module source: {path}")
        entries.append((mod, qualified_theorems(path)))

    total = sum(len(t) for _, t in entries)
    lines = [f"import {m}" for m in modules]
    lines += [
        "",
        "/-!",
        f"# Audit — axiom footprint for `formal/{pkg}/`",
        "",
        "Generated. Do not edit by hand:",
        "",
        "```bash",
        "python3 formal/tools/gen_audit.py",
        "```",
        "",
        f"{len(modules)} modules, {total} results. Source for `formal/AXIOMS.md`.",
        "-/",
        "",
    ]
    for mod, thms in entries:
        lines.append(f"-- {mod} ({len(thms)})")
        lines += [f"#print axioms {t}" for t in thms]
        lines.append("")

    dest = pkg_dir / "Audit.lean"
    dest.write_text("\n".join(lines), encoding="utf-8")
    return dest, total


def main() -> int:
    grand = 0
    for pkg, modules in PACKAGES.items():
        dest, n = generate(pkg, modules)
        grand += n
        print(f"{dest.relative_to(ROOT)}: {n} results across {len(modules)} modules")
    print(f"total: {grand}")
    print("now add \"Audit\" to each lakefile's roots (once) and rebuild")
    return 0


if __name__ == "__main__":
    sys.exit(main())
