#!/usr/bin/env python3
"""Period table for the Z/2 wave equation (experimental annex).

Supports the quarantined probe `formal/experimental/WaveEquation.lean`;
nothing here is cited by the paper. Mirrors the Lean definitions
exactly: the state is a pair (prev, cur) of Bool fields, the step is

    next i = prev i xor X cur i

with ring coupling X c i = c(i-1) xor c(i+1) (indices mod n) and
Dirichlet coupling padded with false walls. The initial state is the
single pulse (silent previous layer, one live site at 0). The script
computes the least positive state period for 2 <= n <= 12 and checks
the observed laws

    ring:      n even -> n,  n odd -> 2n
    dirichlet: 2n + 2

Sizes proved in Lean by `decide` (ring 2-6, Dirichlet 3-5) are marked;
the rest is the numerical conjecture recorded in the module docstring.
Exit status 0 iff every computed period matches the pattern.
"""

RING_PROVED = {2, 3, 4, 5, 6}
DIRICHLET_PROVED = {3, 4, 5}
N_RANGE = range(2, 13)


def ring_coupling(c, n):
    return [c[(i - 1) % n] ^ c[(i + 1) % n] for i in range(n)]


def dirichlet_coupling(c, n):
    def wall(m):
        return c[m] if 0 <= m < n else False
    return [(False if i == 0 else wall(i - 1)) ^ wall(i + 1)
            for i in range(n)]


def period(n, coupling, limit=100000):
    prev = tuple(False for _ in range(n))
    cur = tuple(i == 0 for i in range(n))
    start = (prev, cur)
    state = start
    for t in range(1, limit):
        p, c = state
        nxt = tuple(a ^ b for a, b in zip(p, coupling(list(c), n)))
        state = (c, nxt)
        if state == start:
            return t
    raise RuntimeError(f"no period below {limit} for n={n}")


def main():
    ok = True
    print("== wave period table (single pulse) ==")
    print(f"{'n':>3} {'ring':>6} {'law':>6} {'':>8} "
          f"{'dirichlet':>9} {'law':>6}")
    for n in N_RANGE:
        r = period(n, ring_coupling)
        r_law = n if n % 2 == 0 else 2 * n
        d = period(n, dirichlet_coupling)
        d_law = 2 * n + 2
        r_mark = "lean" if n in RING_PROVED else "num"
        d_mark = "lean" if n in DIRICHLET_PROVED else "num"
        ok &= (r == r_law) and (d == d_law)
        print(f"{n:>3} {r:>6} {r_law:>6} {r_mark:>8} "
              f"{d:>9} {d_law:>6} {d_mark:>5}")
    print("pattern holds" if ok else "PATTERN VIOLATED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
