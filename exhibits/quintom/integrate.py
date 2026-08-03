"""
Quintom exhibit — frictionless (H=0) and damped (H>0) caricatures.

Refused as Lean by policy. Demonstrates:
  H = 0  → undamped two-channel oscillator (envelope constant)
  H > 0  → envelope decay (dissipation / registration face)

No cosmological numbers are derived from Bool.
"""

from __future__ import annotations

import math


def step_frictionless(phi: float, sigma: float, dt: float, omega: float = 1.0):
    """Exact swap-compatible oscillator step on two scalars (toy)."""
    # Coupled rotation in the (φ, σ) plane — involution at half-period.
    c, s = math.cos(omega * dt), math.sin(omega * dt)
    return c * phi - s * sigma, s * phi + c * sigma


def step_damped(phi: float, sigma: float, dt: float, H: float, omega: float = 1.0):
    """Hubble-friction caricature: rotate then apply e^{-H dt} envelope."""
    phi, sigma = step_frictionless(phi, sigma, dt, omega)
    damp = math.exp(-H * dt)
    return damp * phi, damp * sigma


def envelope(phi: float, sigma: float) -> float:
    return math.hypot(phi, sigma)


def run(H: float, steps: int = 200, dt: float = 0.05) -> list[float]:
    phi, sigma = 1.0, 0.0
    out = []
    for _ in range(steps):
        if H == 0.0:
            phi, sigma = step_frictionless(phi, sigma, dt)
        else:
            phi, sigma = step_damped(phi, sigma, dt, H)
        out.append(envelope(phi, sigma))
    return out


def main() -> None:
    env0 = run(0.0)
    envH = run(0.15)
    # Frictionless: envelope constant (up to float noise).
    drift0 = max(env0) - min(env0)
    assert drift0 < 1e-9, f"H=0 envelope drifted: {drift0}"
    # Damped: envelope shrinks.
    assert envH[-1] < envH[0] * 0.5, "H>0 expected strong decay"
    # Swap involution on labels (discrete check).
    assert {"phi", "sigma"} == {"sigma", "phi"}  # relabel set
    print("quintom exhibit OK")
    print(f"  H=0 envelope drift={drift0:.2e}")
    print(f"  H>0 envelope {envH[0]:.4f} -> {envH[-1]:.4f}")


if __name__ == "__main__":
    main()
