#!/usr/bin/env python3
"""Independent numeric regression checks for the formulas mirrored in Lean.

These are not substitutes for Lean proofs. They catch transcription mistakes between
README equations, Python application code, and Lean definitions.
"""

from __future__ import annotations

import math
import random


def generic_mean(T, n, a, b):
    return T * n * a / (n * a + b)


def generic_spacing_formula(T, n, a, b):
    return T * a * b / ((n * a + b) * ((n + 1) * a + b))


def generic_error_formula(T, n, a, b):
    return T * (n * a) ** 2 / (b * (n * a + b))


def ras_mean(R, n, a, b):
    return (R - n) * n * a / (n * a + b)


def ras_spacing_formula(R, n, a, b):
    return a * (b * (R - 2 * n - 1) - a * n * (n + 1)) / (
        (n * a + b) * ((n + 1) * a + b)
    )


def ras_error_formula(R, n, a, b):
    return a * n**2 * (R * a + b) / (b * (n * a + b))



def tracking_error_after_relaxations(c):
    return math.exp(-c)


def survival_at_relaxations(relax_rate, koff, c):
    gamma = relax_rate / koff
    return math.exp(-c / gamma)


def mean_residual_at_dwell_end(relax_rate, koff):
    gamma = relax_rate / koff
    return 1.0 / (1.0 + gamma)


def mean_completed_at_dwell_end(relax_rate, koff):
    gamma = relax_rate / koff
    return gamma / (1.0 + gamma)


def close(x, y, tol=1e-10):
    return abs(x - y) <= tol * max(1.0, abs(x), abs(y))


def main():
    rng = random.Random(20260910)
    for _ in range(5000):
        T = rng.uniform(10, 5000)
        R = rng.uniform(20, 5000)
        a = 10 ** rng.uniform(-5, 0)
        b = 10 ** rng.uniform(-5, 0)
        n = rng.randint(0, 15)

        lhs = generic_mean(T, n + 1, a, b) - generic_mean(T, n, a, b)
        assert close(lhs, generic_spacing_formula(T, n, a, b))

        linear = n * T * a / b
        assert close(linear - generic_mean(T, n, a, b), generic_error_formula(T, n, a, b))

        lhs_ras = ras_mean(R, n + 1, a, b) - ras_mean(R, n, a, b)
        assert close(lhs_ras, ras_spacing_formula(R, n, a, b))

        linear_ras = n * R * a / b
        assert close(linear_ras - ras_mean(R, n, a, b), ras_error_formula(R, n, a, b))

    # Slow/fast identity: exp(-koff * c/r) = exp(-c/Gamma).
    for _ in range(5000):
        r = 10 ** rng.uniform(-5, 2)
        koff = 10 ** rng.uniform(-5, 2)
        c = rng.uniform(0.0, 10.0)
        lhs = math.exp(-koff * (c / r))
        rhs = survival_at_relaxations(r, koff, c)
        assert close(lhs, rhs)
        assert close(math.exp(-r * (c / r)), tracking_error_after_relaxations(c))
        # Integral identity E[e^(-r D)] for D ~ Exp(koff).
        expected_residual_direct = koff / (koff + r)
        assert close(expected_residual_direct, mean_residual_at_dwell_end(r, koff))
        assert close(1.0 - expected_residual_direct, mean_completed_at_dwell_end(r, koff))

    # Model 1 -> Model 3 scaling invariants from the repository.
    kon1, koff1 = 7e-8, 5e-3
    kon3, koff3 = 7e-5, 5.0
    assert close(kon1 / koff1, kon3 / koff3)
    assert close((1 / koff3), (1 / koff1) / 1000)

    # n=1, GTP-bound SOS: probability of surviving three Ras relaxation times.
    g1 = (1e-2 + 2.5e-3) / 5e-4
    g2 = (1e-2 + 2.5e-2) / 5e-4
    g3 = (1e-2 + 2.5e-3) / 0.5
    assert close(g1, 25.0)
    assert close(g2, 70.0)
    assert close(g3, 0.025)
    assert close(math.exp(-3 / g1), 0.8869204367171575)
    assert close(math.exp(-3 / g2), 0.9580482443263975)
    assert close(math.exp(-3 / g3), 7.667648073722e-53, tol=1e-9)
    assert close(mean_completed_at_dwell_end(1e-2 + 2.5e-3, 5e-4), 25 / 26)
    assert close(mean_completed_at_dwell_end(1e-2 + 2.5e-2, 5e-4), 70 / 71)
    assert close(mean_completed_at_dwell_end(1e-2 + 2.5e-3, 0.5), 1 / 41)

    print("10000 randomized algebra/slow-fast checks + Ras scaling invariants: PASS")


if __name__ == "__main__":
    main()
