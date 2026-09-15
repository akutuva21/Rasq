#!/usr/bin/env python3
"""Independent numerical smoke tests for the abstract RasQ theory formulas.

These checks are deliberately implementation-independent and cheap.  They catch
formula/transcription mistakes before Lean compilation, but they are not a
substitute for the Lean kernel.
"""
from __future__ import annotations

import math
import random
from collections import defaultdict

rng = random.Random(20260915)
checks = 0

# Fast-switching fixed point and exact averaging deviation.
for _ in range(5000):
    a = rng.uniform(-0.8, 0.999)
    m0 = rng.uniform(-20, 20)
    m1 = rng.uniform(-20, 20)
    x = (a * m0 + m1) / (1 + a)
    step = lambda mu, z: a * z + (1 - a) * mu
    cyc = step(m1, step(m0, x))
    assert math.isclose(cyc, x, rel_tol=1e-11, abs_tol=1e-11)
    lhs = x - (m0 + m1) / 2
    rhs = (1 - a) * (m1 - m0) / (2 * (1 + a))
    assert math.isclose(lhs, rhs, rel_tol=1e-11, abs_tol=1e-11)
    checks += 2

# Equal-mean dwell laws can have different residual processivity, and latency
# cannot improve the completed fraction for r >= 0.
for _ in range(5000):
    r = rng.uniform(0, 10)
    d = rng.uniform(0, 10)
    latency = rng.uniform(0, 2 * d + 1)
    det = math.exp(-r * d)
    mix = (1 + math.exp(-r * (2 * d))) / 2
    rhs = (det - 1) ** 2 / 2
    assert math.isclose(mix - det, rhs, rel_tol=1e-10, abs_tol=1e-12)
    assert mix + 1e-12 >= det
    active = max(d - latency, 0.0)
    assert math.exp(-r * active) + 1e-12 >= det
    checks += 3

# Mesoscopic inverse-area law and finite-window implications.
for _ in range(5000):
    A = rng.uniform(0.1, 100)
    scale = rng.uniform(0.1, 20)
    spacing = rng.uniform(0.05, 5)
    v = rng.uniform(0.1, 5)
    kappa = rng.uniform(0.01, 3)
    R = lambda area: spacing**2 / (area * v)
    assert math.isclose(R(scale * A), R(A) / scale, rel_tol=1e-12, abs_tol=1e-12)
    upper = spacing**2 / (kappa * v)
    if A <= upper:
        assert R(A) + 1e-12 >= kappa
    checks += 2

# Accessibility partition, Damkohler form, and fast-mixing target-loss bound.
for _ in range(5000):
    act = rng.uniform(0, 20)
    k = rng.uniform(0, 20)
    mix = max(rng.uniform(0.01, 20), k * act)
    target = rng.uniform(0, 5000)
    fa = mix / (act + mix)
    fd = act / (act + mix)
    assert math.isclose(fa + fd, 1.0, rel_tol=1e-12, abs_tol=1e-12)
    assert math.isclose(fa, 1 / (1 + act / mix), rel_tol=1e-12, abs_tol=1e-12)
    assert fd <= 1 / (k + 1) + 1e-12
    loss = target - target * fa
    assert loss <= target / (k + 1) + 1e-9
    checks += 4

# Deterministic data processing for finite TV and decoder-error replacement.
for _ in range(2500):
    n = rng.randint(2, 12)
    c = rng.randint(1, min(5, n))
    p = [rng.uniform(-2, 2) for _ in range(n)]
    q = [rng.uniform(-2, 2) for _ in range(n)]
    f = [rng.randrange(c) for _ in range(n)]

    def tv(a, b):
        return 0.5 * sum(abs(x - y) for x, y in zip(a, b))

    pp = [0.0] * c
    qq = [0.0] * c
    for i in range(n):
        pp[f[i]] += p[i]
        qq[f[i]] += q[i]
    assert tv(pp, qq) <= tv(p, q) + 1e-12

    # A finite event/decoder selector cannot change its mass by more than L1.
    chosen = [rng.choice([False, True]) for _ in range(n)]
    ep = sum(x for x, keep in zip(p, chosen) if keep)
    eq = sum(x for x, keep in zip(q, chosen) if keep)
    assert ep <= eq + sum(abs(x - y) for x, y in zip(p, q)) + 1e-12
    checks += 2

# Catalytic lumping: regrouping slow microstates by catalytic class leaves a
# class-dependent downstream mixture unchanged; same class masses imply same mix.
for _ in range(2500):
    ns = rng.randint(2, 10)
    nc = rng.randint(1, min(5, ns))
    ny = rng.randint(1, 6)
    cls = [rng.randrange(nc) for _ in range(ns)]
    w = [rng.uniform(-2, 2) for _ in range(ns)]
    code = [[rng.uniform(-3, 3) for _ in range(ny)] for _ in range(nc)]

    cm = defaultdict(float)
    for s in range(ns):
        cm[cls[s]] += w[s]
    for y in range(ny):
        micro = sum(w[s] * code[cls[s]][y] for s in range(ns))
        grouped = sum(cm[c] * code[c][y] for c in range(nc))
        assert math.isclose(micro, grouped, rel_tol=1e-11, abs_tol=1e-11)
        checks += 1

print(f"THEORY IDENTITIES: PASS ({checks:,} independent checks)")
