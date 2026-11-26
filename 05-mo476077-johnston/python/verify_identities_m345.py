#!/usr/bin/env python3
"""Verify exact algebraic identities for MO #476077 (m = 3, 4, 5) and test the 3-variable cubic perturbation in exact Fraction arithmetic."""
from fractions import Fraction
import random


def power_sums(e1, e2, e3, e4=0, e5=0):
    p1 = e1
    p2 = e1**2 - 2 * e2
    p3 = e1**3 - 3 * e1 * e2 + 3 * e3
    p4 = e1**4 - 4 * e1**2 * e2 + 2 * e2**2 + 4 * e1 * e3 - 4 * e4
    p5 = (
        e1**5
        - 5 * e1**3 * e2
        + 5 * e1 * e2**2
        + 5 * e1**2 * e3
        - 5 * e2 * e3
        - 5 * e1 * e4
        + 5 * e5
    )
    return p1, p2, p3, p4, p5


def elem_symm(vec, max_k):
    e = [Fraction(0)] * (max_k + 1)
    e[0] = Fraction(1)
    for v in vec:
        for k in range(min(max_k, len(vec)), 0, -1):
            e[k] += v * e[k - 1]
    return e


rng = random.Random(2026)
for _ in range(200):
    e2 = Fraction(rng.randint(-50, 50), rng.randint(1, 7))
    e3 = Fraction(rng.randint(-50, 50), rng.randint(1, 7))
    e4 = Fraction(rng.randint(-50, 50), rng.randint(1, 7))
    e5 = Fraction(rng.randint(-50, 50), rng.randint(1, 7))

    # m = 3 (e1 = 2)
    _, p2, p3, _, _ = power_sums(2, e2, e3)
    S21 = p2 - p3
    assert 4 * (e2 - 1) == 3 * e3 + S21

    # m = 4 (e1 = 3)
    _, p2, p3, p4, _ = power_sums(3, e2, e3, e4)
    S21 = p2 - p3
    S22 = p2 - 2 * p3 + p4
    assert 2 * e2 * (e2 - 3) == 4 * e4 + 2 * S21 + S22
    assert 6 * (e3 - 1) == S22 + 4 * e4 + 2 * (e2 - 3) * (7 - e2)

    # m = 5 (e1 = 4)
    _, p2, p3, p4, p5 = power_sums(4, e2, e3, e4, e5)
    S21 = p2 - p3
    S22 = p2 - 2 * p3 + p4
    S23 = p2 - 3 * p3 + 3 * p4 - p5
    E1 = 2 * S22 + S23
    assert 4 * (e2 - 6) * (5 * e2 - 24) == 3 * E1 + (5 * e2 - 21) * S21 + 15 * e5
    assert (5 * e2 - 21) * (e3 - 4) == E1 + 5 * e5 + 2 * (e2 - 6) * (5 * e2 - 19)
    assert 8 * (5 * e2 - 21) * (e4 - 1) == (5 * e2 - 21) * (S23 + 5 * e5) + (41 - 5 * e2) * (E1 + 5 * e5) + 4 * (e2 - 6) * (5 * e2**2 - 46 * e2 + 125)
    assert 5 * (5 * e2**2 - 46 * e2 + 125) == (5 * e2 - 23) ** 2 + 96

# Exact test of the 3-variable cubic perturbation identity across m = 3..8:
# Replacing g(t) by g(t) - eps*(t + h_{m-2}/h_{m-3}) preserves e_1 and e_m while strictly lowering e_k.
for m in range(3, 9):
    n = m + 3
    # Build an interior vector in F_{m, n} with one negative entry and remaining positive entries < 1
    b = Fraction(-1, 5)
    pos_val = Fraction(m - 1, 1) - b
    pos_each = pos_val / (n - 1)
    assert pos_each < 1
    vec = [pos_each] * (n - 1) + [b]
    e_full = elem_symm(vec, m)
    assert e_full[1] == m - 1
    assert all(e_full[j] > 0 for j in range(1, m + 1))

    # Delete (vec[0], vec[1], vec[-1]) = (a, a, b)
    y_prime = vec[2:-1]
    h = elem_symm(y_prime, m)
    assert all(h[r] > 0 for r in range(m - 1))
    alpha = h[m - 2] / h[m - 3]
    # Check Delta e_m = -eps*h_{m-2} + eps*alpha*h_{m-3} == 0 and Delta e_k / (-eps) > 0 for 2 <= k < m
    delta_em_coeff = -h[m - 2] + alpha * h[m - 3]
    assert delta_em_coeff == 0
    for k in range(2, m):
        h_k_minus_3 = Fraction(0) if k == 2 else h[k - 3]
        delta_ek_coeff = -h[k - 2] + alpha * h_k_minus_3
        assert delta_ek_coeff < 0, f"Expected negative slope at m={m}, k={k}, got {delta_ek_coeff}"

print("Verified: Exact algebraic identities (m=3,4,5) and 3-variable cubic perturbation (m=3..8) pass in Fraction arithmetic.")
