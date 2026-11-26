#!/usr/bin/env python3
"""Verify OEIS A383093 Mobius identity against live OEIS A383093 and A323774 for n = 1..24."""
import math
from collections import Counter


def lcm(a, b):
    return a * b // math.gcd(a, b)


def gen_partitions(n, max_v=None):
    if max_v is None:
        max_v = n
    if n == 0:
        yield ()
        return
    for v in range(min(n, max_v), 0, -1):
        for rest in gen_partitions(n - v, v):
            yield (v,) + rest


def a383093(n):
    if n == 0:
        return 1
    cnt = 0
    for p in gen_partitions(n):
        c = Counter(p)
        L = 1
        G = 0
        for x, mult in c.items():
            L = lcm(L, x)
            G = math.gcd(G, mult * x)
        if G % L == 0:
            cnt += 1
    return cnt


def tau(s):
    return sum(1 for d in range(1, s + 1) if s % d == 0)


def F(n):
    return sum(math.comb(n // s + tau(s) - 1, n // s) for s in range(1, n + 1) if n % s == 0)


# Live OEIS A383093(0..24) and A323774(1..24)
OEIS_A383093_0_TO_24 = [1, 1, 2, 2, 4, 2, 7, 2, 9, 5, 9, 2, 23, 2, 11, 10, 24, 2, 33, 2, 36, 12, 15, 2, 87]
OEIS_A323774_1_TO_24 = [1, 3, 3, 7, 3, 12, 3, 16, 8, 14, 3, 39, 3, 16, 15, 40, 3, 50, 3, 54, 17, 20, 3, 135]

a_vals = {n: a383093(n) for n in range(0, 25)}
computed_a = [a_vals[n] for n in range(0, 25)]
assert computed_a == OEIS_A383093_0_TO_24, f"Mismatch vs OEIS A383093: {computed_a}"

for n in range(1, 25):
    lhs = sum(a_vals[d] for d in range(1, n + 1) if n % d == 0)
    rhs = F(n)
    assert lhs == rhs == OEIS_A323774_1_TO_24[n - 1], f"Mismatch at n={n}: {lhs}, {rhs}, {OEIS_A323774_1_TO_24[n - 1]}"

print("A383093(0..24):", computed_a)
print("Verified: sum_{d|n} A383093(d) == A323774(n) == F(n) for all n = 1..24 against live OEIS.")
