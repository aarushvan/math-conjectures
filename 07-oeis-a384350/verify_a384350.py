#!/usr/bin/env python3
"""Exhaustively verify OEIS A384350 subset-by-subset equivalence for n = 0..11."""


def strict_partitions(x, max_v=None):
    if max_v is None:
        max_v = x
    if x == 0:
        yield ()
        return
    for v in range(min(x, max_v), 0, -1):
        for rest in strict_partitions(x - v, v - 1):
            yield (v,) + rest


SP_CACHE = {x: list(strict_partitions(x)) for x in range(1, 12)}


def prop_non_element_sum(S, n):
    non_el = [y for y in range(1, n + 1) if y not in S]
    sums = {0}
    for y in non_el:
        sums |= {s + y for s in sums}
    return any(x in sums for x in S)


def prop_more_than_one_disjoint_family(S):
    elems = sorted(S)
    count = 0

    def bt(idx, used):
        nonlocal count
        if count >= 2:
            return
        if idx == len(elems):
            count += 1
            return
        for p in SP_CACHE[elems[idx]]:
            if all(y not in used for y in p):
                used.update(p)
                bt(idx + 1, used)
                used.difference_update(p)

    bt(0, set())
    return count >= 2


# Live OEIS A384350(0..11)
OEIS_A384350 = [0, 0, 0, 1, 4, 13, 33, 81, 183, 402, 856, 1801]

seq = []
for n in range(0, 12):
    cnt = 0
    for mask in range(1 << n):
        S = {i + 1 for i in range(n) if (mask >> i) & 1}
        a = prop_non_element_sum(S, n)
        b = prop_more_than_one_disjoint_family(S)
        assert a == b, f"Mismatch at n={n}, S={S}: {a} != {b}"
        if a:
            cnt += 1
    seq.append(cnt)

assert seq == OEIS_A384350, f"Mismatch vs OEIS A384350: {seq}"
print("A384350(0..11):", seq)
print("Verified: 0 mismatches across all 4095 subsets for n = 0..11; matches live OEIS A384350.")
