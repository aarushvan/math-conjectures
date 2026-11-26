#!/usr/bin/env python3
"""
Independent exhaustive verifier for Gus Wiseman's conjectures on
OEIS A382427 and OEIS A381717.

Verifies for n = 0..22:
1. Partitioning into constant blocks with pairwise distinct sums
   is equivalent to admitting a permutation with pairwise distinct maximal run-sums.
2. Exact partition counts match the published OEIS data for A382427 and A381717.
"""

from collections import Counter


OEIS_A382427 = [1, 1, 2, 3, 4, 7, 11, 14, 19, 28, 39, 50, 70, 91, 120, 161, 203, 260, 338, 426, 556, 695, 863]
OEIS_A381717 = [0, 0, 0, 0, 1, 0, 0, 1, 3, 2, 3, 6, 7, 10, 15, 15, 28, 37, 47, 64, 71, 97, 139]


def strict_partitions(m, min_v=1):
    if m == 0:
        yield ()
        return
    for x in range(min_v, m + 1):
        for rest in strict_partitions(m - x, x + 1):
            yield (x,) + rest


def has_distinct_const_blocks(counts):
    def bt(idx, used_sums):
        if idx == len(counts):
            return True
        val, m = counts[idx]
        for sp in strict_partitions(m):
            sums = [val * x for x in sp]
            if all(s not in used_sums for s in sums):
                used_sums.update(sums)
                if bt(idx + 1, used_sums):
                    return True
                used_sums.difference_update(sums)
        return False

    return bt(0, set())


def has_distinct_run_sum_perm(counts):
    if not counts:
        return True

    def bt(idx, used_sums, ks):
        if idx == len(counts):
            return 2 * max(ks) <= sum(ks) + 1
        val, m = counts[idx]
        for sp in strict_partitions(m):
            sums = [val * x for x in sp]
            if all(s not in used_sums for s in sums):
                used_sums.update(sums)
                ks.append(len(sp))
                if bt(idx + 1, used_sums, ks):
                    return True
                ks.pop()
                used_sums.difference_update(sums)
        return False

    return bt(0, set(), [])


def gen_partitions(n, max_v=None):
    if max_v is None:
        max_v = n
    if n == 0:
        yield ()
        return
    for v in range(min(n, max_v), 0, -1):
        for rest in gen_partitions(n - v, v):
            yield (v,) + rest


def main():
    a382427_computed = []
    a381717_computed = []
    for n in range(len(OEIS_A382427)):
        c_yes = 0
        c_no = 0
        for p in gen_partitions(n):
            counts = tuple(sorted(Counter(p).items()))
            a = has_distinct_const_blocks(counts)
            b = has_distinct_run_sum_perm(counts)
            assert a == b, f"Equivalence failed at n={n}, partition={p}: A={a}, B={b}"
            if a:
                c_yes += 1
            else:
                c_no += 1
        a382427_computed.append(c_yes)
        a381717_computed.append(c_no)

    assert a382427_computed == OEIS_A382427, f"A382427 mismatch: {a382427_computed}"
    assert a381717_computed == OEIS_A381717, f"A381717 mismatch: {a381717_computed}"
    print(f"Verified A382427 & A381717 equivalence and exact counts for n=0..{len(OEIS_A382427)-1}.")
    print("verify_a382427.py PASSED.")


if __name__ == "__main__":
    main()
