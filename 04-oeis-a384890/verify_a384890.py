#!/usr/bin/env python3
"""
Independent verifier for Gus Wiseman's question on OEIS A384890:
"Do all constant runs in this sequence have lengths 1, 2, or 3?"

Verifies:
1. Direct anti-run definition on binary indices matches all 87 live OEIS terms (n=0..86).
2. Exact formula a(n) = 1 + popcount(n & (n >> 1)) for n >= 1 holds for 1 <= n <= 20000.
3. All constant runs in a(0..1000000) have length 1, 2, or 3.
"""

OEIS_A384890 = [
    0,1,1,2,1,1,2,3,1,1,1,2,2,2,3,4,1,1,1,2,1,1,2,3,2,2,2,3,3,3,4,5,
    1,1,1,2,1,1,2,3,1,1,1,2,2,2,3,4,2,2,2,3,2,2,3,4,3,3,3,4,4,4,5,6,
    1,1,1,2,1,1,2,3,1,1,1,2,2,2,3,4,1,1,1,2,1,1,2
]


def a384890_direct(n):
    """Count maximal anti-runs (adjacent increments > 1) in binary indices of n."""
    if n == 0:
        return 0
    indices = []
    pos = 1
    m = n
    while m:
        if m & 1:
            indices.append(pos)
        m >>= 1
        pos += 1
    runs = 1
    for i in range(1, len(indices)):
        if indices[i] - indices[i - 1] == 1:
            runs += 1
    return runs


def a384890_bit(n):
    if n == 0:
        return 0
    return 1 + bin(n & (n >> 1)).count("1")


def main():
    for n, val in enumerate(OEIS_A384890):
        d = a384890_direct(n)
        b = a384890_bit(n)
        assert d == val and b == val, f"Mismatch at n={n}: oeis={val}, direct={d}, bit={b}"

    for n in range(1, 20001):
        assert a384890_direct(n) == a384890_bit(n), f"Formula mismatch at n={n}"

    cur = a384890_bit(0)
    run_len = 1
    lengths_seen = set()
    for n in range(1, 1000001):
        v = a384890_bit(n)
        if v == cur:
            run_len += 1
        else:
            assert run_len in (1, 2, 3), f"Bad run length {run_len} ending before n={n}"
            lengths_seen.add(run_len)
            cur = v
            run_len = 1

    print(f"Verified A384890 against {len(OEIS_A384890)} OEIS terms, formula up to 20000, "
          f"and run lengths {sorted(lengths_seen)} up to 1,000,000.")
    print("verify_a384890.py PASSED.")


if __name__ == "__main__":
    main()
