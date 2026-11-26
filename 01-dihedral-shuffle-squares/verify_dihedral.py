#!/usr/bin/env python3
"""
Independent exhaustive verifier for Conjecture 2 of
"Variations on shuffle squares" (Grytczuk, Pawlik, Pleszczynski, arXiv:2308.13882v2).

Verifies:
1. Exact exhaustive search over ALL even 3-letter ternary words of length 6 (n=3) and length 8 (n=4).
2. Orbit classification under S_3 x D_{2n} for length 8 counterexamples.
3. Exact verification that W_n = 0^(2n-5) 11022 fails for n = 4, 5, 6, 7, 8.
"""

from itertools import product


def dihedral_perms(n):
    """Return all permutations in D_n (0-indexed rotations and reflections)."""
    perms = []
    for k in range(n):
        perms.append(tuple((i + k) % n for i in range(n)))
        perms.append(tuple((k - i) % n for i in range(n)))
    return list(dict.fromkeys(perms))


def is_gamma_shuffle_square(word, perm):
    """
    Check if `word` (length 2n) splits into disjoint subsequences U, V of length n
    such that V[j] == U[perm[j]] for all j in 0..n-1.
    Uses exact memoization on failed (u_tuple, v_tuple) prefixes.
    """
    n = len(perm)
    inv = [0] * n
    for j, p in enumerate(perm):
        inv[p] = j
    failed = set()

    def backtrack(idx, u, v):
        if idx == 2 * n:
            return True
        state = (u, v)
        if state in failed:
            return False
        ch = word[idx]
        lu, lv = len(u), len(v)
        if lu < n:
            vp = inv[lu]
            if vp >= lv or v[vp] == ch:
                if backtrack(idx + 1, u + (ch,), v):
                    return True
        if lv < n:
            up = perm[lv]
            if up >= lu or u[up] == ch:
                if backtrack(idx + 1, u, v + (ch,)):
                    return True
        failed.add(state)
        return False

    return backtrack(0, (), ())


def is_dihedral_shuffle_square(word):
    n = len(word) // 2
    perms = dihedral_perms(n)
    for perm in perms:
        if is_gamma_shuffle_square(word, perm):
            return True, perm
    return False, None


def canonical_s3_d2n(w):
    """Canonical representative of w under S_3 alphabet relabeling and D_{2n} dihedral actions."""
    L = len(w)
    best = None
    perms_s3 = [
        (0, 1, 2), (0, 2, 1),
        (1, 0, 2), (1, 2, 0),
        (2, 0, 1), (2, 1, 0),
    ]
    for rev in (w, w[::-1]):
        for shift in range(L):
            rot = rev[shift:] + rev[:shift]
            for p in perms_s3:
                cand = tuple(p[c] for c in rot)
                if best is None or cand < best:
                    best = cand
    return best


def main():
    # 1. Exhaustive check for n = 3 (length 6) and n = 4 (length 8)
    for n in (3, 4):
        total_even_3 = 0
        counterexamples = []
        orbits = set()
        for w in product((0, 1, 2), repeat=2 * n):
            if w.count(0) % 2 or w.count(1) % 2 or w.count(2) % 2:
                continue
            if 0 not in w or 1 not in w or 2 not in w:
                continue
            total_even_3 += 1
            ok, _ = is_dihedral_shuffle_square(w)
            if not ok:
                counterexamples.append("".join(map(str, w)))
                orbits.add("".join(map(str, canonical_s3_d2n(w))))
        print(
            f"n={n} (len={2*n}): total_even_ternary={total_even_3}, "
            f"counterexamples={len(counterexamples)}, canonical_orbits={len(orbits)}"
        )
        if orbits:
            print("  canonical orbit reps:", sorted(orbits))
        if n == 3:
            assert len(counterexamples) == 0, "Expected 0 counterexamples at n=3 (D_3 = S_3)"
        if n == 4:
            assert "00011022" in counterexamples, "Expected 00011022 to be a counterexample at n=4"

    # 2. Verify W_n = 0^(2n-5) 11022 for n = 4..8
    for n in range(4, 9):
        w = (0,) * (2 * n - 5) + (1, 1, 0, 2, 2)
        ok, perm = is_dihedral_shuffle_square(w)
        w_str = "".join(map(str, w))
        print(f"W_{n} = {w_str} (len={len(w)}): dihedral_shuffle_square={ok}")
        assert not ok, f"Unexpectedly found dihedral split for W_{n}: {perm}"

    print("verify_dihedral.py PASSED.")


if __name__ == "__main__":
    main()
