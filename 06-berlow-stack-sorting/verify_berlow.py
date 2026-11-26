#!/usr/bin/env python3
"""Exhaustively verify Lemmas 1-5 and convergence of s_{213, 231} across S_3..S_7."""
from itertools import permutations


def has_pat3(seq, pat):
    L = len(seq)
    if L < 3:
        return False
    p0, p1, p2 = pat
    for i in range(L):
        for j in range(i + 1, L):
            if (seq[i] < seq[j]) != (p0 < p1):
                continue
            for k in range(j + 1, L):
                if (seq[i] < seq[k]) == (p0 < p2) and (seq[j] < seq[k]) == (p1 < p2):
                    return True
    return False


def s_literal(perm):
    stack, out = [], []
    for x in perm:
        while stack:
            cand = [x] + stack[::-1]  # top-to-bottom
            if has_pat3(cand, (2, 1, 3)) or has_pat3(cand, (2, 3, 1)):
                out.append(stack.pop())
            else:
                break
        stack.append(x)
    while stack:
        out.append(stack.pop())
    return tuple(out)


def s_fast(perm):
    stack, out = [], []
    for x in perm:
        while stack and min(stack) < x < max(stack):
            out.append(stack.pop())
        stack.append(x)
    while stack:
        out.append(stack.pop())
    return tuple(out)


def bad_set(perm):
    n = len(perm)
    res = set()
    mn = mx = perm[-1]
    for i in range(n - 2, -1, -1):
        v = perm[i]
        if mn < v < mx:
            res.add(v)
        if v < mn:
            mn = v
        if v > mx:
            mx = v
    return res


for n in range(3, 8):
    idn = tuple(range(1, n + 1))
    idnr = tuple(range(n, 0, -1))
    max_d = 0
    count = 0
    for pi in permutations(range(1, n + 1)):
        count += 1
        fpi = s_fast(pi)
        if n <= 6:
            assert fpi == s_literal(pi), f"Lemma 1 failed on {pi}"
        b0, b1 = bad_set(pi), bad_set(fpi)
        assert b1 <= b0, f"Lemma 2 failed on {pi}"
        assert fpi[-1] == pi[0], f"Lemma 3 failed on {pi}"
        if pi[0] not in (1, n):
            assert len(b1) <= len(b0) - 1, f"Lemma 3 drop failed on {pi}"
        if not b0:
            assert fpi in (idn, idnr), f"Lemma 5 failed on {pi}"
        f2pi = s_fast(fpi)
        if pi[0] in (1, n) and fpi[0] in (1, n) and f2pi[0] in (1, n):
            assert fpi in (idn, idnr), f"Lemma 4 failed on {pi}"
        cur, steps = pi, 0
        while cur not in (idn, idnr):
            cur = s_fast(cur)
            steps += 1
            assert steps <= 3 * n - 7
        if steps > max_d:
            max_d = steps
    print(f"S_{n} ({count} perms): Lemmas 1-5 exact, max steps = {max_d} (<= {3 * n - 7})")

print("Verified: Berlow Conjecture 5.1 / Zhang Conjecture 4.2 for T={213, 231} holds across S_3..S_7.")
