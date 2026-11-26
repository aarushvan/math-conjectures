#!/usr/bin/env python3
"""Complete computational and certificate verifier for arXiv:2308.13882v2 Conjecture 1.

Proves that W(n) = 0^(n-7) 1 0^2 1^4 0^(n-8) 1^3 0 1^4 is a binary shuffle anti-square
of length 2n for every integer n >= 12:
  1. Verifies the DP shuffle-square oracle against brute-force partitions up to length 10.
  2. Directly checks all cyclic shifts of W(n) for every n = 12..45 (lengths 24..90).
  3. Extracts and independently verifies in exact integer arithmetic all 568 Farkas dual
     certificates proving LP infeasibility over R_{>= 0} for every cut and 1-run split
     for all t = n - 12 >= 0 simultaneously.
"""

import argparse
from functools import lru_cache
from fractions import Fraction
from itertools import combinations
import math


def lcm(a, b):
    return a * b // math.gcd(a, b)


def make_word(n):
    if n < 12:
        raise ValueError("n must be >= 12")
    return "0" * (n - 7) + "1" + "00" + "1111" + "0" * (n - 8) + "111" + "0" + "1111"


def shuffle_square(word):
    half = len(word) // 2

    @lru_cache(maxsize=None)
    def match(i, pending):
        if i == len(word):
            return not pending
        bit = word[i]
        if pending and bit == pending[0] and match(i + 1, pending[1:]):
            return True
        longer_len = (i + len(pending)) // 2
        return longer_len < half and match(i + 1, pending + bit)

    res = match(0, "")
    match.cache_clear()
    return res


def brute_shuffle_square(word):
    n2 = len(word)
    for comb in combinations(range(1, n2), n2 // 2 - 1):
        left = {0, *comb}
        u = [word[i] for i in range(n2) if i in left]
        v = [word[i] for i in range(n2) if i not in left]
        if u == v:
            return True
    return False


def is_anti_square(word):
    shifts = dict.fromkeys(word[i:] + word[:i] for i in range(len(word)))
    return not any(shuffle_square(s) for s in shifts)


def get_cut_templates():
    # Cyclic blocks of W(12 + t): Z(5+t), O(1), Z(2), O(4), Z(4+t), O(3), Z(1), O(4)
    # Ordered as: 4 Z-cuts (tidx = 0..3), then 8 O-cuts (tidx = 4..11).
    circ = [("Z", 0), ("O", 1), ("Z", 1), ("O", 4), ("Z", 2), ("O", 3), ("Z", 3), ("O", 4)]
    z_cuts = []
    o_cuts = []
    for idx, (kind, val) in enumerate(circ):
        if kind == "Z":
            seq = [("Z", (val, "tail"))] + circ[idx + 1 :] + circ[:idx] + [("Z", (val, "head"))]
            z_cuts.append((f"cutZ_{val}", seq, val))
        else:
            for p in range(1, val):
                seq = [("O", val - p)] + circ[idx + 1 :] + circ[:idx] + [("O", p)]
                o_cuts.append((f"cutO_{idx}_{p}", seq, None))
    return z_cuts + o_cuts


def enum_run_splits(o_lens):
    res = []

    def bt(idx, rem, cur):
        if idx == len(o_lens):
            if rem == 0:
                res.append(tuple(cur))
            return
        max_after = sum(o_lens[idx + 1 :])
        lo = max(0, rem - max_after)
        hi = min(o_lens[idx], rem)
        for k in range(lo, hi + 1):
            cur.append(k)
            bt(idx + 1, rem - k, cur)
            cur.pop()

    bt(0, 6, [])
    return res


def build_linear_system(seq, split_z, ks):
    """Build exact equality system (rows, rhs_list) over variables [t, x_0..x_{nz-1}, y_0..y_{nz-1}] >= 0."""
    # Zero run lengths as (const, t_coeff): Z0 = 5+t, Z1 = 2, Z2 = 4+t, Z3 = 1
    z_specs = [(5, 1), (2, 0), (4, 1), (1, 0)]
    o_lens = [val for kind, val in seq if kind == "O"]
    z_positions = []
    o_idx = 0
    for kind, val in seq:
        if kind == "O":
            o_idx += 1
        else:
            z_positions.append((val, o_idx))
    nz = len(z_positions)
    nvars = 1 + 2 * nz
    eqs = []

    if split_z is not None:
        c_val, t_coeff = z_specs[split_z]
        row = [0] * nvars
        row[0] = -t_coeff
        row[1 + 0] = 1
        row[1 + nz + 0] = 1
        row[1 + nz - 1] = 1
        row[1 + nz + nz - 1] = 1
        eqs.append((row, c_val))
        for j in range(1, nz - 1):
            z_id = z_positions[j][0]
            c_val, t_coeff = z_specs[z_id]
            row = [0] * nvars
            row[0] = -t_coeff
            row[1 + j] = 1
            row[1 + nz + j] = 1
            eqs.append((row, c_val))
    else:
        for j in range(nz):
            z_id = z_positions[j][0]
            c_val, t_coeff = z_specs[z_id]
            row = [0] * nvars
            row[0] = -t_coeff
            row[1 + j] = 1
            row[1 + nz + j] = 1
            eqs.append((row, c_val))

    for r in range(7):
        row = [0] * nvars
        for j, (_, o_before) in enumerate(z_positions):
            u_b = sum(ks[:o_before])
            v_b = sum(o_lens[:o_before]) - u_b
            if u_b == r:
                row[1 + j] += 1
            if v_b == r:
                row[1 + nz + j] -= 1
        eqs.append((row, 0))
    return eqs, nvars


def simplex_farkas_int(eqs, nvars):
    """Return an integer Farkas dual vector d such that d^T A >= 0 and d^T b < 0."""
    m = len(eqs)
    A, b, signs = [], [], []
    for row, r in eqs:
        row_f = [Fraction(v) for v in row]
        r_f = Fraction(r)
        if r_f < 0:
            row_f = [-v for v in row_f]
            r_f = -r_f
            signs.append(-1)
        else:
            signs.append(1)
        A.append(row_f)
        b.append(r_f)

    tot = nvars + m
    T = [A[i] + [Fraction(1 if j == i else 0) for j in range(m)] + [b[i]] for i in range(m)]
    obj = [-sum(A[i][j] for i in range(m)) for j in range(nvars)] + [Fraction(0)] * m + [-sum(b)]
    basis = [nvars + i for i in range(m)]

    while True:
        piv_col = next((j for j in range(tot) if obj[j] < 0), -1)
        if piv_col == -1:
            break
        piv_row, best_ratio = -1, None
        for i in range(m):
            if T[i][piv_col] > 0:
                ratio = T[i][tot] / T[i][piv_col]
                if piv_row == -1 or ratio < best_ratio or (ratio == best_ratio and basis[i] < basis[piv_row]):
                    best_ratio, piv_row = ratio, i
        assert piv_row != -1
        pv = T[piv_row][piv_col]
        T[piv_row] = [v / pv for v in T[piv_row]]
        for i in range(m):
            if i != piv_row and T[i][piv_col] != 0:
                f = T[i][piv_col]
                T[i] = [T[i][k] - f * T[piv_row][k] for k in range(tot + 1)]
        if obj[piv_col] != 0:
            f = obj[piv_col]
            obj = [obj[k] - f * T[piv_row][k] for k in range(tot + 1)]
        basis[piv_row] = piv_col

    assert obj[tot] < 0, "Expected infeasible LP"
    y_frac = [-(Fraction(1) - obj[nvars + i]) * signs[i] for i in range(m)]
    denom = 1
    for q in y_frac:
        denom = lcm(denom, q.denominator)
    y_int = [int(q * denom) for q in y_frac]
    g = 0
    for v in y_int:
        g = math.gcd(g, abs(v))
    if g > 1:
        y_int = [v // g for v in y_int]

    # Exact integer verification (zero Fractions needed)
    for col in range(nvars):
        assert sum(y_int[i] * eqs[i][0][col] for i in range(m)) >= 0
    assert sum(y_int[i] * eqs[i][1] for i in range(m)) < 0
    return y_int


def emit_lean_table():
    templates = get_cut_templates()
    print("/-- Generated exact Farkas dual certificates for all 568 (template, 1-split) cases. -/")
    print("def allCerts : List (Nat × List Nat × List Int) := [")
    for tidx, (tname, seq, split_z) in enumerate(templates):
        o_lens = [val for kind, val in seq if kind == "O"]
        for ks in enum_run_splits(o_lens):
            eqs, nvars = build_linear_system(seq, split_z, ks)
            dual = simplex_farkas_int(eqs, nvars)
            ks_str = "[" + ", ".join(str(k) for k in ks) + "]"
            d_str = "[" + ", ".join(str(d) for d in dual) + "]"
            print(f"  ({tidx}, {ks_str}, {d_str}),")
    print("]")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit-lean", action="store_true", help="Print Lean 4 Farkas certificate table")
    args = parser.parse_args()
    if args.emit_lean:
        emit_lean_table()
        return

    checked = 0
    for L in range(2, 11, 2):
        for val in range(1 << L):
            w = format(val, f"0{L}b")
            if w.count("1") % 2 == 0:
                assert shuffle_square(w) == brute_shuffle_square(w), f"Oracle mismatch on {w}"
                checked += 1

    for n in range(12, 46):
        w = make_word(n)
        assert len(w) == 2 * n
        assert w.count("1") == 12
        assert w.count("0") == 2 * n - 12
        assert is_anti_square(w), f"Failed anti-square check at n={n}"

    templates = get_cut_templates()
    assert len(templates) == 12
    total_certs = 0
    for tname, seq, split_z in templates:
        o_lens = [val for kind, val in seq if kind == "O"]
        for ks in enum_run_splits(o_lens):
            eqs, nvars = build_linear_system(seq, split_z, ks)
            dual = simplex_farkas_int(eqs, nvars)
            assert len(dual) == len(eqs)
            total_certs += 1

    assert total_certs == 568
    print(f"Oracle checked on {checked} even words (len <= 10).")
    print("Direct anti-square check passed for W(n), n = 12..45 (lengths 24..90).")
    print(f"All {total_certs} run-level LP systems across 12 cyclic cut templates certified infeasible by exact integer Farkas duals.")


if __name__ == "__main__":
    main()
