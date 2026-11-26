#!/usr/bin/env python3
"""
Exact rational verification tool for MathOverflow #476077
("Bounding elementary symmetric polynomials away from zero").

Rescaled convention:
  d = m - 1, y_i = d * x_i.
Hypotheses:
  1. y_i <= 1 for all i
  2. e_1(y) = d
  3. e_j(y) >= 0 for all 1 <= j <= m
Conjecture:
  e_k(y) >= comb(d, k) for all 1 <= k <= d.
"""

from fractions import Fraction
from math import comb
import sys
import json


def poly_esymm_exact(ys):
    """Return [e_0(y), e_1(y), ..., e_n(y)] as exact Fractions."""
    n = len(ys)
    e = [Fraction(0)] * (n + 1)
    e[0] = Fraction(1)
    for y in ys:
        yf = Fraction(y)
        for j in range(n, 0, -1):
            e[j] += yf * e[j - 1]
    return e


def verify_vector(ys_raw, m, max_denom=10**9, adjust_for_exact_e1=True):
    """
    Verify whether a vector y (or its exact rational approximation) satisfies
    all MO #476077 hypotheses and whether it violates any e_k >= comb(d, k).
    """
    d = m - 1
    n = len(ys_raw)
    if n < m:
        return {"valid_dim": False, "reason": f"n={n} < m={m}"}

    ys = [Fraction(v).limit_denominator(max_denom) if not isinstance(v, Fraction) else v for v in ys_raw]
    if adjust_for_exact_e1:
        # Adjust the smallest-index entry strictly below 1 (or any entry) so sum(ys) == d
        diff = Fraction(d) - sum(ys)
        if diff != 0:
            # Prefer adjusting an entry strictly < 1 so y_i <= 1 stays intact
            idx = min(range(n), key=lambda i: ys[i])
            ys[idx] += diff

    max_y = max(ys)
    e = poly_esymm_exact(ys)

    hyp_max = max_y <= 1
    hyp_e1 = e[1] == d
    hyp_ej = all(e[j] >= 0 for j in range(1, m + 1))
    feasible = hyp_max and hyp_e1 and hyp_ej

    violations = []
    min_gap = None
    min_ratio = None
    for k in range(1, d + 1):
        target = Fraction(comb(d, k))
        gap = e[k] - target
        ratio = float(e[k] / target) if target != 0 else 1.0
        if min_gap is None or gap < min_gap[1]:
            min_gap = (k, gap, e[k], target)
        if min_ratio is None or ratio < min_ratio[1]:
            min_ratio = (k, ratio, e[k], target)
        if e[k] < target:
            violations.append({
                "k": k,
                "e_k": str(e[k]),
                "e_k_float": float(e[k]),
                "bound": int(target),
                "gap": float(gap),
                "ratio": ratio,
            })

    return {
        "m": m,
        "d": d,
        "n": n,
        "feasible": feasible,
        "hyp_max_y_le_1": hyp_max,
        "max_y": str(max_y),
        "hyp_e1_eq_d": hyp_e1,
        "e1": str(e[1]),
        "hyp_ej_ge_0": hyp_ej,
        "e_1_to_m_float": [float(e[j]) for j in range(1, m + 1)],
        "e_1_to_m_exact": [str(e[j]) for j in range(1, m + 1)],
        "min_e_2_to_m": float(min(e[j] for j in range(1, m + 1))),
        "min_gap_k": min_gap[0],
        "min_gap_float": float(min_gap[1]),
        "min_ratio_k": min_ratio[0],
        "min_ratio": min_ratio[1],
        "violations": violations,
        "ys_exact": [str(v) for v in ys],
    }


def run_self_tests():
    # 1. Equality vectors y* = (1^d, 0^(n-d)) for m = 3..7
    for m in range(3, 8):
        d = m - 1
        y_star = [Fraction(1)] * d + [Fraction(0)] * (m + 2 - d)
        res = verify_vector(y_star, m, adjust_for_exact_e1=False)
        assert res["feasible"], f"Equality vector infeasible for m={m}"
        assert res["violations"] == [], f"Unexpected violation at equality for m={m}"
        assert res["min_gap_float"] == 0.0, f"Expected gap 0 at equality for m={m}"
        assert res["e_1_to_m_exact"][-1] == "0", f"Expected e_m = 0 at equality for m={m}"

    # 2. Check a known negative-entry feasible point for m=4 (d=3), n=5
    # e.g. y = (1, 1, 1, 1/4, -1/4) -> e1 = 3, (1+t)^3(1+t/4)(1-t/4) = (1+3t+3t^2+t^3)(1-t^2/16)
    # = 1 + 3t + (3 - 1/16)t^2 + (1 - 3/16)t^3 + (-3/16)t^4 -> e4 < 0 (infeasible!).
    res_bad = verify_vector([Fraction(1), Fraction(1), Fraction(1), Fraction(1, 4), Fraction(-1, 4)], 4, adjust_for_exact_e1=False)
    assert not res_bad["feasible"], "Expected (1,1,1,1/4,-1/4) to violate e_4 >= 0"

    # 3. Valid negative-entry feasible point for m=4 (d=3), n=5:
    # (1+t)(1+0.9t)^2(1+0.3t)(1-0.1t): check exact feasibility
    y_neg = [Fraction(1), Fraction(9, 10), Fraction(9, 10), Fraction(3, 10), Fraction(-1, 10)]
    res_neg = verify_vector(y_neg, 4, adjust_for_exact_e1=False)
    assert res_neg["feasible"], f"Expected feasible: {res_neg}"
    assert res_neg["violations"] == [], f"Unexpected violation for m=4: {res_neg}"

    print("verify_mo476077.py self-tests PASSED.")


if __name__ == "__main__":
    if len(sys.argv) <= 1 or sys.argv[1] == "--self-test":
        run_self_tests()
    else:
        m = int(sys.argv[1])
        vals = [Fraction(arg) for arg in sys.argv[2:]]
        out = verify_vector(vals, m, adjust_for_exact_e1=True)
        print(json.dumps(out, indent=2))
