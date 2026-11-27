# 05. Elementary Symmetric Polynomial Lower Bounds (MathOverflow #476077)

Complete proof of Nathaniel Johnston's conjecture ([MathOverflow #476077](https://mathoverflow.net/questions/476077/bounding-elementary-symmetric-polynomials-away-from-zero)) for all integers $2 \le m \le n$ and $1 \le k < m$, including the exact characterization of the unique equality case ($2 \le k < m$).

For arbitrary-sign real vectors $x \in \mathbb{R}^n$ with $\max_j x_j \le \frac{1}{m-1}$, $e_1(x) = 1$, and $e_j(x) \ge 0$ ($1 \le j \le m$), $e_k(x) \ge \binom{m-1}{k}/(m-1)^k$, with equality iff $(m-1)x$ permutes $(1^{m-1}, 0^{n-m+1})$. Proved via compactness, a Hermite-Biehler/Gauss-Lucas Strong Dropping Lemma for boundary minimizers, and a 3-variable cubic perturbation with Newton's inequalities and IVT double-root splitting for interior minimizers.

- [Complete proof](PROOF.md)
- [Lean 4 ring certificates](JohnstonEsymmM345.lean) ($m = 3, 4, 5$) 🟡
- [Exact rational verifiers (`verify_mo476077.py`, `verify_identities_m345.py`)](python/)
- [C++20 block & optimization search](cpp/mo476077_search.cpp) and [preliminary search report](results/search_report.md)
- [Statement Audit](../docs/STATEMENT_AUDIT.md#track-05-elementary-symmetric-polynomial-lower-bounds-mo-476077--partial)

Run `lean JohnstonEsymmM345.lean && python3 python/verify_mo476077.py --self-test && python3 python/verify_identities_m345.py`.

## Statement Audit & Remaining Lemmas for Full End-to-End Lean Formalization

`JohnstonEsymmM345.lean` stays honestly marked **🟡 Partial**: it kernel-checks the exact polynomial-ring certificates over `Int` (`identity_m3_e2`, `identity_m4_e2`, `identity_m4_e3`, `identity_m5_e2`, `identity_m5_e3`, `identity_m5_e4`, `m5_quadratic_pos`), which lift to $\mathbb{R}$ once paired with `S2r >= 0`. Turning Track `05` into a full end-to-end ✅ proof over $\mathbb{R}^n$ would require formalizing three analytic/real-algebraic components (currently proved in [PROOF.md](PROOF.md)):

1. Connecting `S2r` to $\sum_{i=1}^n y_i^2 (1 - y_i)^r \ge 0$ over $\mathbb{R}^n$ for $y_i \le 1$ via Newton's power-sum identities.
2. Arbitrary-$m$ compactness of $\mathcal{F}_{m,n}$ plus the Hermite-Biehler / Gauss-Lucas Strong Dropping Lemma for boundary minimizers ($y_i^* = 1$).
3. Newton's inequalities and the Intermediate Value Theorem 3-variable cubic perturbation eliminating interior minimizers ($y_i^* < 1$).
