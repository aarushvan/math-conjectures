# 05. Elementary Symmetric Polynomial Lower Bounds (MathOverflow #476077)

Complete proof of Nathaniel Johnston's conjecture ([MathOverflow #476077](https://mathoverflow.net/questions/476077/bounding-elementary-symmetric-polynomials-away-from-zero)) for all integers $2 \le m \le n$ and $1 \le k < m$, including the exact characterization of the unique equality case ($2 \le k < m$).

For arbitrary-sign real vectors $x \in \mathbb{R}^n$ with $\max_j x_j \le \frac{1}{m-1}$, $e_1(x) = 1$, and $e_j(x) \ge 0$ ($1 \le j \le m$), $e_k(x) \ge \binom{m-1}{k}/(m-1)^k$, with equality iff $(m-1)x$ permutes $(1^{m-1}, 0^{n-m+1})$. Proved via compactness, a Hermite-Biehler/Gauss-Lucas Strong Dropping Lemma for boundary minimizers, and a 3-variable cubic perturbation with Newton's inequalities and IVT double-root splitting for interior minimizers.

- [Complete proof](PROOF.md)
- [Lean 4 ring certificates ($m = 3, 4, 5$) 🟡](JohnstonEsymmM345.lean)
- [Exact rational verifiers (`verify_mo476077.py`, `verify_identities_m345.py`)](python/)
- [C++20 block & optimization search](cpp/mo476077_search.cpp) and [preliminary search report](results/search_report.md)

Run `lean JohnstonEsymmM345.lean && python3 python/verify_mo476077.py --self-test && python3 python/verify_identities_m345.py`.
