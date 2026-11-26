# Machine-Verified Proofs, Disproofs & Formalizations for Open Conjectures

Independently audited mathematical proofs, counterexamples, and zero-dependency Lean 4 formalizations (`leanprover/lean4:v4.36.0`) for combinatorics, word combinatorics, and OEIS conjectures.

## Verified Results Summary

| Tier | Problem & Source | Verdict | Key Result | Formal / Verifier |
| :---: | :--- | :--- | :--- | :--- |
| **S** | **Dihedral Shuffle Squares** ([arXiv:2308.13882v2](https://arxiv.org/abs/2308.13882v2), Conj. 2; Grytczuk, Pawlik & Pleszczyński) | **Disproved** | False for all even lengths $2n \ge 8$. Minimal counterexample `00011022` (the unique $S_3 \times D_8$ orbit of all 48 length-8 counterexamples) and infinite family $W_n = \mathtt{0}^{2n-5}\mathtt{11022}$ ($n \ge 4$) via cyclic adjacent-$\mathtt{00}$ invariance under $D_n$. | [`DihedralShuffleDisproof.lean`](01-dihedral-shuffle-squares/DihedralShuffleDisproof.lean) · [`verify_dihedral.py`](01-dihedral-shuffle-squares/verify_dihedral.py) · [Proof](01-dihedral-shuffle-squares/PROOF.md) |
| **B+** | **Constant-Block vs. Distinct Run-Sum Partitions** ([OEIS A382427](https://oeis.org/A382427) / [A381717](https://oeis.org/A381717); Gus Wiseman, 2025) | **Proved** | Exact equivalence for all integer partitions via minimum-block Pigeonhole merge and forbidden-head inductive interleaving. | [`WisemanA382427.lean`](02-oeis-a382427-a381717/WisemanA382427.lean) · [`verify_a382427.py`](02-oeis-a382427-a381717/verify_a382427.py) · [Proof](02-oeis-a382427-a381717/PROOF.md) |
| **B** | **Prime-Difference Greedy Deviation Bound** ([OEIS A377090](https://oeis.org/A377090); M. F. Hasler, Feb 2025) | **Disproved** | $\bigl\|\|a(n)\| - n/2\bigr\| < 2\ln(n+2)$ fails first at $n = 370{,}313$ ($a(n) = -185{,}183$, $\|d(n)\| = 26.5 \ge 25.644219$); `361` violations through $10^7$, peak ratio `1.309077` against $2\ln(n+2)$ at $n = 2{,}010{,}806$ ($|d(n)| = 38.0$). | [`verify_a377090.c`](03-oeis-a377090/verify_a377090.c) · [Disproof](03-oeis-a377090/DISPROOF.md) |
| **B-** | **Anti-Run Constant-Run Lengths** ([OEIS A384890](https://oeis.org/A384890); Gus Wiseman, 2025) | **Proved** | Every constant run has length $1, 2,$ or $3$, via $a(n) = 1 + \operatorname{popcount}(n \mathbin{\&} (n \gg 1))$ ($n \ge 1$) and mod-4/mod-8 carry analysis. | [`WisemanA384890.lean`](04-oeis-a384890/WisemanA384890.lean) · [`verify_a384890.py`](04-oeis-a384890/verify_a384890.py) · [Proof](04-oeis-a384890/PROOF.md) |
| **A** | **Elementary Symmetric Polynomial Lower Bounds** ([MathOverflow #476077](https://mathoverflow.net/questions/476077); Nathaniel Johnston) | **In Progress** | Zero counterexamples across 3-block and Poisson limits ($m \le 25$), 4-block families ($m \le 14$), and 14,400 multi-start optimization runs ($m = 6 \dots 10$). Analytical proof underway. | [`mo476077_search.cpp`](05-mo476077-johnston/cpp/mo476077_search.cpp) · [`verify_mo476077.py`](05-mo476077-johnston/python/verify_mo476077.py) · [Report](05-mo476077-johnston/results/search_report.md) |

## Reproducing All Checks

Requires Lean `v4.36.0` (no Mathlib required), Python 3, and `clang` / `clang++`:

```bash
bash verify_all.sh
```

## Outreach Drafts
Ready-to-send emails and OEIS comment submissions are in [outreach/EMAILS_AND_SUBMISSIONS.md](outreach/EMAILS_AND_SUBMISSIONS.md).
