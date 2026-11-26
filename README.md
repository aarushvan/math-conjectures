# Machine-Verified Proofs, Disproofs & Formalizations for Open Conjectures

Independently audited mathematical proofs, counterexamples, and zero-dependency Lean 4 formalizations (`leanprover/lean4:v4.36.0`) across combinatorics, algebra, and number theory. Every resolution listed below has been line-by-line refereed, matched against live primary sources (MathOverflow, arXiv, OEIS), and verified end-to-end by [`verify_all.sh`](verify_all.sh).

## Headline Resolutions (Papers & MathOverflow)

| Tier | Problem & Primary Source | Verdict | Key Result | Formal / Verifier |
| :---: | :--- | :--- | :--- | :--- |
| **S+** | **Elementary Symmetric Polynomial Lower Bounds** ([MathOverflow #476077](https://mathoverflow.net/questions/476077/bounding-elementary-symmetric-polynomials-away-from-zero); Nathaniel Johnston, Jul 2024, 0 answers) | **Proved (All $2 \le m \le n$)** | Proved $e_k(x) \ge \binom{m-1}{k}/(m-1)^k$ for all $2 \le m \le n$, $1 \le k < m$, and arbitrary-sign reals $x \in \mathbb{R}^n$, with unique equality characterization ($2 \le k < m$), via Hermite-Biehler/Gauss-Lucas root interlacing dropping, Newton inequalities, and a 3-variable cubic perturbation; plus zero-calculus ring identities for $m = 3, 4, 5$. | [Proof](05-mo476077-johnston/PROOF.md) · [`JohnstonEsymmM345.lean`](05-mo476077-johnston/JohnstonEsymmM345.lean) · [`verify_identities_m345.py`](05-mo476077-johnston/python/verify_identities_m345.py) · [`mo476077_search.cpp`](05-mo476077-johnston/cpp/mo476077_search.cpp) |
| **S** | **Periodic Points of $\{213, 231\}$-Avoiding Stack Sorting** (Katalin Berlow, [arXiv:2008.01164v2](https://arxiv.org/abs/2008.01164), Conj. 5.1 / Owen Zhang, [arXiv:2405.01854](https://arxiv.org/abs/2405.01854), Conj. 4.2) | **Proved (All $n \ge 1$)** | Proved that $\mathrm{id}_n$ and $\mathrm{id}_n^r$ are the only periodic points of $s_{\{213, 231\}}$ on $S_n$ (top-to-bottom stack convention), with explicit convergence bound $\le 3n - 7$ ($n \ge 3$) via extreme-only pop characterization, $\mathrm{Bad}(f(\pi)) \subseteq \mathrm{Bad}(\pi)$, and bottom-of-stack elimination. (The conjugate pair $\{132, 213\}$ / $\{231, 312\}$ is separate.) | [Proof](06-berlow-stack-sorting/PROOF.md) · [`BerlowStackSorting.lean`](06-berlow-stack-sorting/BerlowStackSorting.lean) · [`verify_berlow.py`](06-berlow-stack-sorting/verify_berlow.py) |
| **S** | **Binary Shuffle Anti-Squares** ([arXiv:2308.13882v2](https://arxiv.org/abs/2308.13882v2), Conj. 1; Grytczuk, Pawlik & Pleszczynski) | **Proved (All $n \ge 12$)** | Proved existence of a binary shuffle anti-square of length $2n$ for every $n \ge 12$ via the explicit family $W_n = \mathtt{0}^{n-7}\mathtt{10}^2\mathtt{1}^4\mathtt{0}^{n-8}\mathtt{1}^3\mathtt{01}^4$, reducing all cyclic shifts to 568 linear flow systems all certified infeasible by exact integer Farkas duals in $\{-1,0,1\}^{11}$. | [Proof](09-shuffle-antisquares/PROOF.md) · [`verify_antisquares.py`](09-shuffle-antisquares/verify_antisquares.py) |
| **S** | **Dihedral Shuffle Squares for Ternary Words** ([arXiv:2308.13882v2](https://arxiv.org/abs/2308.13882v2), Conj. 2; Grytczuk, Pawlik & Pleszczynski) | **Disproved (All $2n \ge 8$)** | False for all even lengths $2n \ge 8$. Minimal counterexample `00011022` (the unique $S_3 \times D_8$ orbit of all 48 length-8 counterexamples) and infinite family $W_n = \mathtt{0}^{2n-5}\mathtt{11022}$ ($n \ge 4$) via cyclic adjacent-$\mathtt{00}$ invariance under $D_n$. | [Proof](01-dihedral-shuffle-squares/PROOF.md) · [`DihedralShuffleDisproof.lean`](01-dihedral-shuffle-squares/DihedralShuffleDisproof.lean) · [`verify_dihedral.py`](01-dihedral-shuffle-squares/verify_dihedral.py) |

## OEIS Conjecture Resolutions

| Tier | Problem & Source | Verdict | Key Result | Formal / Verifier |
| :---: | :--- | :--- | :--- | :--- |
| **B+** | **Constant-Block vs. Distinct Run-Sum Partitions** ([OEIS A382427](https://oeis.org/A382427) / [A381717](https://oeis.org/A381717); Gus Wiseman, 2025) | **Proved** | Exact equivalence for all integer partitions via minimum-block Pigeonhole merge and forbidden-head inductive interleaving. | [Proof](02-oeis-a382427-a381717/PROOF.md) · [`WisemanA382427.lean`](02-oeis-a382427-a381717/WisemanA382427.lean) · [`verify_a382427.py`](02-oeis-a382427-a381717/verify_a382427.py) |
| **B** | **Prime-Difference Greedy Deviation Bound** ([OEIS A377090](https://oeis.org/A377090); M. F. Hasler, Feb 2025) | **Disproved** | $\bigl\|\|a(n)\| - n/2\bigr\| < 2\ln(n+2)$ fails first at $n = 370{,}313$ ($a(n) = -185{,}183$, $\|d(n)\| = 26.5 \ge 25.644219$); `361` violations through $10^7$, peak ratio `1.309077` against $2\ln(n+2) = 29.028094$ at $n = 2{,}010{,}806$ ($|d(n)| = 38.0$), max $|d(n)| = 39.0$ at $n = 4{,}652{,}436$. | [Disproof](03-oeis-a377090/DISPROOF.md) · [`verify_a377090.c`](03-oeis-a377090/verify_a377090.c) |
| **B** | **Disjoint Strict-Partition Families** ([OEIS A384350](https://oeis.org/A384350); Gus Wiseman, 2025) | **Proved** | Exact subset-by-subset equivalence for every $S \subseteq \{1,\dots,n\}$ via minimum non-trivial element argument; exhaustively checked against live OEIS terms for $n = 0 \dots 11$. | [Proof](07-oeis-a384350/PROOF.md) · [`verify_a384350.py`](07-oeis-a384350/verify_a384350.py) |
| **B** | **Common-Sum Block Partitions Mobius Identity** ([OEIS A383093](https://oeis.org/A383093) / [A323774](https://oeis.org/A323774); Gus Wiseman, 2025) | **Proved** | Proved $\sum_{d \mid n} a(d) = \sum_{s \mid n} \binom{n/s + \tau(s) - 1}{n/s}$ for all $n \ge 1$ via mutually inverse multiplicity-scaling bijections $\Phi, \Psi$; checked against live OEIS A383093 ($n = 0 \dots 24$) and A323774. | [Proof](08-oeis-a383093/PROOF.md) · [`verify_a383093.py`](08-oeis-a383093/verify_a383093.py) |
| **B-** | **Anti-Run Constant-Run Lengths** ([OEIS A384890](https://oeis.org/A384890); Gus Wiseman, 2025) | **Proved** | Every constant run has length $1, 2,$ or $3$, via $a(n) = 1 + \operatorname{popcount}(n \mathbin{\&} (n \gg 1))$ ($n \ge 1$) and mod-4/mod-8 carry analysis. | [Proof](04-oeis-a384890/PROOF.md) · [`WisemanA384890.lean`](04-oeis-a384890/WisemanA384890.lean) · [`verify_a384890.py`](04-oeis-a384890/verify_a384890.py) |

## Reproducing All Checks

Requires Lean `leanprover/lean4:v4.36.0` (zero external dependencies, no Mathlib download required), Python 3 (stdlib only, Python 3.9+ compatible), and `clang` / `clang++`:

```bash
bash verify_all.sh
```

## Outreach Drafts
Ready-to-post answers, emails to authors, and OEIS comment submissions are in [`outreach/EMAILS_AND_SUBMISSIONS.md`](outreach/EMAILS_AND_SUBMISSIONS.md).
