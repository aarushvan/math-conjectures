# 06. Periodic Points of `{213, 231}`-Avoiding Stack Sorting

Complete proof of Katalin Berlow's Conjecture 5.1 ([arXiv:2008.01164v2](https://arxiv.org/abs/2008.01164)) and Owen Zhang's Conjecture 4.2 ([arXiv:2405.01854](https://arxiv.org/abs/2405.01854)) for $T = \{213, 231\}$ across all $n \ge 1$.

Under the top-to-bottom stack convention and right-greedy push rule, the only periodic points of $s_{\{213, 231\}}$ on $S_n$ are $\mathrm{id}_n$ and $\mathrm{id}_n^r$, reached within at most $3n - 7$ iterations for every $\pi \in S_n$ ($n \ge 3$). *(See [Track 10](../10-berlow-stack-sorting-132-213/) for partial results and $n \le 12$ exhaustion on the separate conjugate pair $\{132, 213\}$ / $\{231, 312\}$.)*

- [Complete proof](PROOF.md)
- [Lean 4 formalization (Lemma 3 `s213_231_last_eq_head` + $S_4, S_5$ checks) 🟡](BerlowStackSorting.lean)
- [Exhaustive $S_3 \dots S_7$ Python verifier](verify_berlow.py)

Run `lean BerlowStackSorting.lean && python3 verify_berlow.py`.
