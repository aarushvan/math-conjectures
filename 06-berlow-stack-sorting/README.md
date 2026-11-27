# 06. Periodic Points of `{213, 231}`-Avoiding Stack Sorting

Complete proof of Katalin Berlow's Conjecture 5.1 ([arXiv:2008.01164v2](https://arxiv.org/abs/2008.01164)) and Owen Zhang's Conjecture 4.2 ([arXiv:2405.01854](https://arxiv.org/abs/2405.01854)) for $T = \{213, 231\}$ across all $n \ge 1$.

Under the top-to-bottom stack convention and right-greedy push rule, the only periodic points of $s_{\{213, 231\}}$ on $S_n$ are $\mathrm{id}_n$ and $\mathrm{id}_n^r$, reached within at most $3n - 7$ iterations for every $\pi \in S_n$ ($n \ge 3$). *(See [Track 10](../10-berlow-stack-sorting-132-213/) for partial results and $n \le 12$ exhaustion on the separate conjugate pair $\{132, 213\}$ / $\{231, 312\}$.)*

- [Complete proof](PROOF.md)
- [Lean 4 formalization](BerlowStackSorting.lean) (full all-$n$ proof, zero `sorryAx`) ✅
- [Exhaustive Python verifier](verify_berlow.py) ($S_3 \dots S_7$)
- [Statement Audit](../docs/STATEMENT_AUDIT.md#track-06-periodic-points-of-213-231-avoiding-stack-sorting)

Run `lean BerlowStackSorting.lean && python3 verify_berlow.py`.

## Statement Audit

Maps Berlow's top-to-bottom literal `{213, 231}`-avoiding stack transition (`hasPairBetween` / `has213or231` / `s213_231_literal` / `iterSortLit`) and proves its exact equivalence (`s213_231_literal_eq`) with `min(S) < x < max(S)`, then proves `berlow_convergence_3n_minus_7` ($n \ge 3$) and `berlow_conjecture_5_1_213_231` ($n \ge 1, p \ge 1$) over `IsPerm n π`.
