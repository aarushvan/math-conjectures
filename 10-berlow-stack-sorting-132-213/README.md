# 10. Periodic Points of `{132, 213}`-Avoiding Stack Sorting

Verified partial resolution and structural reduction for the remaining half $T = \{132, 213\}$ (conjugate to $\{231, 312\}$) of Berlow's Conjecture 5.1 ([arXiv:2008.01164v2](https://arxiv.org/abs/2008.01164)) and Zhang's Conjecture 4.2 ([arXiv:2405.01854](https://arxiv.org/abs/2405.01854)). *(See [Track 06](../06-berlow-stack-sorting/) for our complete all-$n$ proof for $T = \{213, 231\}$.)*

Proved for all $n \ge 1$: binary-weight descent forcing every orbit to hit $1$-first and $n$-first permutations infinitely often ($f(n\rho) = s_{21}(\rho)n$), first-return reduction $R_n$ on $S_{n-1}$, exclusion of periods $1, 2, 3$, and exhaustive computational verification through $n = 12$ (`578,290` distinct classical images at $n = 12$). Any counterexample requires $n \ge 13$ and least period $\ge 4$.

- [Partial proof and reduction note](PARTIAL_PROOF.md)
- [Exhaustive Python verifier (`--through-12`) ⬜](verify_berlow_132_213.py)

Run `python3 verify_berlow_132_213.py --through-12`.
