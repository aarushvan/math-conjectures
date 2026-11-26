# 08. Common-Sum Block Partitions Mobius Identity

Complete proof of Gus Wiseman's 2025 Dirichlet / Mobius transform conjecture connecting [OEIS A383093](https://oeis.org/A383093) ($a(0) = 1$, offset $0$) and [OEIS A323774](https://oeis.org/A323774) for all $n \ge 1$.

Explicit mutually inverse multiplicity-scaling bijections $\Phi, \Psi$ pair partitions of $n$ admitting common-sum $s$ constant blocks ($L(\lambda) \mid s \mid G(\lambda)$) with divisors $d \mid n$ and partitions $\lambda' \vdash d$ having $L(\lambda') \mid G(\lambda')$, proving $\sum_{d \mid n} a(d) = \sum_{s \mid n} \binom{n/s + \tau(s) - 1}{n/s}$.

- [Complete proof](PROOF.md)
- [Python verifier ($n \le 24$, live OEIS A383093 / A323774 match) ⬜](verify_a383093.py)

Run `python3 verify_a383093.py`.
