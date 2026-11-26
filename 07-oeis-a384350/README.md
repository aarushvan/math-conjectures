# 07. Disjoint Strict-Partition Families

Complete proof of Gus Wiseman's 2025 conjecture on [OEIS A384350](https://oeis.org/A384350) (cf. [A179009](https://oeis.org/A179009)) for every subset $S \subseteq \{1, \dots, n\}$ and all $n \ge 0$.

Any non-trivial pairwise disjoint family of strict integer partitions $\{P_x : x \in S\}$ satisfies $P_{x_0} \subseteq \{1, \dots, n\} \setminus S$ at $x_0 = \min\{x \in S : P_x \ne \{x\}\}$, proving subset-by-subset equivalence with elements summing distinct non-elements.

- [Complete proof](PROOF.md)
- [Exhaustive Python verifier ($n \le 11$, live OEIS match) ⬜](verify_a384350.py)

Run `python3 verify_a384350.py`.
