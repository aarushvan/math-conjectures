# Proof of Gus Wiseman's Conjecture on OEIS A384350

- **Source:** Gus Wiseman, [OEIS A384350](https://oeis.org/A384350) (2025; cf. [OEIS A179009](https://oeis.org/A179009)).
- **Conjecture:** *The number of subsets $S \subseteq \{1,\dots,n\}$ containing at least one element that is a sum of distinct non-elements equals the number of subsets $S \subseteq \{1,\dots,n\}$ such that it is possible in more than one way to choose a disjoint family of strict integer partitions, one of each element.*
- **Status:** **Proved** (exact subset-by-subset equivalence for every $S \subseteq \{1,\dots,n\}$ and all $n \ge 0$).
- **Verifier:** [`verify_a384350.py`](verify_a384350.py) (exhaustive subset-by-subset verification for $n = 0 \dots 11$, matched against live OEIS A384350 terms).

---

## Proof

Fix any $n \ge 0$ and any subset $S \subseteq \{1, \dots, n\}$. If $S = \emptyset$, there are $0$ elements to express (so no element of $S$ is a sum of distinct non-elements) and only $1$ empty family of partitions (not more than one). Assume henceforth that $S \neq \emptyset$.

For every $S \subseteq \{1, \dots, n\}$, assigning the singleton strict partition $P_x = \{x\}$ to each $x \in S$ gives a valid pairwise disjoint family of strict integer partitions, and distinct elements $x \neq x'$ receive distinct partitions $P_x \neq P_{x'}$. Therefore, admitting more than one pairwise disjoint family of strict integer partitions (one for each element of $S$) is equivalent to the existence of at least one **non-trivial** pairwise disjoint family $\{P_x : x \in S\}$, i.e., one with $P_x \neq \{x\}$ for some $x \in S$.

- **($\Rightarrow$):** Suppose some $x \in S$ equals the sum of distinct elements $y_1, \dots, y_k \in \{1, \dots, n\} \setminus S$. Since $x \in S$ and each $y_j \notin S$, we cannot have $k = 1$ (nor $k = 0$ since $x \ge 1$), so $k \ge 2$ and $P_x := \{y_1, \dots, y_k\} \neq \{x\}$ is a strict partition of $x$ disjoint from $S$. Setting $P_z := \{z\}$ for every $z \in S \setminus \{x\}$ yields a non-trivial pairwise disjoint family of strict partitions for $S$.

- **($\Leftarrow$):** Suppose $\{P_x : x \in S\}$ is a non-trivial pairwise disjoint family of strict integer partitions ($\sum_{y \in P_x} y = x$, parts distinct positive integers, $P_x \cap P_{x'} = \emptyset$ for $x \neq x'$). Let
  $$T := \{ x \in S : P_x \neq \{x\} \} \neq \emptyset, \qquad x_0 := \min(T).$$
  Because $P_{x_0} \neq \{x_0\}$ and $P_{x_0}$ is a partition of $x_0$ into positive integers, every part $y \in P_{x_0}$ satisfies $1 \le y < x_0 \le n$. If any $y \in P_{x_0}$ belonged to $S$, then $y < x_0 = \min(T)$ would force $y \notin T$, hence $P_y = \{y\}$, giving $y \in P_y \cap P_{x_0}$ with $y \neq x_0$, contradicting pairwise disjointness of $\{P_x : x \in S\}$. Consequently $P_{x_0} \cap S = \emptyset$, so $P_{x_0} \subseteq \{1, \dots, n\} \setminus S$ writes $x_0 \in S$ as a sum of distinct non-elements. $\square$
