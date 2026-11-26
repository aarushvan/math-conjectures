# Disproof of Conjecture 2 in "Variations on Shuffle Squares" (arXiv:2308.13882v2)

**Authors of the conjecture:** Jarosław Grytczuk, Bartłomiej Pawlik, and Mariusz Pleszczyński, *Variations on shuffle squares*, [arXiv:2308.13882v2](https://arxiv.org/abs/2308.13882v2) (June 30, 2024), Section 2.3.

## Conjecture Statement
An *even word* over $\{0, 1, 2\}$ is a word in which each letter occurs an even number of times.
For $n \ge 1$, two words $U, V$ of length $n$ are $\gamma$-similar if $V = \gamma(U)$ or $U = \gamma(V)$, where $\gamma(U) = u_{\gamma_0} u_{\gamma_1} \cdots u_{\gamma_{n-1}}$ (0-indexed). A word $W$ of length $2n$ is a *dihedral shuffle square* if it can be partitioned into two disjoint subwords $U, V$ of length $n$ that are $\gamma$-similar for some $\gamma \in D_n$ (rotations $i \mapsto (i+k) \bmod n$ and reflections $i \mapsto (k-i) \bmod n$).

> **Conjecture 2 (arXiv:2308.13882v2):** Every even ternary word is a shuffle $\gamma$-square for a dihedral permutation $\gamma \in D_n$.

## Counterexample and Infinite Family

**Verdict:** False for every even length $2n \ge 8$ ($n \ge 4$).

- **Minimal counterexample ($n = 4$, length $8$):**
  $$W_4 = \mathtt{00011022}.$$
- **Infinite family ($n \ge 4$, length $2n$):**
  $$W_n = \mathtt{0}^{2n-5}\mathtt{11022}.$$

Clearly $W_n$ has length $2n$, with counts $\#_0(W_n) = 2n-4$, $\#_1(W_n) = 2$, $\#_2(W_n) = 2$, so $W_n$ is an even ternary word.

## Proof

Assume for contradiction that $W_n$ splits into two disjoint subwords $U, V$ of length $n$ with $V = \gamma(U)$ or $U = \gamma(V)$ for some $\gamma \in D_n$.

1. **Equal letter counts:** Every permutation $\gamma \in D_n$ preserves letter multiplicities, so $U$ and $V$ each contain exactly $n-2$ copies of $\mathtt{0}$, one $\mathtt{1}$, and one $\mathtt{2}$.
2. **Forced subwords:** In $W_n = \mathtt{0}^{2n-5}\mathtt{11022}$, the prefix $\mathtt{0}^{2n-5}$ consists entirely of $\mathtt{0}$s, the $\mathtt{1}$s appear before the isolated $\mathtt{0}$ at index $2n-3$, and the $\mathtt{2}$s appear after it. Since each of $U, V$ receives exactly one $\mathtt{1}$ and one $\mathtt{2}$, the isolated $\mathtt{0}$ goes to either $U$ or $V$.
   - If the isolated $\mathtt{0}$ goes to $U$, then $U$ ends in $\mathtt{102}$ and $V$ ends in $\mathtt{12}$. Because $|U| = |V| = n$, the remaining $n-3$ (resp. $n-2$) characters from the prefix $\mathtt{0}^{2n-5}$ force
     $$U = \mathtt{0}^{n-3}\mathtt{102}, \qquad V = \mathtt{0}^{n-2}\mathtt{12}.$$
   - If the isolated $\mathtt{0}$ goes to $V$, the exact roles of $U$ and $V$ swap.
3. **Dihedral invariant:** Define the number of cyclic adjacent $\mathtt{00}$ pairs in a length-$n$ word $X$ by
   $$c(X) = \#\bigl\{i \in \{0, \dots, n-1\} : x_i = \mathtt{0} \text{ and } x_{(i+1) \bmod n} = \mathtt{0}\bigr\}.$$
   Viewing indices $0, \dots, n-1$ as vertices of a regular $n$-gon, rotations preserve cyclic order $(i, i+1)$ and reflections reverse cyclic order $(i, i+1) \mapsto (\sigma(i)+1, \sigma(i))$. Hence $c(\gamma(X)) = c(X)$ for every $\gamma \in D_n$.
4. **Contradiction:**
   - In $\mathtt{0}^{n-2}\mathtt{12}$, the $\mathtt{0}$s form a single contiguous run of $n-2$ vertices, giving $c(\mathtt{0}^{n-2}\mathtt{12}) = n - 3$.
   - In $\mathtt{0}^{n-3}\mathtt{102}$, the $\mathtt{0}$s split into a run of length $n-3$ and an isolated $\mathtt{0}$, giving $c(\mathtt{0}^{n-3}\mathtt{102}) = n - 4$.
   Since $n - 3 \ne n - 4$, no $\gamma \in D_n$ can map one subword to the other. $\blacksquare$

## Computational & Formal Verification
- **Lean 4 kernel check:** [DihedralShuffleDisproof.lean](DihedralShuffleDisproof.lean) proves `dihedral_conjecture_false` for all $n \ge 4$ and `minimal_counterexample_00011022` with zero external dependencies and zero `sorry`s.
- **Exhaustive Python verification (`verify_dihedral.py`):**
  - $n = 3$ (length $6$): `90` even 3-letter ternary words checked; **0** counterexamples (consistent with $D_3 = S_3$).
  - $n = 4$ (length $8$): `1260` even 3-letter ternary words checked; **48** counterexamples, forming **1** single canonical orbit under $S_3 \times D_8$ represented by `00011022`.
  - $W_n$ explicitly verified false for $n = 4, 5, 6, 7, 8$.
