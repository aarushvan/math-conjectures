# Proof of Conjecture 1 of Grytczuk, Pawlik & Pleszczynski (`arXiv:2308.13882v2`)

- **Source:** Jaroslaw Grytczuk, Bartlomiej Pawlik, and Mariusz Pleszczynski, *Variations on shuffle squares* ([arXiv:2308.13882v2](https://arxiv.org/abs/2308.13882v2), Section 2.2, Conjecture 1).
- **Conjecture 1:** *There exists a shuffle anti-square of length $2n$ for every $n \ge 12$.*
- **Status:** **Completely Proved** for all integers $n \ge 12$ using a single explicit one-parameter family. Together with [Track 01](../01-dihedral-shuffle-squares/PROOF.md) (which disproves Conjecture 2 for all $2n \ge 8$), both Conjecture 1 and Conjecture 2 of `arXiv:2308.13882v2` are now completely resolved.
- **Verifier:** [`verify_antisquares.py`](verify_antisquares.py) (verifies the DP oracle against brute-force partitions up to length $10$, checks every cyclic shift of $W_n$ directly for $n = 12 \dots 45$, and extracts and verifies in exact integer arithmetic all $568$ Farkas dual certificates proving $W_n$ is a shuffle anti-square for every $n \ge 12$).

---

## Definitions and Explicit Family

An even binary word $W \in \{0, 1\}^{2n}$ (even number of $0$s and $1$s) is a **shuffle square** if its index set $\{1, \dots, 2n\}$ can be partitioned into two disjoint subsets $I \sqcup J$ such that the subsequences $W|_I$ and $W|_J$ are identical strings. A word $W$ is a **shuffle anti-square** if none of its cyclic shifts $\sigma^s(W)$ ($0 \le s < 2n$) is a shuffle square.

For every integer $n \ge 12$, set $t := n - 12 \ge 0$ and define the explicit binary word of length $2n$ (containing $12$ ones and $2n - 12$ zeros):
$$W_n := \mathtt{0}^{n-7}\, \mathtt{1}\, \mathtt{0}^2\, \mathtt{1}^4\, \mathtt{0}^{n-8}\, \mathtt{1}^3\, \mathtt{0}\, \mathtt{1}^4.$$
At $n = 12$ ($t = 0$), $W_{12} = \mathtt{000001001111000011101111}$ is the paper's own Appendix A length-24 shuffle anti-square.

---

## Theorem

For every integer $n \ge 12$, $W_n$ is a binary shuffle anti-square of length $2n$.

---

## Proof

Write $t = n - 12 \ge 0$, so $W_n$ consists of $8$ cyclic blocks:
$$B = \big(\mathtt{0}^{5+t},\; \mathtt{1}^1,\; \mathtt{0}^2,\; \mathtt{1}^4,\; \mathtt{0}^{4+t},\; \mathtt{1}^3,\; \mathtt{0}^1,\; \mathtt{1}^4\big).$$
Suppose for contradiction that some cyclic shift $S = \sigma^s(W_n)$ ($0 \le s < 2n$) admits a shuffle-square partition $(U, V)$ with $U = V \in \{0, 1\}^n$. Because $W_n$ has $12$ ones, $U$ and $V$ must each receive $6$ ones and $n - 6$ zeros.

### 1. Twelve Exhaustive Cyclic Cut Templates
Cutting the cyclic word $W_n$ at index $s$ falls into one of $12$ exhaustive structural templates (noting that splitting the length-$1$ block $\mathtt{1}^1$ or $\mathtt{0}^1$ at its boundary is already covered by adjacent blocks):
- **$4$ zero-run cuts** (`cutZ_0..cutZ_3`): splitting one of the four zero-runs $Z_a$ ($a \in \{0, 1, 2, 3\}$) of parametric length $L_a(t) = c_a + d_a t$ into a tail prefix of length $z_{\text{tail}} \ge 0$ at the start of $S$ and a head suffix of length $z_{\text{head}} \ge 0$ at the end of $S$ ($z_{\text{tail}} + z_{\text{head}} = L_a(t)$). This gives $5$ zero-runs $Z'_0, \dots, Z'_4$ interleaved with $4$ one-runs of lengths $o_0, o_1, o_2, o_3$ ($\sum o_i = 12$).
- **$8$ interior one-run cuts** (`cutO`): splitting one of the three multi-one runs ($\mathtt{1}^4, \mathtt{1}^3, \mathtt{1}^4$) into $(p, o - p)$ for $1 \le p \le o - 1$ ($3 + 2 + 3 = 8$ templates). This gives $4$ zero-runs $Z'_0, \dots, Z'_3$ interleaved with $5$ one-runs of lengths $o_0, \dots, o_4$ ($\sum o_i = 12$).

### 2. Run-Level Flow Reduction
In a fixed template with $m \in \{4, 5\}$ one-runs of lengths $o_0, \dots, o_{m-1}$ and $nz \in \{4, 5\}$ zero-runs:
- Let $k_i \in \{0, \dots, o_i\}$ be the number of ones assigned to $U$ from the $i$-th one-run (leaving $o_i - k_i$ ones to $V$), with $\sum_{i=0}^{m-1} k_i = 6$. Enumerating all tuples $(k_0, \dots, k_{m-1})$ across the $12$ templates yields exactly **$568$ valid $(template, \mathbf{k})$ pairs**.
- Let $x_j \ge 0$ and $y_j \ge 0$ be the numbers of zeros assigned to $U$ and $V$ respectively from the $j$-th zero-run ($0 \le j < nz$).

For $U$ and $V$ to be identical binary strings of length $n$ containing $6$ ones, two sets of linear equality constraints must hold over the nonnegative real variables $(t, x_0, \dots, x_{nz-1}, y_0, \dots, y_{nz-1}) \ge 0$:
1. **Four zero-run length equations:**
   - For each uncut zero-run of parametric length $c + d \cdot t$, $x_j + y_j - d \cdot t = c$.
   - For a cut zero-run (zero-run cuts only), $x_0 + y_0 + x_4 + y_4 - d \cdot t = c$.
2. **Seven gap-balance equations ($0 \le r \le 6$):**
   Every zero in $U$ is preceded by a fixed count $u_j = \sum_{i < \text{pos}(j)} k_i \in \{0, \dots, 6\}$ of ones in $U$, and every zero in $V$ is preceded by $v_j = \sum_{i < \text{pos}(j)} (o_i - k_i) \in \{0, \dots, 6\}$ ones in $V$. Equality $U = V$ requires identical zero-run lengths between consecutive ones at every rank $r \in \{0, \dots, 6\}$:
   $$\sum_{u_j = r} x_j - \sum_{v_j = r} y_j = 0 \qquad (0 \le r \le 6).$$

### 3. Universal Infeasibility via $568$ Exact Farkas Dual Certificates
For every one of the $568$ linear systems $A \mathbf{v} = \mathbf{b}$ ($\mathbf{v} \ge 0$, where $\mathbf{v} = (t, x_0, \dots, y_{nz-1})$), [`verify_antisquares.py`](verify_antisquares.py) computes via exact rational Phase-I Simplex and clears denominators to extract an integer dual vector $\mathbf{d} \in \{-1, 0, 1\}^{11}$ satisfying
$$\mathbf{d}^T A \ge \mathbf{0} \qquad \text{and} \qquad \mathbf{d}^T \mathbf{b} < 0.$$
Therefore no nonnegative real solution $(t, \mathbf{x}, \mathbf{y}) \ge 0$ exists for any $t \ge 0$ in any of the $568$ cases:
$$0 \le \mathbf{d}^T A \mathbf{v} = \mathbf{d}^T \mathbf{b} < 0,$$
a contradiction. Thus no cyclic shift of $W_n$ is a shuffle square for any $n \ge 12$. $\blacksquare$
