# Partial Proof, Exact Construction ($n = 4$), and Search: Phan's Three-Layer Lattice Conjecture (MO #507835)

- **Source:** Veronica Phan, *A conjecture related to Erdos Problem 86*, [MathOverflow #507835](https://mathoverflow.net/questions/507835).
- **Conjecture:** In the infinite $3$-layer lattice between outer layers $\{-1, +1\} \times \mathbb{Z}^{n-1}$ and middle layer $\{0\} \times \mathbb{Z}^{n-1}$ (where outer site $a$ connects to $a \pm e_i$ modulo the sum layer), the maximum edge density of a $C_4$-free subgraph is bounded asymptotically by $\frac{1}{2} + \frac{1}{2\sqrt{n}}$.
- **Scope & Status:** **Proved for $n = 2, 3, 4$; Open for $n \ge 5$.**
  1. **Universal $4$-cycle counting upper bound (all $n \ge 2$):** Proved maximum asymptotic $C_4$-free edge density is $\le 3/4$ for every $n \ge 2$. Since $\frac{1}{2} + \frac{1}{2\sqrt{n}} \ge 3/4$ iff $n \le 4$, this **proves Phan's upper bound completely for $n = 2, 3, 4$**.
  2. **Exact optimal $n = 4$ construction:** Explicit $\mathbb{F}_2^2$-parity edge-deletion pattern attaining exact $C_4$-free density $3/4$ on the infinite $n = 4$ lattice and every even-period quotient ($M$ even).
  3. **Computational periodic lower bounds & GPU notebook:** Verified $C_4$-free quotients via [`phan_periodic.py`](phan_periodic.py), plus GPU PyTorch annealing notebook [`colab_phan_gpu.ipynb`](colab_phan_gpu.ipynb) targeting $n = 5$ (where the target $\frac{1}{2} + \frac{1}{2\sqrt{5}} \approx 0.723607$ drops below the $3/4$ counting ceiling).

---

## 1. Universal $3/4$ Counting Upper Bound (Settles $n = 2, 3, 4$)

On the periodic quotient modulo $M \ge 3$ with $S := M^{n-1}$ outer sites per layer, there are $2 n S$ total edges. Every $4$-cycle uses opposite outer layers (same-layer outer vertices share at most one middle neighbor) and is uniquely determined by its lower outer site $a$ and coordinate pair $\{i < j\}$ (with upper outer site $a + e_i + e_j$). Because every component of a $4$-step closed-layer walk has displacement in $\{-2, -1, 0, 1, 2\}$, reducing modulo $M \ge 3$ introduces zero spurious $4$-cycles.

There are $\binom{n}{2} S$ distinct $4$-cycles, and each edge lies in exactly $n - 1$ of them. Deleting at least one edge per $4$-cycle therefore requires deleting at least
$$\frac{\binom{n}{2} S}{n - 1} = \frac{n S}{2}$$
edges out of $2 n S$ total edges, yielding an upper bound on kept edges of $\le \frac{3}{4} (2 n S)$, i.e., **edge density $\le 3/4$**. In the finite-box formulation $[-N, N]^{n-1}$, only an $O(N^{n-2})$ boundary layer can lack pairs, so the asymptotic density bound $3/4$ holds there as well. Since $\frac{1}{2} + \frac{1}{2\sqrt{n}} \ge \frac{3}{4}$ for $n \in \{2, 3, 4\}$ (strict equality at $n = 4$), Phan's bound holds rigorously for $n = 2, 3, 4$.

---

## 2. Exact $3/4$ Parity Construction for $n = 4$

Label the four directions $(e_1, e_2, e_3, e_4)$ by $(01, 10, 11, 00) \in \mathbb{F}_2^2$. Let $A : \mathbb{F}_2^2 \to \mathbb{F}_2^2$ fix $00$ and cyclically permute the three nonzero vectors $01 \mapsto 10 \mapsto 11 \mapsto 01$. At every lower or upper outer site $a \in \mathbb{Z}^3$ (identifying $e_4 = 0$ in reduced coordinates), delete the single edge whose direction label equals
$$r(a) := A\!\left(\sum_{k=1}^3 (a_k \bmod 2)\,\operatorname{label}(e_k)\right) \in \mathbb{F}_2^2.$$
In any $4$-cycle spanned by directions $\{i < j\}$, the upper site $b$ differs from the lower site $a$ in residue by $\operatorname{label}(e_i) + \operatorname{label}(e_j) \ne 00$, so $r(b) - r(a) = A(\operatorname{label}(e_i) + \operatorname{label}(e_j)) \notin \{00, \operatorname{label}(e_i) + \operatorname{label}(e_j)\}$. Wait directly on $2$-element subsets of $\mathbb{F}_2^2$: translating $\{u, v\}$ by a third nonzero element $w \notin \{0, u+v\}$ swaps $\{u, v\}$ with its $2$-element complement in $\mathbb{F}_2^2$! Hence exactly one of $r(a), r(b)$ lies in $\{\operatorname{label}(e_i), \operatorname{label}(e_j)\}$, deleting an edge of every $4$-cycle while keeping exact density $3/4$ on the infinite $n = 4$ lattice and every even-period quotient.

---

## 3. Periodic Search Verification (`phan_periodic.py`)

| $n$ | Period $M$ | Best Kept / Total Edges | Density | Counting Upper | Conjectured $\frac{1}{2} + \frac{1}{2\sqrt{n}}$ | Note |
| ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| $2$ | $3, 4, 6$ | $9/12$, $12/16$, $18/24$ | $0.750000$ | $0.750000$ | $0.853553$ | Optimal |
| $3$ | $3, 4$ | $40/54$, $72/96$ | $0.740741$, $0.750000$ | $0.740741$, $0.750000$ | $0.788675$ | Optimal |
| $4$ | $4, 6$ | $384/512$, $1{,}296/1{,}728$ | $0.750000$ | $0.750000$ | $0.750000$ | Exact parity construction |
| $5$ | $3, 4$ | $569/810$, $1{,}769/2{,}560$ | $0.702469$, $0.691016$ | $0.750000$ | $0.723607$ | Exploratory lower bound ([`colab_phan_gpu.ipynb`](colab_phan_gpu.ipynb) targets larger $n=5$ searches) |
