# Proof of Gus Wiseman's Möbius Identity on OEIS A383093

- **Source:** Gus Wiseman, [OEIS A383093](https://oeis.org/A383093) (2025; offset 0 with $a(0) = 1$) and [OEIS A323774](https://oeis.org/A323774) ($F(n) = \sum_{s \mid n} \binom{n/s + \tau(s) - 1}{n/s}$ for $n \ge 1$).
- **Conjecture:** Let $a(n)$ count integer partitions of $n$ that can be partitioned into constant blocks with a common sum. Then for all $n \ge 1$,
  $$\sum_{d \mid n} a(d) = \mathrm{A323774}(n) = \sum_{s \mid n} \binom{n/s + \tau(s) - 1}{n/s},$$
  i.e., $a$ is the Dirichlet / Möbius transform inverse of $\mathrm{A323774}$ on $\mathbb{Z}_{\ge 1}$.
- **Status:** **Proved** for all $n \ge 1$ via an explicit mutually inverse multiplicity-scaling bijection.
- **Verifier:** [`verify_a383093.py`](verify_a383093.py) (exact check against live OEIS A383093 and A323774 terms for $n = 0 \dots 24$).

---

## Proof

Write a nonempty integer partition $\lambda \vdash d$ ($d \ge 1$) in frequency form as distinct parts $x_1, \dots, x_k \ge 1$ with positive multiplicities $c_1, \dots, c_k \ge 1$ ($\sum_{i=1}^k c_i x_i = d$). Define
$$L(\lambda) := \operatorname{lcm}(x_1, \dots, x_k), \qquad G(\lambda) := \gcd(c_1 x_1, \dots, c_k x_k).$$

Partitioning $\lambda$ into constant blocks all having a common sum $s \ge 1$ means choosing positive integer block sizes dividing each multiplicity such that every block of value $x_i$ sums to $s$: equivalently, $x_i \mid s$ and $s \mid c_i x_i$ for every $1 \le i \le k$ (the block count of $x_i$-blocks is then $c_i x_i / s$, each of size $s / x_i$). Thus a common sum $s$ works for $\lambda$ if and only if
$$L(\lambda) \mid s \mid G(\lambda).$$
Let $\mathcal{A}(d) := \{\lambda \vdash d : L(\lambda) \mid G(\lambda)\}$, so $|\mathcal{A}(d)| = a(d)$ for every $d \ge 1$. On the other hand, define
$$\mathcal{F}(n) := \{ (\lambda, s) : \lambda \vdash n,\; L(\lambda) \mid s \mid G(\lambda) \}.$$
For any fixed divisor $s \mid n$, choosing a partition $\lambda \vdash n$ that admits a constant-block decomposition of common sum $s$ is the same as choosing a multiset of $n/s$ constant blocks, each summing to $s$. Since a constant block summing to $s$ is uniquely determined by its part size (a positive divisor of $s$, of which there are $\tau(s)$), and each multiset of $n/s$ constant blocks merges uniquely by summing multiplicities per part size back into $(\lambda, s)$ (note $s \mid c_i x_i$ for every present part $x_i$ ensures $s \mid G(\lambda)$, and each chosen part divides $s$ so $L(\lambda) \mid s$), we have
$$|\mathcal{F}(n)| = \sum_{s \mid n} \binom{n/s + \tau(s) - 1}{n/s} = \mathrm{A323774}(n).$$

We construct mutually inverse bijections $\Phi : \mathcal{F}(n) \to \bigsqcup_{d \mid n} \mathcal{A}(d)$ and $\Psi : \bigsqcup_{d \mid n} \mathcal{A}(d) \to \mathcal{F}(n)$:

- **Map $\Phi(\lambda, s)$:** Let $g := G(\lambda) / s \in \mathbb{Z}_{\ge 1}$. Since $G(\lambda) = \gcd(c_1 x_1, \dots, c_k x_k)$ divides $\sum c_i x_i = n$, we have $g \mid n$; set $d := n / g \mid n$. For each $1 \le i \le k$, write $c_i x_i / s = g \cdot b_i$ where $b_i = (c_i x_i) / G(\lambda) \in \mathbb{Z}_{\ge 1}$. Since $x_i \mid s$, let $q_i := s / x_i \in \mathbb{Z}_{\ge 1}$, so $c_i = g \cdot (b_i q_i)$ is divisible by $g$. Define $\lambda' \vdash d$ with the same distinct parts $x_1, \dots, x_k$ and reduced multiplicities $c'_i := c_i / g$. Then $G(\lambda') = G(\lambda) / g = s$ and $L(\lambda') = L(\lambda) \mid s = G(\lambda')$, so $(d, \lambda') \in \bigsqcup_{d \mid n} \mathcal{A}(d)$ with $\Phi(\lambda, s) = (d, \lambda')$.

- **Map $\Psi(d, \lambda')$:** Given $d \mid n$ and $\lambda' \in \mathcal{A}(d)$ with multiplicities $c'_i$, set $g := n / d \in \mathbb{Z}_{\ge 1}$, $s := G(\lambda')$, and $\lambda \vdash n$ with the same distinct parts $x_1, \dots, x_k$ and scaled multiplicities $c_i := g c'_i$. Then $L(\lambda) = L(\lambda') \mid G(\lambda') = s$ and $G(\lambda) = g G(\lambda') = g s$, so $s \mid G(\lambda)$ and $(\lambda, s) \in \mathcal{F}(n)$ with $\Psi(d, \lambda') = (\lambda, s)$.

Because $G(\lambda) / s = g = n / d$ in both directions, $\Psi(\Phi(\lambda, s)) = (\lambda, s)$ and $\Phi(\Psi(d, \lambda')) = (d, \lambda')$. Thus $|\mathcal{F}(n)| = \sum_{d \mid n} |\mathcal{A}(d)|$, proving $\sum_{d \mid n} a(d) = \sum_{s \mid n} \binom{n/s + \tau(s) - 1}{n/s}$ for all $n \ge 1$. $\square$
