# Complete Proof of Nathaniel Johnston's Conjecture (MathOverflow #476077)

- **Source:** Nathaniel Johnston, *Bounding elementary symmetric polynomials away from zero*, [MathOverflow #476077](https://mathoverflow.net/questions/476077/bounding-elementary-symmetric-polynomials-away-from-zero) (Jul 30, 2024; 0 answers at time of writing).
- **Status:** **Completely Proved** for all integers $2 \le m \le n$ and all $1 \le k < m$, including the exact characterization of the unique equality case.
- **Formal & computational verification:**
  - Zero-dependency Lean 4 algebraic certificate for $m = 3, 4, 5$: [`JohnstonEsymmM345.lean`](JohnstonEsymmM345.lean)
  - Exact rational verifier for $m = 3, 4, 5$ and the cubic perturbation for $m = 3 \dots 8$: [`verify_identities_m345.py`](python/verify_identities_m345.py)
  - Exact rational verifier and C++ adversarial search: [`verify_mo476077.py`](python/verify_mo476077.py), [`mo476077_search.cpp`](cpp/mo476077_search.cpp)

---

## Theorem

Let $2 \le m \le n$ be integers. Define the rescaled feasible set ($y_i = (m-1)x_i$)
$$\mathcal{F}_{m,n} := \left\{ y \in \mathbb{R}^n : y_i \le 1 \text{ for all } i,\; e_1(y) = m - 1,\; e_j(y) \ge 0 \text{ for } 1 \le j \le m \right\},$$
where $e_j$ denotes the $j$-th elementary symmetric polynomial (with $e_0(y) = 1$). Then for every $y \in \mathcal{F}_{m,n}$ and every integer $1 \le k < m$,
$$e_k(y) \ge \binom{m-1}{k}.$$
Moreover, for $2 \le k < m$, equality holds if and only if $y$ is a permutation of
$$(\underbrace{1, \dots, 1}_{m-1},\; \underbrace{0, \dots, 0}_{n-m+1}).$$
*(Setting $x = y/(m-1)$ gives the original MathOverflow #476077 inequality $e_k(x) \ge \binom{m-1}{k}/(m-1)^k$.)*

---

## Preliminary Lemmas

### Lemma 1 (Zero-Tail Rigidity and Strict Positivity of $e_1, \dots, e_{m-1}$)

1. **(Zero-tail rigidity)** Let $y \in \mathbb{R}^n$ and $1 \le r < n$. Suppose $e_0(y), \dots, e_r(y) \ge 0$, $e_r(y) = 0$, and $e_{r+1}(y) \ge 0$. Then $e_j(y) = 0$ for all $j \ge r$, and consequently at most $r - 1$ entries of $y$ are nonzero.
2. **(Strict positivity)** For every $y \in \mathcal{F}_{m,n}$ and every $1 \le r \le m - 1$, $e_r(y) > 0$.

**Proof.** For (1), consider $f(t) = \prod_{i=1}^n (t + y_i) = \sum_{j=0}^n e_j(y) t^{n-j}$. If $r = 1$, then $e_1(y) = 0$ and $e_2(y) \ge 0$ yield $\sum_{i=1}^n y_i^2 = e_1(y)^2 - 2 e_2(y) = -2 e_2(y) \le 0$, so $y = 0$ and $e_j(y) = 0$ for all $j \ge 1$. Now suppose $r \ge 2$ and, for contradiction, let $s > r$ be minimal with $e_s(y) \neq 0$.

- If $s = r + 1$, let $h(t) := \frac{(r+1)!}{n!} f^{(n-r-1)}(t) = \sum_{j=0}^{r+1} \frac{e_j(y)}{\binom{n}{j}}\binom{r+1}{j} t^{r+1-j}$. By repeated application of Rolle's theorem, $h(t)$ is real-rooted of degree $r+1$ with all coefficients nonnegative, so we may write $h(t) = \prod_{a=1}^{r+1} (t + z_a)$ with $z_a \ge 0$. The linear coefficient of $h$ vanishes because $e_r(y) = 0$, so $\sum_{a=1}^{r+1} \prod_{b \neq a} z_b = 0$. Since $z_a \ge 0$, at least two $z_a$ must vanish, forcing $h(0) = \frac{e_{r+1}(y)}{\binom{n}{r+1}} = 0$, contradicting $e_{r+1}(y) \neq 0$.
- Thus $s \ge r + 2 \ge 4$ (in particular $s \ge 3$), and by minimality of $s$ together with $e_r(y) = 0$, we have $e_{s-1}(y) = e_{s-2}(y) = 0$. Set $g(t) := \frac{s!}{n!} f^{(n-s)}(t) = \prod_{l=1}^s (t - \rho_l)$. Again by Rolle's theorem, $g$ is real-rooted of degree $s \ge 3$, and $g(0) = e_s(y)/\binom{n}{s} \neq 0$ (so $\rho_l \in \mathbb{R} \setminus \{0\}$), while $g'(0) = g''(0) = 0$. Differentiating the logarithmic derivative $g'(t)/g(t) = \sum_{l=1}^s (t - \rho_l)^{-1}$ at $t = 0$ gives
  $$\frac{g''(0) g(0) - g'(0)^2}{g(0)^2} = -\sum_{l=1}^s \frac{1}{\rho_l^2} < 0,$$
  contradicting $g'(0) = g''(0) = 0$.

Hence $e_j(y) = 0$ for all $j \ge r$. If $y$ had $k \ge r$ nonzero entries, then $e_k(y)$ would equal the nonzero product of those $k$ entries whenever $y$ has no other nonzero entries, contradiction; thus at most $r - 1$ entries of $y$ are nonzero.

For (2), if $e_r(y) = 0$ for some $1 \le r \le m - 1$, then $r + 1 \le m$ so $e_{r+1}(y) \ge 0$ holds by $y \in \mathcal{F}_{m,n}$. By (1), at most $r - 1 \le m - 2$ entries of $y$ are nonzero. Since every entry satisfies $y_i \le 1$, we get $e_1(y) = \sum y_i \le m - 2 < m - 1$, contradiction. $\square$

---

### Lemma 2 (Strong Dropping Lemma via Hermite-Biehler and Gauss-Lucas)

Let $y \in \mathbb{R}^n$ with $1 \le m \le n$, and let $y_{\setminus i} \in \mathbb{R}^{n-1}$ be obtained by deleting $y_i$.
1. If $e_j(y) \ge 0$ for $0 \le j \le m$, then $e_r(y_{\setminus i}) \ge 0$ for $0 \le r \le m - 1$.
2. If $e_j(y) > 0$ for $0 \le j \le m$, then $e_r(y_{\setminus i}) > 0$ for $0 \le r \le m - 1$.
3. If $y \in \mathcal{F}_{m,n}$ with $m \ge 3$, and $y' \in \mathbb{R}^{n-3}$ deletes any $3$ entries of $y$, then $e_r(y') > 0$ for $0 \le r \le m - 4$ and $e_{m-3}(y') \ge 0$.
4. If $e_0(y), \dots, e_{m-1}(y) > 0$, $e_m(y) \ge 0$, and $y_i < 0$, then $e_r(y_{\setminus i}) > 0$ for all $0 \le r \le m$.

**Proof.** Set $f(t) = \prod_{l=1}^n (t + y_l) = (t + y_i) g(t)$ where $g(t) = \prod_{l \neq i} (t + y_l)$. Consider the complex polynomial $P(z) := f(z) + i g(z) = (z + y_i + i) g(z)$. Since all roots of $g$ are real and $-y_i - i$ has imaginary part $-1$, every root of $P$ lies in the closed lower half-plane $\mathbb{H}_- := \{z \in \mathbb{C} : \operatorname{Im}(z) \le 0\}$.

Let $d := n - m \ge 0$. By the Gauss-Lucas theorem applied $d$ times, all roots of $P^{(d)}(z) = f^{(d)}(z) + i g^{(d)}(z)$ also lie in $\mathbb{H}_-$. Note that $\deg f^{(d)} = m$ and $\deg g^{(d)} = m - 1$, with positive leading coefficients $n!/m!$ and $(n-1)!/(m-1)!$. By Rolle's theorem, $f^{(d)}$ and $g^{(d)}$ are real-rooted. Let $H(t) := \gcd(f^{(d)}(t), g^{(d)}(t))$ be their monic real greatest common divisor, and write $f^{(d)} = H \tilde f$, $g^{(d)} = H \tilde g$, so $K := \deg \tilde f \ge 1$, $\deg \tilde g = K - 1$, $\gcd(\tilde f, \tilde g) = 1$, and $P^{(d)} = H \cdot (\tilde f + i \tilde g)$.

Since $\tilde f$ and $\tilde g$ are real polynomials without common roots, $\tilde P := \tilde f + i \tilde g$ has no real roots. As every root of $\tilde P$ is a root of $P^{(d)}$, all $K$ roots $w_1, \dots, w_K$ of $\tilde P$ satisfy $\operatorname{Im}(w_j) < 0$ strictly. Writing $\tilde P(t) = c_K \prod_{j=1}^K (t - w_j)$ with $c_K = n!/m! > 0$, each factor $t - w_j$ lies in the open upper half-plane for $t \in \mathbb{R}$, so a continuous branch of $\theta(t) := \arg \tilde P(t)$ decreases strictly from $K\pi$ (as $t \to -\infty$) to $0$ (as $t \to +\infty$). Since $\tilde g(t) = 0 \iff \theta(t) \in \pi \mathbb{Z}$ and $\tilde f(t) = 0 \iff \theta(t) \in \frac{\pi}{2} + \pi \mathbb{Z}$, the $K - 1$ roots $\beta_1 < \dots < \beta_{K-1}$ of $\tilde g$ strictly interlace the $K$ roots $\alpha_1 < \dots < \alpha_K$ of $\tilde f$:
$$\alpha_1 < \beta_1 < \alpha_2 < \beta_2 < \dots < \beta_{K-1} < \alpha_K.$$
In particular, every root of $g^{(d)} = H \tilde g$ is either a root of $H$ (hence a root of $f^{(d)}$) or strictly less than $\alpha_K$ (a root of $f^{(d)}$).

- Under hypothesis (1), $f^{(d)}$ has nonnegative coefficients and positive leading term, so all roots of $f^{(d)}$ are $\le 0$. Thus all roots of $g^{(d)}$ are $\le 0$, giving $e_r(y_{\setminus i}) \ge 0$ for $0 \le r \le m - 1$.
- Under hypothesis (2), all coefficients of $f^{(d)}$ are strictly positive, so all roots of $f^{(d)}$ are $< 0$. Thus all roots of $g^{(d)}$ are $< 0$, giving $e_r(y_{\setminus i}) > 0$ for $0 \le r \le m - 1$.

For (3), $y \in \mathcal{F}_{m,n}$ satisfies $e_0(y), \dots, e_{m-1}(y) > 0$ (Lemma 1(2)) and $e_m(y) \ge 0$. Deleting the 3 entries one by one: after 1 deletion we have $e_0, \dots, e_{m-2} > 0$ by (2) at order $m-1$ and $e_{m-1} \ge 0$ by (1) at order $m$; after 2 deletions we have $e_0, \dots, e_{m-3} > 0$ and $e_{m-2} \ge 0$; after 3 deletions we have $e_0, \dots, e_{m-4} > 0$ and $e_{m-3} \ge 0$ (when $m = 3$, this simply reads $e_0(y') = 1 > 0$).

For (4), $e_0(y_{\setminus i}) = 1 > 0$, and induction on $r = 1, \dots, m$ using the recurrence $e_r(y_{\setminus i}) = e_r(y) + (-y_i) e_{r-1}(y_{\setminus i})$ with $-y_i > 0$ yields $e_r(y_{\setminus i}) > 0$ immediately. $\square$

---

### Lemma 3 (Nonnegative Case, Including $n = m$)

If $y \in \mathcal{F}_{m,n}$ satisfies $y_i \ge 0$ for all $i$ (which is automatic when $n = m$, since $n = m$ and $y_i \le 1$ with $\sum y_i = m - 1$ implies $y_i = (m-1) - \sum_{l \neq i} y_l \ge (m-1) - (m-1) = 0$), then $e_k(y) \ge \binom{m-1}{k}$ for $1 \le k < m$, with equality for $2 \le k < m$ if and only if $y$ is a permutation of $(1^{m-1}, 0^{n-m+1})$.

**Proof.** Repeatedly take any two entries satisfying $0 < y_j \le y_i < 1$ and replace $(y_i, y_j)$ by $(y_i + \epsilon, y_j - \epsilon)$ with $\epsilon := \min(1 - y_i, y_j) > 0$. This preserves $y \ge 0$, $y \le 1$, and $e_1(y) = m - 1$, increases the number of entries in $\{0, 1\}$ by at least $1$, and changes $e_k$ ($2 \le k < m$) by
$$\Delta e_k = (-\epsilon(y_i - y_j) - \epsilon^2)\, e_{k-2}(y_{\setminus \{i,j\}}).$$
By Lemma 1(2) and two applications of Lemma 2(2) at orders $m - 1$ and $m - 2$ (valid since $m - 1 \le n$ and $m - 2 \le n - 1$), $e_{k-2}(y_{\setminus \{i,j\}}) > 0$ strictly for $2 \le k < m$. Thus each step strictly decreases $e_k$ for $2 \le k < m$, while nonnegativity of the updated vector trivially maintains $e_r \ge 0$ for all $r$. Terminating in at most $n$ steps at a $\{0,1\}$-vector with sum $m - 1$, we reach a permutation of $(1^{m-1}, 0^{n-m+1})$, where $e_k = \binom{m-1}{k}$. Because every prior step strictly lowered $e_k$, equality holds iff no step was possible, i.e., $y$ was already a permutation of $(1^{m-1}, 0^{n-m+1})$. $\square$

---

## Main Proof (Induction on $m \ge 2$)

**Base case ($m = 2$):** For $1 \le k < 2$, $k = 1$ and $e_1(y) = 1 = \binom{1}{1}$ by definition of $\mathcal{F}_{2,n}$.

**Inductive step ($m \ge 3$):** Assume the theorem (including the equality characterization for $2 \le k < m - 1$ when $m - 1 \ge 3$) holds for $m - 1$ and all $n' \ge m - 1$. Fix any $n \ge m$ and $k \in \{2, \dots, m - 1\}$. By Lemma 3, the case $n = m$ is already settled, so we may assume $n \ge m + 1$.

### Step 1: Compactness of $\mathcal{F}_{m,n}$
For any $y \in \mathcal{F}_{m,n}$, $1 - y_j \ge 0$ for all $j$ and $\sum_{j=1}^n (1 - y_j) = n - (m - 1) = n - m + 1$. Hence $1 - y_i \le n - m + 1$, giving
$$m - n \le y_i \le 1 \qquad (1 \le i \le n).$$
Thus $\mathcal{F}_{m,n}$ is compact and nonempty, so $e_k$ attains its global minimum on $\mathcal{F}_{m,n}$ at some point $y^* \in \mathcal{F}_{m,n}$.

### Step 2: Boundary Minimizers ($y^*_i = 1$ for some $i$)
Suppose $y^*_i = 1$ for some $i$, and let $y' := y^*_{\setminus i} \in \mathbb{R}^{n-1}$. By Lemma 2(1), $e_r(y') \ge 0$ for $1 \le r \le m - 1$; also $y'_l \le 1$ and $e_1(y') = e_1(y^*) - 1 = m - 2$. Hence $y' \in \mathcal{F}_{m-1, n-1}$ with $n - 1 \ge m - 1$. Using $e_k(y^*) = e_k(y') + e_{k-1}(y')$:
- If $2 \le k \le m - 2$ (which requires $m \ge 4$), the induction hypothesis gives $e_k(y') \ge \binom{m-2}{k}$ and $e_{k-1}(y') \ge \binom{m-2}{k-1}$, so
  $$e_k(y^*) \ge \binom{m-2}{k} + \binom{m-2}{k-1} = \binom{m-1}{k}.$$
- If $k = m - 1$, then $e_{m-1}(y') \ge 0$ (since $y' \in \mathcal{F}_{m-1,n-1}$) and $e_{m-2}(y') \ge \binom{m-2}{m-2} = 1$ (by induction for $m \ge 4$, and directly from $e_1(y') = 1$ for $m = 3$), so
  $$e_{m-1}(y^*) = e_{m-1}(y') + e_{m-2}(y') \ge 0 + 1 = 1 = \binom{m-1}{m-1}.$$

### Step 3: Elimination of Interior Minimizers ($y^*_i < 1$ for all $i$)
Suppose for contradiction that $y^*_i < 1$ for all $1 \le i \le n$. By Lemma 3, $y^*$ must have at least one negative entry, and since $e_1(y^*) = m - 1 > 0$, it also has at least one positive entry. In particular, $y^*$ has at least two distinct entries.

For any three chosen coordinates $(y^*_1, y^*_2, y^*_3)$ (reindexing if needed), write $y' := (y^*_4, \dots, y^*_n) \in \mathbb{R}^{N}$ where $N = n - 3 \ge m - 2 \ge 1$, and set $h_r := e_r(y')$ (with $h_{-1} = 0$, $h_0 = 1$). Let
$$g(t) := (t - y^*_1)(t - y^*_2)(t - y^*_3) = t^3 - s_1 t^2 + s_2 t - s_3.$$
Replacing $(y^*_1, y^*_2, y^*_3)$ by the roots $(y_1(\epsilon), y_2(\epsilon), y_3(\epsilon))$ of a cubic perturbation $g_\epsilon(t) = g(t) + (\Delta s_2) t - (\Delta s_3)$ keeps $s_1$ and $y'$ fixed, so $\Delta e_1 = 0$ and for every $2 \le j \le m$:
$$\Delta e_j = (\Delta s_2)\, h_{j-2} + (\Delta s_3)\, h_{j-3}.$$
By Lemma 1(2), $e_1(y^*), \dots, e_{m-1}(y^*) > 0$. Since $y^*_i < 1$ for all $i$ and $e_1, \dots, e_{m-1} > 0$, any sufficiently small real root-perturbation preserves $y_i < 1$ and $e_1, \dots, e_{m-1} > 0$, so to contradict minimality of $e_k(y^*)$ it suffices to produce a smooth or continuous family of real roots near $(y^*_1, y^*_2, y^*_3)$ with $\Delta e_m \ge 0$ and $\Delta e_k < 0$ for small $\epsilon > 0$.

#### Case 1: $y^*$ has at least $3$ distinct entries
Reindex so $y^*_1 > y^*_2 > y^*_3$. Because these roots of $g$ are simple, by the Implicit Function Theorem any perturbation $g_\epsilon(t)$ with coefficients $O(\epsilon)$ has $3$ simple real roots $y_l(\epsilon) = y^*_l + O(\epsilon) < 1$ for sufficiently small $\epsilon > 0$. By Lemma 2(3), $h_0, \dots, h_{m-4} > 0$ and $h_{m-3} \ge 0$.

- **Subcase 1a ($h_{m-3} > 0$):** Set $\alpha := h_{m-2}/h_{m-3}$ and take $g_\epsilon(t) := g(t) - \epsilon(t + \alpha)$, so $\Delta s_2 = -\epsilon$ and $\Delta s_3 = +\epsilon \alpha$. Then $\Delta e_m = \epsilon(-h_{m-2} + \alpha h_{m-3}) = 0$ identically, preserving $e_m \ge 0$, while
  $$\Delta e_k = -\frac{\epsilon}{h_{m-3}} \left( h_{k-2} h_{m-3} - h_{k-3} h_{m-2} \right).$$
  We verify $h_{k-2} h_{m-3} - h_{k-3} h_{m-2} > 0$:
  - If $k = 2$, then $h_{k-3} = h_{-1} = 0$ and $h_{k-2} = h_0 = 1$, so $h_0 h_{m-3} - 0 = h_{m-3} > 0$.
  - If $3 \le k \le m - 1$ and $h_{m-2} \le 0$, then $h_{k-2} > 0, h_{m-3} > 0, h_{k-3} > 0$ give $h_{k-2} h_{m-3} > 0 \ge h_{k-3} h_{m-2}$.
  - If $3 \le k \le m - 1$ and $h_{m-2} > 0$, then $h_0, \dots, h_{m-2} > 0$ and $N = n - 3 \ge m - 2 > m - 3$. Because $\prod_{l=4}^n (t + y^*_l)$ is real-rooted of degree $N$, Newton's inequalities give for every $1 \le j \le m - 3 \le N - 1$:
    $$h_j^2 \ge \frac{j+1}{j} \cdot \frac{N - j + 1}{N - j} \, h_{j-1} h_{j+1} > h_{j-1} h_{j+1} \implies \frac{h_{j+1}}{h_j} < \frac{h_j}{h_{j-1}}.$$
    Chaining from $j = k - 2$ to $j = m - 3$ yields $\frac{h_{m-2}}{h_{m-3}} < \frac{h_{k-2}}{h_{k-3}}$, hence $h_{k-2} h_{m-3} > h_{k-3} h_{m-2}$.

  In all subcases $\Delta e_k < 0$, contradicting minimality of $e_k(y^*)$.

- **Subcase 1b ($h_{m-3} = 0$):** Here $m \ge 4$ (as $h_0 = 1 > 0$). Newton's inequality at $j = m - 3$ gives $h_{m-3}^2 \ge \frac{(m-2)(N-m+4)}{(m-3)(N-m+3)} h_{m-4} h_{m-2}$; since $h_{m-3} = 0$ and $h_{m-4} > 0$, we must have $h_{m-2} \le 0$.
  - If $2 \le k \le m - 2$, take $g_\epsilon(t) := g(t) - \epsilon t$ ($\Delta s_2 = -\epsilon$, $\Delta s_3 = 0$). Then $\Delta e_m = -\epsilon h_{m-2} \ge 0$ and $\Delta e_k = -\epsilon h_{k-2} < 0$.
  - If $k = m - 1$, take $g_\epsilon(t) := g(t) + \epsilon$ ($\Delta s_2 = 0$, $\Delta s_3 = -\epsilon$). Then $\Delta e_m = -\epsilon h_{m-3} = 0$ and $\Delta e_{m-1} = -\epsilon h_{m-4} < 0$.

  Both contradict minimality of $e_k(y^*)$.

#### Case 2: $y^*$ has exactly $2$ distinct entries $1 > a > 0 > b$
Suppose $y^*$ consists of $p$ copies of $a$ and $q$ copies of $b$ with $p + q = n$. Since $q \ge 1$, $b < 0$, and $a < 1$, we have
$$p a = (m - 1) - q b > m - 1 \implies p \ge m \ge 3.$$
Choose $(y^*_1, y^*_2, y^*_3) = (a, a, b)$, so $g(t) = (t - a)^2(t - b)$ and $y'$ retains $p - 2$ copies of $a$ and $q - 1$ copies of $b$.

Delete $b < 0$ first: by Lemma 1(2) and Lemma 2(4), $y^*_{\setminus b} \in \mathbb{R}^{n-1}$ satisfies $e_0, \dots, e_m > 0$. Next delete two copies of $a$ successively via Lemma 2(2) (applied at orders $m$ and $m - 1$, valid since $n - 1 \ge m$ and $n - 2 \ge m - 1$), giving $h_0, h_1, \dots, h_{m-2} > 0$ strictly! Hence $\alpha := h_{m-2}/h_{m-3} > 0$, and since $a > 0$, we have $a + \alpha > 0$.

Consider $g_\epsilon(t) := (t - a)^2(t - b) - \epsilon(t + \alpha)$ for small $\epsilon > 0$. Choose $\delta > 0$ small enough that $b < a - \delta < a + \delta < 1$. Because $(t - a)^2(t - b) > 0$ at $t = a \pm \delta$, for sufficiently small $\epsilon > 0$ we have:
$$g_\epsilon(a - \delta) > 0, \qquad g_\epsilon(a) = -\epsilon(a + \alpha) < 0, \qquad g_\epsilon(a + \delta) > 0,$$
while $\lim_{t \to -\infty} g_\epsilon(t) = -\infty$. By the Intermediate Value Theorem, $g_\epsilon$ has three distinct real roots inside $(-\infty, a - \delta)$, $(a - \delta, a)$, and $(a, a + \delta)$, all strictly less than $1$ and converging to $(b, a, a)$ as $\epsilon \to 0^+$. As in Subcase 1a, $\Delta e_1 = 0$, $\Delta e_m = 0$, and $\Delta e_k < 0$ (since $h_0, \dots, h_{m-2} > 0$ and $N = n - 3 > m - 3$), contradicting minimality of $e_k(y^*)$.

Thus no interior minimizer exists, establishing $e_k(y) \ge \binom{m-1}{k}$ for all $y \in \mathcal{F}_{m,n}$.

### Step 4: Unique Equality Case ($2 \le k < m$)
Suppose $y^* \in \mathcal{F}_{m,n}$ attains $e_k(y^*) = \binom{m-1}{k}$ for some $2 \le k < m$. By Step 3, $y^*_i = 1$ for some $i$; let $y' = y^*_{\setminus i} \in \mathcal{F}_{m-1, n-1}$ as in Step 2.
- If $2 \le k \le m - 2$ ($m \ge 4$), equality in $e_k(y') + e_{k-1}(y') \ge \binom{m-2}{k} + \binom{m-2}{k-1}$ forces $e_k(y') = \binom{m-2}{k}$. Since $k \ge 2$ and $k < m - 1$, the induction hypothesis implies $y'$ is a permutation of $(1^{m-2}, 0^{n-m+1})$.
- If $k = m - 1$ and $m \ge 4$, equality in $e_{m-1}(y') + e_{m-2}(y') \ge 0 + 1$ forces $e_{m-2}(y') = 1 = \binom{m-2}{m-2}$ with $m - 2 \ge 2$, so by induction $y'$ is again a permutation of $(1^{m-2}, 0^{n-m+1})$.
- If $k = m - 1$ and $m = 3$, equality $e_2(y^*) = 1$ forces $e_2(y') = 0$ (since $e_2(y') \ge 0$ and $e_1(y') = 1$). Then $e_0(y') = 1 > 0$, $e_1(y') = 1 > 0$, $e_2(y') = 0$, and $e_3(y') = e_3(y^*) - e_2(y') = e_3(y^*) \ge 0$. By Lemma 1(1) with $r = 2$ (noting $n - 1 \ge 3 > 2$ when $n \ge 4$, while $n = 3$ is covered by Lemma 3), $y'$ has at most $1$ nonzero entry; combined with $e_1(y') = 1$, $y'$ must be a permutation of $(1, 0^{n-2})$.

Reinserting $y^*_i = 1$, every minimizer $y^*$ is a permutation of $(1^{m-1}, 0^{n-m+1})$. Conversely, that vector clearly lies in $\mathcal{F}_{m,n}$ and achieves $e_k = \binom{m-1}{k}$. $\blacksquare$

---

## Companion Zero-Calculus Algebraic Certificates ($m = 3, 4, 5$)

For $m = 3, 4, 5$, elementary nonnegativity of the quadratic-weighted sums $S_{2,r} := \sum_{i=1}^n y_i^2 (1 - y_i)^r \ge 0$ ($r \ge 0$, valid for all real $y_i \le 1$, including negative entries) yields pure polynomial-ring certificates verified over $\mathbb{Z}[e_2, \dots, e_m]$ in [`JohnstonEsymmM345.lean`](JohnstonEsymmM345.lean) and over $\mathbb{Q}$ in [`verify_identities_m345.py`](python/verify_identities_m345.py).
