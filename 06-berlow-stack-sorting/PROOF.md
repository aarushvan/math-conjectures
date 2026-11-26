# Proof of Berlow's Conjecture 5.1 / Zhang's Conjecture 4.2 for $T = \{213, 231\}$

- **Sources:**
  - Katalin Berlow, *Restricted stacks as functions* ([arXiv:2008.01164v2](https://arxiv.org/abs/2008.01164), *Discrete Mathematics* 2021), Conjecture 5.1.
  - Owen Zhang, *The Order of the (123, 132)-Avoiding Stack Sort* ([arXiv:2405.01854](https://arxiv.org/abs/2405.01854)), Conjecture 4.2.
- **Conjecture:** Under the top-to-bottom stack convention and right-greedy push rule, the only periodic points of the $\{213, 231\}$-avoiding stack-sorting map $f := s_{\{213, 231\}} : S_n \to S_n$ are the identity $\mathrm{id}_n = (1, 2, \dots, n)$ and its reverse $\mathrm{id}_n^r = (n, n-1, \dots, 1)$.
- **Status:** **Completely Proved** for all $n \ge 1$, together with the explicit linear convergence bound $f^{3n-7}(\pi) \in \{\mathrm{id}_n, \mathrm{id}_n^r\}$ for all $n \ge 3$ (while $f(\pi) \in \{\mathrm{id}_n, \mathrm{id}_n^r\}$ in $0$ or $1$ steps for $n \le 2$).
- **Scope note on Conjecture 5.1:** Berlow's Conjecture 5.1 asks for the periodic points of both $s_{\{213, 231\}}$ and $s_{\{132, 213\}}$ (equivalently $s_{\{231, 312\}}$ by complementation symmetry, as noted by Zhang). Since $\{213, 231\}$ is self-complementary whereas $\{132, 213\}^c = \{231, 312\}$, this note completely resolves the $\{213, 231\}$ map; the $\{132, 213\}$ / $\{231, 312\}$ conjugate pair remains separate.
- **Verification:**
  - Zero-dependency Lean 4 formalization of Lemma 3 (Bottom-of-Stack Elimination for all lists) plus kernel checks on $S_4, S_5$: [`BerlowStackSorting.lean`](BerlowStackSorting.lean)
  - Exhaustive Python verifier checking literal $\{213, 231\}$ stack simulation and Lemmas 1-5 on $S_3 \dots S_7$: [`verify_berlow.py`](verify_berlow.py)

---

## Convention

Following Berlow ([arXiv:2008.01164v2](https://arxiv.org/abs/2008.01164), Section 1), input permutation $\pi = (\pi_1, \dots, \pi_n)$ is read left-to-right. The stack $S$ is read **from top to bottom** (newest pushed element first, oldest bottom element last). When incoming element $x = \pi_i$ arrives:
1. While $S$ is nonempty and pushing $x$ onto the top of $S$ would create a subsequence of $x \mathbin{\Vert} S$ order-isomorphic to any pattern in $T = \{213, 231\}$, pop the top element of $S$ to the output.
2. Push $x$ onto the top of $S$.
After all input elements are processed, pop all remaining elements of $S$ from top to bottom to the output.

Note that $f$ satisfies Berlow's Lemma 3.5 complementation symmetry: for $\pi^c_i := n + 1 - \pi_i$, since $T^c = \{213^c, 231^c\} = \{231, 213\} = T$, we have $f(\pi^c) = f(\pi)^c$ for every $\pi \in S_n$.

---

## Proof

### Lemma 1 (Extreme-Only Stack Rule)

Let $S$ be any nonempty stack whose entries (read top-to-bottom) avoid $\{213, 231\}$, and let $x \notin S$. Pushing $x$ onto the top of $S$ creates a top-to-bottom $213$ or $231$ pattern in $x \mathbin{\Vert} S$ if and only if
$$\min(S) < x < \max(S).$$

**Proof.**
- **($\Rightarrow$):** Since $S$ avoids $\{213, 231\}$, any occurrence of $213$ or $231$ in $x \mathbin{\Vert} S$ must use $x$ as its first (top) element, followed by two entries $a$ (above) and $b$ (below) in $S$. If $(x, a, b)$ is a $213$, then $a < x < b$, so $\min(S) \le a < x < b \le \max(S)$. If $(x, a, b)$ is a $231$, then $b < x < a$, so $\min(S) \le b < x < a \le \max(S)$.
- **($\Leftarrow$):** Suppose $\min(S) < x < \max(S)$, and let $u = \min(S)$ and $v = \max(S)$. Since $u < x < v$, $u \neq v$, so both appear at distinct positions in $S$. If $u$ sits above $v$ in $S$, then $(x, u, v)$ forms a $213$ in $x \mathbin{\Vert} S$. If $v$ sits above $u$ in $S$, then $(x, v, u)$ forms a $231$ in $x \mathbin{\Vert} S$. $\square$

---

### Definition (Right-Interior / Bad Elements)

For $\pi \in S_n$, define the set of **right-interior** elements
$$\mathrm{Bad}(\pi) := \{ \pi_i : 1 \le i \le n - 2,\; \min(\pi_{i+1..n}) < \pi_i < \max(\pi_{i+1..n}) \}.$$
Equivalently, $x \notin \mathrm{Bad}(\pi)$ if and only if $x$ is either a **right-to-left minimum** of $\pi$ (every element following $x$ in $\pi$ is $> x$, which holds vacuously for $\pi_n$) or a **right-to-left maximum** of $\pi$ (every element following $x$ in $\pi$ is $< x$). Thus $\mathrm{Bad}(\pi) = \emptyset \iff \pi \in \mathrm{Av}_n(213, 231)$, and $|\mathrm{Bad}(\pi)| \le n - 2$ for $n \ge 2$ since $\pi_{n-1}, \pi_n \notin \mathrm{Bad}(\pi)$.

---

### Lemma 2 (Monotonicity of $\mathrm{Bad}$)

For every $\pi \in S_n$, $\mathrm{Bad}(f(\pi)) \subseteq \mathrm{Bad}(\pi)$.

**Proof.** Take any $x \notin \mathrm{Bad}(\pi)$. By complementation symmetry $f(\pi^c) = f(\pi)^c$ (under which right-to-left minima and maxima swap roles and $\mathrm{Bad}(\pi^c) = \{n+1-y : y \in \mathrm{Bad}(\pi)\}$), we may assume without loss of generality that $x$ is a right-to-left minimum of $\pi$, so every element appearing after $x$ in $\pi$ is strictly greater than $x$.

Consider the moment when $x$ is pushed onto the stack, and let $S_{\text{below}}$ be the stack immediately beneath $x$ after all necessary pops caused by $x$ have completed. By Lemma 1, either $S_{\text{below}} = \emptyset$ or $x$ satisfies one of two exhaustive cases:
- **Case A ($S_{\text{below}} = \emptyset$ or $x < \min(S_{\text{below}})$):** Every element currently remaining in $S_{\text{below}}$ is $> x$, and every remaining input element after $x$ is $> x$. Therefore every element that exits to the output after $x$ is $> x$, making $x$ a right-to-left minimum of $f(\pi)$.
- **Case B ($S_{\text{below}} \neq \emptyset$ and $x > \max(S_{\text{below}})$):** Every later input element satisfies $z > x$. In LIFO stack order, none of the elements in $S_{\text{below}}$ can be popped while $x$ remains on the stack; hence whenever $x$ becomes exposed at the top of the stack during the input scan, the stack equals $[x] \mathbin{\Vert} S_{\text{below}}$ with $\max(S) = x$. By Lemma 1, a later input $z > x = \max(S)$ never triggers a pop of $x$. Thus $x$ stays in the stack until the final flush, when everything above $x$ exits first and only elements of $S_{\text{below}}$ (all $< x$) exit after $x$. Hence $x$ is a right-to-left maximum of $f(\pi)$.

In both cases $x \notin \mathrm{Bad}(f(\pi))$. $\square$

---

### Lemma 3 (Bottom-of-Stack Elimination)

For every $\pi \in S_n$ ($n \ge 1$), $f(\pi)_n = \pi_1$, and hence $\pi_1 \notin \mathrm{Bad}(f(\pi))$. In particular, if $\pi_1 \notin \{1, n\}$, then $|\mathrm{Bad}(f(\pi))| \le |\mathrm{Bad}(\pi)| - 1$.

**Proof.** Input element $\pi_1$ is pushed onto an empty stack. Whenever it is exposed at the top of the stack, the stack is the singleton $[\pi_1]$ with $\min(S) = \max(S) = \pi_1$, so by Lemma 1 it can never be popped during the input scan and exits last during the final flush: $f(\pi)_n = \pi_1$. If $\pi_1 \notin \{1, n\}$, then both $1$ and $n$ follow $\pi_1$ in $\pi$, so $\pi_1 \in \mathrm{Bad}(\pi) \setminus \mathrm{Bad}(f(\pi))$; combining with Lemma 2 yields $|\mathrm{Bad}(f(\pi))| \le |\mathrm{Bad}(\pi)| - 1$. $\square$

*(This lemma is completely formalized for arbitrary lists over $\mathbb{N}$ in [`BerlowStackSorting.lean`](BerlowStackSorting.lean), theorem `s213_231_last_eq_head`.)*

---

### Lemma 4 (At Most Two Consecutive Extreme Starts)

If $n \ge 2$ and $\pi_1, f(\pi)_1, f^2(\pi)_1 \in \{1, n\}$, then $f(\pi) \in \{\mathrm{id}_n, \mathrm{id}_n^r\}$.

**Proof.** Set $\tau := f(\pi)$. By Lemma 3, $\tau_n = \pi_1 \in \{1, n\}$, and since $n \ge 2$ and $\tau$ is a permutation with $\tau_1 \in \{1, n\}$, we have $\{\tau_1, \tau_n\} = \{1, n\}$. Applying Lemma 3 to $\tau$, $f(\tau)_n = \tau_1$, and since $f(\tau)_1 \in \{1, n\}$, we obtain $f(\tau)_1 = \tau_n$.

By complementation symmetry $f(\pi^c) = f(\pi)^c$, assume without loss of generality that $\pi_1 = n$, so $\tau_n = n$, $\tau_1 = 1$, and $f(\tau)_1 = n = \tau_n$. For the very last input element $\tau_n = n$ to be the **first** element output by $f(\tau)$, zero elements can be popped while scanning $\tau_1, \dots, \tau_n$ (any element popped early would precede $\tau_n$ in the output). Thus at step $i \in \{2, \dots, n\}$, the stack before pushing $\tau_i$ is $\{\tau_1, \dots, \tau_{i-1}\}$, which contains $\tau_1 = 1 = \min(S)$. Since pushing $\tau_i$ triggers no pop, Lemma 1 forces $\tau_i \ge \max(\tau_1, \dots, \tau_{i-1})$ for all $2 \le i \le n$. Hence $1 = \tau_1 < \tau_2 < \dots < \tau_n = n$, i.e., $f(\pi) = \mathrm{id}_n$. When $\pi_1 = 1$, complementation gives $f(\pi) = \mathrm{id}_n^r$. $\square$

---

### Lemma 5 (One-Step Convergence from $\mathrm{Av}_n(213, 231)$)

If $\mathrm{Bad}(\pi) = \emptyset$, then $f(\pi) \in \{\mathrm{id}_n, \mathrm{id}_n^r\}$.

**Proof.** For $n = 1$, $S_1 = \{\mathrm{id}_1\}$. For $n \ge 2$, $\pi_1 \notin \mathrm{Bad}(\pi)$ forces $\pi_1 \in \{1, n\}$. By complementation symmetry, assume without loss of generality that $\pi_1 = n$, and write $\pi = (n, \rho_1, \dots, \rho_{n-1})$, where $\rho \in \mathrm{Av}_{n-1}(231)$ (since $\pi$ avoids $231$ and $213$).

By Lemma 3, $n$ remains at the bottom of the stack throughout the scan, so $\max(S) = n$ at every later step. We claim by induction on steps that the portion $S_{\text{top}}$ of the stack strictly above $n$ is always strictly increasing from top to bottom (i.e., $S_{\text{top}}$ avoids $21$): initially $S_{\text{top}} = \emptyset$; if $S_{\text{top}} \neq \emptyset$ has top element $t = \min(S)$, then Lemma 1 pops top elements iff $t < x < n$ (i.e., $t < x$), stopping only when $S_{\text{top}} = \emptyset$ or $x < t$, after which pushing $x$ restores strict top-to-bottom increase and $\min(S) = x = \operatorname{top}(S)$.

Hence $\rho$ undergoes West's classical $21$-avoiding stack-sorting map $s_{21}$ followed by flushing $n$ last. By Knuth's theorem ($s_{21}(\rho) = \mathrm{id}_{n-1} \iff \rho \in \mathrm{Av}_{n-1}(231)$), we obtain $f(\pi) = (1, 2, \dots, n-1, n) = \mathrm{id}_n$. $\square$

---

### Main Theorem

For every $n \ge 1$, the only periodic points of $s_{\{213, 231\}}$ on $S_n$ are $\mathrm{id}_n$ and $\mathrm{id}_n^r$ (which form a $2$-cycle for $n \ge 2$ and a $1$-cycle for $n = 1$). Moreover, for every $n \ge 3$ and every $\pi \in S_n$,
$$f^{3n-7}(\pi) \in \{\mathrm{id}_n, \mathrm{id}_n^r\}.$$

**Proof.** Note first that $\mathrm{Bad}(\mathrm{id}_n) = \mathrm{Bad}(\mathrm{id}_n^r) = \emptyset$, and Lemma 3 + Lemma 5 immediately give $f(\mathrm{id}_n) = \mathrm{id}_n^r$ and $f(\mathrm{id}_n^r) = \mathrm{id}_n$.

Let $\sigma \in S_n$ ($n \ge 2$) be any periodic point of $f$, say $f^p(\sigma) = \sigma$ ($p \ge 1$). By Lemma 2,
$$\mathrm{Bad}(\sigma) \supseteq \mathrm{Bad}(f(\sigma)) \supseteq \dots \supseteq \mathrm{Bad}(f^p(\sigma)) = \mathrm{Bad}(\sigma),$$
so $|\mathrm{Bad}(f^t(\sigma))|$ is constant for all $t \ge 0$. By Lemma 3, every iterate $f^t(\sigma)$ must start with $1$ or $n$. Applying Lemma 4 to $\sigma$ yields $f(\sigma) \in \{\mathrm{id}_n, \mathrm{id}_n^r\}$, and hence $\sigma \in \{\mathrm{id}_n, \mathrm{id}_n^r\}$.

Finally, for $n \ge 3$ and $\pi \in S_n$, let $T \ge 0$ be minimal with $f^T(\pi) \in \{\mathrm{id}_n, \mathrm{id}_n^r\}$ (finite since $S_n$ is finite and $\{\mathrm{id}_n, \mathrm{id}_n^r\}$ is the unique periodic orbit). Assume for contradiction that $T \ge 3n - 6$. Define $s_0 := 1$ if $|\mathrm{Bad}(\pi)| = n - 2$ (which forces $\pi_1 \notin \{1, n\}$, so $|\mathrm{Bad}(f(\pi))| \le n - 3$ by Lemma 3), and $s_0 := 0$ otherwise (so $|\mathrm{Bad}(f^{s_0}(\pi))| \le n - 3$). For each block $t = 0, 1, \dots, n - 4$, set $j_t := s_0 + 3t$. Since
$$j_t + 1 = s_0 + 3t + 1 \le 1 + 3(n - 4) + 1 = 3n - 10 < 3n - 6 \le T,$$
we have $f^{j_t + 1}(\pi) \notin \{\mathrm{id}_n, \mathrm{id}_n^r\}$. By Lemma 4, at least one of $f^{j_t}(\pi), f^{j_t+1}(\pi), f^{j_t+2}(\pi)$ does not start with $1$ or $n$, so Lemmas 2 and 3 give
$$|\mathrm{Bad}(f^{s_0 + 3(t+1)}(\pi))| \le |\mathrm{Bad}(f^{s_0 + 3t}(\pi))| - 1.$$
Summing over $t = 0, \dots, n - 4$ yields $|\mathrm{Bad}(f^{s_0 + 3(n-3)}(\pi))| \le (n - 3) - (n - 3) = 0$, so $\mathrm{Bad}(f^{s_0 + 3(n-3)}(\pi)) = \emptyset$. By Lemma 5, $f^{s_0 + 3(n-3) + 1}(\pi) \in \{\mathrm{id}_n, \mathrm{id}_n^r\}$, whence $T \le s_0 + 3(n-3) + 1 \le 3n - 7$, contradicting $T \ge 3n - 6$. $\blacksquare$
