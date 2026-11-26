# Partial Proof & Structural Reduction: Berlow's Conjecture 5.1 / Zhang's Conjecture 4.2 for $T = \{132, 213\}$ (Conjugate to $\{231, 312\}$)

- **Sources:**
  - Katalin Berlow, *Restricted stacks as functions* ([arXiv:2008.01164v2](https://arxiv.org/abs/2008.01164), *Discrete Mathematics* 2021), Conjecture 5.1 and Lemma 3.5.
  - Owen Zhang, *The Order of the (123, 132)-Avoiding Stack Sort* ([arXiv:2405.01854](https://arxiv.org/abs/2405.01854)), Conjecture 4.2.
- **Scope & Status:** **Verified Partial Resolution.** For the remaining half $T = \{132, 213\}$ (conjugate to $\{231, 312\}$ via complementation), we prove for **all $n \ge 1$**:
  1. Every orbit visits permutations beginning with $n$ and permutations beginning with $1$ infinitely often (via an explicit binary-weight descent), reducing the conjecture to a first-return map $R_n : S_{n-1} \to S_{n-1}$.
  2. Exact decomposition of $f$ on the first letter, giving $f(n\rho) = W(\rho)n$ where $W = s_{21}$ is West's classical stack sort.
  3. Complete exclusion of non-monotone periodic points of period $1$, $2$, or $3$ for all $n \ge 1$.
  4. **Exhaustive computational proof through $n = 12$** (every permutation in $S_1 \dots S_{12}$ reaches $\{\mathrm{id}_n, \mathrm{id}_n^r\}$, checking all $578{,}290$ distinct classical images at $n = 12$).
  - **Open Gap:** Any counterexample to the general conjecture for $T = \{132, 213\}$ must have size $n \ge 13$ and least period $\ge 4$.
- **Verifier:** [`verify_berlow_132_213.py`](verify_berlow_132_213.py) (`python3 verify_berlow_132_213.py --through-12`).
- **Companion Track:** See [`06-berlow-stack-sorting`](../06-berlow-stack-sorting/PROOF.md) for the complete all-$n$ resolution of the $\{213, 231\}$ map from Conjecture 5.1.

---

## 1. The Stack Rule

Write $f := s_{\{132, 213\}}$ for the map on words of distinct integers. Read the input from left to right. Push the incoming letter whenever legal. On a blocked push, pop the top to the output and retry the same letter. Flush the stack from top to bottom at the end. All patterns in a stack are read from top to bottom.

**Lemma 1.** Given a $\{132, 213\}$-avoiding stack and an incoming letter $x$, a push is blocked exactly when some stack entries $a, b$, with $a$ above $b$, satisfy $x < b < a$ or $a < x < b$. In particular, the first input letter is the last output letter ($f(p)_n = p_1$).

**Proof.** A newly formed forbidden subsequence must begin with $x$. The two displayed inequalities are the exact rank conditions for $132$ ($x < b < a$) and $213$ ($a < x < b$). In a singleton stack neither condition can hold, so the bottom letter is never popped while any input letter remains and exits last in the final flush. $\square$

---

## 2. Decomposition at the First Letter

Let $W$ denote West's classical ($21$-avoiding) stack sort on distinct letters: it keeps the stack strictly increasing from top to bottom, popping while its top is smaller than the incoming letter. Both $f$ and $W$ map the empty word to itself.

**Lemma 2.** Write a nonempty word uniquely as
$$j H_0 u_1 H_1 u_2 H_2 \cdots u_m H_m,$$
where $j$ is the first letter, $u_1, \dots, u_m$ are all subsequent letters smaller than $j$, and each $H_i$ is a possibly empty word of letters greater than $j$. Run the classical sort $W$ on $j u_1 \cdots u_m$; let $E_i$ be the word popped while admitting $u_i$ in that run, and let $D$ be its final flush. Then
$$f(j H_0 u_1 H_1 \cdots u_m H_m) = f(H_0) E_1 f(H_1) E_2 \cdots E_m f(H_m) D.$$
In particular, $f(n\rho) = W(\rho) n$ for every $\rho \in S_{n-1}$.

**Proof.** The low letters below $j$ remain in a strictly increasing stack (top to bottom) with $j$ at the bottom. During each high gap $H_i$, all high entries sit above these low letters; a proposed high letter $x > j$ cannot form $132$ or $213$ using any lower entry below $H_i$, because the bottom witness $b$ in either inequality of Lemma 1 must satisfy $b > x$, forcing any witness $a$ above $b$ to lie in the same high gap. Thus each $H_i$ is processed identically to an independent run of $f$.

When a low letter $u_i < j$ arrives, every surviving high letter $h > j$ above $j$ blocks the push via $(u_i, h, j) \sim 132$, flushing $f(H_{i-1})$ completely. On the remaining increasing low stack, $u_i$ cannot be the top of a $132$ (the stack increases toward $j$ below it), and creates a $213$ exactly when the top entry $a$ satisfies $a < u_i < j$. Hence pops and pushes match $W(j u_1 \cdots u_m)$ and maintain increasing low-stack order. For $j = n$, all gaps $H_i$ are empty and $n$ sits at the bottom throughout $W(\rho)$, leaving output $W(\rho) n$. $\square$

---

## 3. Binary-Weight Descent Toward Extreme First Letters

For $e \in \{1, n\}$ and $p \in S_n$, let $B_e(p)$ be the set of letters appearing strictly before $e$ in $p$, and define
$$L_e(p) := \sum_{a \in B_e(p)} 2^{n-a}.$$

**Lemma 3.** If $p \in S_n$ starts with $j \neq e$, then $j$ leaves $B_e$ during this pass, and every letter entering $B_e$ exceeds $j$. Consequently,
$$L_e(f(p)) < L_e(p).$$

**Proof.** The letter $j$ starts before $e$ and is emitted last by Lemma 1, so $j \in B_e(p) \setminus B_e(f(p))$. Suppose a letter $y \notin B_e(p)$ enters $B_e(f(p))$; then $y$ arrives after $e$ in $p$ and is output before $e$, so $e$ is still on the stack with $j$ beneath $e$ when $y$ is pushed. If $e = n$ and $y < j$, $(y, n, j)$ is a $132$; if $e = 1$ and $y < j$, $(y, 1, j)$ is a $213$. Neither can remain unpopped, so $y > j$. Hence the gained weight is at most $\sum_{a=j+1}^n 2^{n-a} = 2^{n-j} - 1 < 2^{n-j}$, proving strict descent. $\square$

**Corollary 4.** For both $e = 1$ and $e = n$, every forward orbit of $f$ visits permutations beginning with $e$ infinitely often, hitting the first such state within $L_e(p)$ steps. $\square$

---

## 4. First-Return Reduction and Low-Period Obstructions

For $\rho \in S_{n-1}$, define $R_n(\rho) := \sigma \in S_{n-1}$ by starting at $n\rho$ and iterating $f$ until the first positive iterate starting with $n$, namely $n\sigma$ (well-defined by Corollary 4).

**Proposition 5 (First-Return Reduction).** For $n \ge 2$, cycles of $f$ on $S_n$ correspond bijectively to cycles of $R_n$ on $S_{n-1}$, and the all-size conjecture holds in size $n$ iff every $R_n$-orbit reaches $(n-1, n-2, \dots, 1)$.

**Proof.** Mark states starting with $n$ along any $f$-cycle (nonempty by Corollary 4) and delete their leading $n$; inversely, splice the deterministic forward orbit segments between consecutive marked states. Monotone words invert in one step without early pops, giving a $2$-cycle marking only $(n, n-1, \dots, 1)$. $\square$

**Proposition 6 (Periods $1$ and $2$).** For $n \ge 1$, the only solutions to $f^2(p) = p$ are $\mathrm{id}_n$ and $\mathrm{id}_n^r$. Every other cycle, if one exists, visits at least three distinct first letters (including $1$ and $n$).

**Proof.** Suppose $f^2(p) = p$ and set $q = f(p)$. By Lemma 1 applied to $q$, $f(q)_n = q_1$, and since $f(q) = p$, we get $q_1 = p_n$. Emitting $p_n$ first from $p$ forces zero pops before the final flush, so $q = p^r$ and $p^r$ avoids $\{132, 213\}$. Repeating for $q$ shows $p$ avoids $\{132, 213\}$, while reversal gives that $p$ avoids $\{231, 312\}$. Avoiding all four non-monotone patterns of length $3$ forces $p \in \{\mathrm{id}_n, \mathrm{id}_n^r\}$. If a cycle contains only $\{1, n\}$ as first letters, they must alternate (since $f(p)_n = p_1$ and a permutation has distinct endpoints for $n \ge 2$), forcing $q_1 = p_n$ at every state and hence reducing to reversal. $\square$

**Proposition 7 (Exclusion of Period $3$).** For every $n \ge 2$, if $p \in S_n$ starts with $n$, then $f^3(p)$ never starts with $n$. In particular, $f$ has no orbit of least period $3$.

**Proof.** Since $p = n\rho$, Lemma 2 gives $f(p) = W(\rho)n$, which ends in $(n-1, n)$ because the maximum of a classical stack sort exits last before $n$. During the second pass, the last two incoming letters $n-1$ and $n$ both exceed every element in the stack and are pushed immediately, so the final flush begins with $(n, n-1)$, meaning $f^2(p)$ contains $n$ immediately before $n-1$. During the third pass, when $(n, n-1)$ arrive consecutively: $n$ cannot form $132$ or $213$ (no element exceeds $n$), so $n$ sits at the top of the stack; then $n-1$ cannot form $132$ (requires two distinct elements $> n-1$) or $213$ (requires an element $< n-1$ above $n$). Thus $n-1$ is pushed directly onto $n$, and $n-1$ is flushed before $n$ in $f^3(p)$, preventing $f^3(p)_1 = n$. By Corollary 4 every cycle visits an $n$-start state, ruling out period $3$. $\square$

---

## 5. Exhaustive Verification Through $n = 12$

**Proposition 8.** For all $1 \le n \le 12$, $\{\mathrm{id}_n, \mathrm{id}_n^r\}$ is the unique cycle of $f = s_{\{132, 213\}}$ on $S_n$.

By Corollary 4 and Lemma 2, every cycle visits an image $f(n\rho) = W(\rho)n$ with $W(\rho) \in W(S_{n-1})$. The recurrence
$$\mathcal{I}(A) = \bigcup_{L \sqcup U = A \setminus \{\max A\}} \{ v w \max(A) : v \in \mathcal{I}(L),\ w \in \mathcal{I}(U) \}$$
enumerates all distinct classical outputs in $W(S_{n-1})$, and [`verify_berlow_132_213.py`](verify_berlow_132_213.py) exhaustively traces forward orbits of every single state through $n = 12$ (matching literal triple-check dynamics on $S_1 \dots S_7$):

| $n$ | State Space Checked | Distinct States Checked | Result |
| ---: | :--- | ---: | :--- |
| $1 \dots 7$ | Full symmetric group $S_n$ | $1, 2, 6, 24, 120, 720, 5{,}040$ | Only $\{\mathrm{id}_n, \mathrm{id}_n^r\}$ (max transients $0, 0, 3, 4, 7, 7, 12$) |
| $8$ | $W(S_7)n$ | $326$ | All reach $\mathrm{id}_8$ |
| $9$ | $W(S_8)n$ | $1{,}780$ | All reach $\mathrm{id}_9$ |
| $10$ | $W(S_9)n$ | $11{,}033$ | All reach $\mathrm{id}_{10}$ |
| $11$ | $W(S_{10})n$ | $76{,}028$ | All reach $\mathrm{id}_{11}$ |
| $12$ | $W(S_{11})n$ | $578{,}290$ | All reach $\mathrm{id}_{12}$ |

**Remaining Open Step:** Showing that the first-return map $R_n : S_{n-1} \to S_{n-1}$ has only the fixed point $(n-1, \dots, 1)$ for all $n \ge 13$ (equivalently excluding cycles of period $\ge 4$ for $n \ge 13$).
