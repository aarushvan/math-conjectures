# Mathematical Conjectures: Catalogue of Results

[Home](README.md) · [Verification](docs/verification.md) · [Lean status](docs/lean-status.md) · [Statement audit](docs/STATEMENT_AUDIT.md)

Numbers `01.` through `12.` index repository folders sequentially. Sections separate complete resolutions (`01.` to `09.`) from verified partial results and reductions (`10.` to `12.`).

---

## Complete resolutions (`01` to `09`)

### 01. Dihedral shuffle squares for ternary words ✅
- **Source:** J. Grytczuk, B. Pawlik, and M. Pleszczynski, *Variations on shuffle squares* ([arXiv:2308.13882v2](https://arxiv.org/abs/2308.13882v2), Section 2.3, Conjecture 2).
- **Verdict:** False for every even length $2n \ge 8$ ($n \ge 4$).
- **Result:** The explicit family $W_n = \mathtt{0}^{2n-5}\mathtt{11022}$ ($n \ge 4$) consists of even ternary words that cannot partition into two dihedrally similar length-$n$ subwords: balanced counts force $\{U, V\} = \{\mathtt{0}^{n-2}\mathtt{12}, \mathtt{0}^{n-3}\mathtt{102}\}$, whose cyclic adjacent-$\mathtt{00}$ counts $n - 3 \ne n - 4$ disagree under every rotation or reflection in $D_n$. Exhaustive search confirms `0` counterexamples at $n = 3$ (`90` words) and `48` counterexamples at $n = 4$ (`1260` words, forming one $S_3 \times D_8$ orbit of `00011022`).
- **Package:** [`01-dihedral-shuffle-squares/`](01-dihedral-shuffle-squares/) (`PROOF.md`, `DihedralShuffleDisproof.lean`, `verify_dihedral.py`).

### 02. Constant-block vs. distinct run-sum partitions ✅
- **Source:** Gus Wiseman, [OEIS A382427](https://oeis.org/A382427) / [A381717](https://oeis.org/A381717) (2025).
- **Verdict:** True for all integer partitions.
- **Result:** A multiset partition $\lambda$ admits a constant-block decomposition with pairwise distinct sums iff $\lambda$ admits a permutation whose maximal constant runs have pairwise distinct sums. Taking a minimum-block decomposition of size $m$, merging the largest $v$-block with another $v$-block beats minimality unless $2k_v \le m + 1$ for every part value $v$, guaranteeing conflict-free interleaving. Checked exhaustively through $n = 22$.
- **Package:** [`02-oeis-a382427-a381717/`](02-oeis-a382427-a381717/) (`PROOF.md`, `WisemanA382427.lean`, `verify_a382427.py`).

### 03. Prime-difference greedy deviation bound ⬜
- **Source:** M. F. Hasler, [OEIS A377090](https://oeis.org/A377090) (Feb 2025).
- **Verdict:** False for $n \ge 370{,}313$.
- **Result:** The conjectured bound
  $$\bigl\lvert \lvert a(n)\rvert - n/2 \bigr\rvert < 2\ln(n+2)$$
  first fails at $n = 370{,}313$ with $a(370{,}313) = -185{,}183$ ($\lvert d(n)\rvert = 26.5 \ge 2\ln(370{,}315) \approx 25.644219$). Computation in C through $n = 10{,}000{,}000$ records `361` violations, peak ratio `1.309077` against $2\ln(n+2) \approx 29.028094$ at $n = 2{,}010{,}806$ ($a(n) = -1{,}005{,}441$, $\lvert d(n)\rvert = 38.0$), and peak deviation $\lvert d(n)\rvert = 39.0$ at $n = 4{,}652{,}436$ ($a(n) = 2{,}326{,}179$).
- **Package:** [`03-oeis-a377090/`](03-oeis-a377090/) (`DISPROOF.md`, `verify_a377090.c`).

### 04. Anti-run constant-run lengths ✅
- **Source:** Gus Wiseman, [OEIS A384890](https://oeis.org/A384890) (2025).
- **Verdict:** True (every constant run has length $1, 2,$ or $3$).
- **Result:** Using $a(n) = 1 + \operatorname{popcount}(n \mathbin{\&} \lfloor n/2\rfloor)$ for $n \ge 1$ ($a(0) = 0$), modulo-4 and modulo-8 carry recursions exclude any $4$ equal consecutive values while small $n$ realize lengths $1, 2,$ and $3$. Verified against all `87` published OEIS terms and through $n = 1{,}000{,}000$.
- **Package:** [`04-oeis-a384890/`](04-oeis-a384890/) (`PROOF.md`, `WisemanA384890.lean`, `verify_a384890.py`).

### 05. Elementary symmetric polynomial lower bounds 🟡
- **Source:** Nathaniel Johnston, *Bounding elementary symmetric polynomials away from zero* ([MathOverflow #476077](https://mathoverflow.net/questions/476077/bounding-elementary-symmetric-polynomials-away-from-zero), Jul 2024).
- **Verdict:** True for all integers $2 \le m \le n$ and $1 \le k < m$, including uniqueness of equality ($k \ge 2$).
- **Result:** For real vectors $x \in \mathbb{R}^n$ of arbitrary sign with $\max_j x_j \le \frac{1}{m-1}$, $e_1(x) = 1$, and $e_j(x) \ge 0$ ($1 \le j \le m$),
  $$e_k(x) \ge \frac{1}{(m-1)^k}\binom{m-1}{k},$$
  with equality for $2 \le k < m$ iff $(m-1)x$ is a permutation of $(1^{m-1}, 0^{n-m+1})$. After rescaling $y_i = (m-1)x_i \le 1$, boundary minimizers drop from $m$ to $m - 1$ by a Strong Dropping Lemma via Hermite-Biehler and Gauss-Lucas interlacing, while interior minimizers ($y_i < 1$) are eliminated by a 3-variable cubic perturbation $g_\epsilon(t) = g(t) - \epsilon(t + h_{m-2}/h_{m-3})$ via Newton's inequalities and IVT root splitting. Lean 4 checks pure ring certificates for $m = 3, 4, 5$.
- **Package:** [`05-mo476077-johnston/`](05-mo476077-johnston/) (`PROOF.md`, `JohnstonEsymmM345.lean`, `python/`, `cpp/`, `results/search_report.md`).

### 06. Periodic points of `{213, 231}`-avoiding stack sorting ✅
- **Source:** Katalin Berlow, *Restricted stacks as functions* ([arXiv:2008.01164v2](https://arxiv.org/abs/2008.01164), Conj. 5.1); Owen Zhang, *The Order of the (123, 132)-Avoiding Stack Sort* ([arXiv:2405.01854](https://arxiv.org/abs/2405.01854), Conj. 4.2).
- **Verdict:** True for all $n \ge 1$ with explicit transient bound $\le 3n - 7$ ($n \ge 3$).
- **Result:** Under the top-to-bottom stack convention and right-greedy push rule, $s_{\{213, 231\}}$ pops iff $\min(S) < x < \max(S)$, yielding monotonicity $\mathrm{Bad}(f(\pi)) \subseteq \mathrm{Bad}(\pi)$, bottom-of-stack elimination $f(\pi)_n = \pi_1$ (end-to-end proof formalized in Lean 4), at most two consecutive extreme starts outside $\{\mathrm{id}_n, \mathrm{id}_n^r\}$, and one-step convergence from $\mathrm{Av}_n(213, 231)$ via Knuth's theorem.
- **Package:** [`06-berlow-stack-sorting/`](06-berlow-stack-sorting/) (`PROOF.md`, `BerlowStackSorting.lean`, `verify_berlow.py`).

### 07. Disjoint strict-partition families ⬜
- **Source:** Gus Wiseman, [OEIS A384350](https://oeis.org/A384350) (2025).
- **Verdict:** True subset-by-subset for every $S \subseteq \{1, \dots, n\}$ and all $n \ge 0$.
- **Result:** Every non-trivial pairwise disjoint family of strict partitions $\{P_x : x \in S\}$ has $\min\{x \in S : P_x \ne \{x\}\}$ partitioned exclusively inside $\{1, \dots, n\} \setminus S$, giving an elementwise equivalence verified against live OEIS terms for $n = 0 \dots 11$.
- **Package:** [`07-oeis-a384350/`](07-oeis-a384350/) (`PROOF.md`, `verify_a384350.py`).

### 08. Common-sum block partitions Möbius identity ⬜
- **Source:** Gus Wiseman, [OEIS A383093](https://oeis.org/A383093) / [A323774](https://oeis.org/A323774) (2025).
- **Verdict:** True for all $n \ge 1$.
- **Result:** Setting $L(\lambda) = \operatorname{lcm}_i(x_i)$ and $G(\lambda) = \gcd_i(c_i x_i)$, explicit mutually inverse multiplicity-scaling bijections $\Phi, \Psi$ establish
  $$\sum_{d \mid n} a(d) = \sum_{s \mid n} \binom{n/s + \tau(s) - 1}{n/s} = \mathrm{A323774}(n) \qquad (n \ge 1),$$
  checked against live OEIS A383093 ($a(0) = 1$, offset $0$) and A323774 for $n = 0 \dots 24$.
- **Package:** [`08-oeis-a383093/`](08-oeis-a383093/) (`PROOF.md`, `verify_a383093.py`).

### 09. Binary shuffle anti-squares ✅
- **Source:** J. Grytczuk, B. Pawlik, and M. Pleszczynski, *Variations on shuffle squares* ([arXiv:2308.13882v2](https://arxiv.org/abs/2308.13882v2), Section 2.2, Conjecture 1).
- **Verdict:** True for all $n \ge 12$.
- **Result:** The single explicit binary family
  $$W_n := \mathtt{0}^{n-7}\, \mathtt{1}\, \mathtt{0}^2\, \mathtt{1}^4\, \mathtt{0}^{n-8}\, \mathtt{1}^3\, \mathtt{0}\, \mathtt{1}^4 \qquad (n \ge 12)$$
  reduces across all $2n$ cyclic shifts to `12` symbolic cut templates and `568` linear flow systems over $(t = n - 12, x_j, y_j) \ge 0$, every single one certified infeasible for all $t \ge 0$ by an exact integer Farkas dual in $\{-1, 0, 1\}^{11}$. Both the cyclic shift reduction and all `568` Farkas certificates are kernel-checked end-to-end in Lean 4 (`grytczuk_conjecture_1_true`).
- **Package:** [`09-shuffle-antisquares/`](09-shuffle-antisquares/) (`PROOF.md`, `ShuffleAntiSquares.lean`, `verify_antisquares.py`).

---

## Partial results and reductions (`10` to `12`)

### 10. Periodic points of `{132, 213}`-avoiding stack sorting ⬜
- **Source:** K. Berlow ([arXiv:2008.01164v2](https://arxiv.org/abs/2008.01164), Conj. 5.1) / O. Zhang ([arXiv:2405.01854](https://arxiv.org/abs/2405.01854), Conj. 4.2); conjugate to $\{231, 312\}$.
- **Verified scope:** Binary-weight descent forces every orbit to hit $1$-first and $n$-first permutations infinitely often ($f(n\rho) = W(\rho)n$), reducing cycles for all $n$ to the first-return map $R_n : S_{n-1} \to S_{n-1}$; periods $1, 2, 3$ are excluded for all $n \ge 1$, and exhaustive tracing verifies $\{\mathrm{id}_n, \mathrm{id}_n^r\}$ through $n = 12$ (`578,290` states at $n = 12$). Open for $n \ge 13$ and least period $\ge 4$.
- **Package:** [`10-berlow-stack-sorting-132-213/`](10-berlow-stack-sorting-132-213/) (`PARTIAL_PROOF.md`, `verify_berlow_132_213.py`).

### 11. Stanley bivariate monomial positivity ⬜
- **Source:** Richard P. Stanley, [MathOverflow #475478](https://mathoverflow.net/questions/475478) / [arXiv:2511.08969](https://arxiv.org/html/2511.08969#S5), Conjecture 5.2.
- **Verified scope:** Proved for all $d \ge 0$ that $c^\lambda_{\alpha,\beta} = 0$ unless $\alpha \preceq \lambda$ and $\beta \preceq \lambda$ in dominance order, and that $c^\lambda_{\lambda,\beta} = A_{\beta\lambda} \ge 0$ on the principal slice ($c^\lambda_{\lambda,\lambda} = 1$). Exact integer computation verifies all `15,859` ordered classes through $d = 8$ (`0` negatives, `10,535` zeros matching dominance, `5,324` positive). Interior positivity ($\alpha, \beta \prec \lambda$) stays open.
- **Package:** [`11-mo475478-stanley-bivariate/`](11-mo475478-stanley-bivariate/) (`NOTES.md`, `stanley_verify.py`).

### 12. Phan three-layer lattice $C_4$-free density ⬜
- **Source:** Veronica Phan, *A conjecture related to Erdos Problem 86*, [MathOverflow #507835](https://mathoverflow.net/questions/507835).
- **Verified scope:** Four-cycle incidence counting proves asymptotic $C_4$-free density $\le 3/4$ for all $n \ge 2$, settling Phan's $\frac{1}{2} + \frac{1}{2\sqrt{n}}$ conjecture completely for $n = 2, 3, 4$, paired with an explicit $\mathbb{F}_2^2$-parity construction attaining density $3/4$ for $n = 4$ (infinite lattice and all even-period quotients). Includes CPU verifier and PyTorch GPU notebook targeting $n = 5$ (open for $n \ge 5$).
- **Package:** [`12-mo507835-phan-lattice/`](12-mo507835-phan-lattice/) (`NOTES.md`, `phan_periodic.py`, `colab_phan_gpu.ipynb`).

---

## Precise scope

- Track `05`: Lean 4 checks pure polynomial-ring certificates for $m = 3, 4, 5$; arbitrary $2 \le m \le n$ is proved by mathematical induction in [`05-mo476077-johnston/PROOF.md`](05-mo476077-johnston/PROOF.md).
- Track `06`: Lean 4 formally proves exact equivalence with literal `{213, 231}`-avoidance (`s213_231_literal_eq`), the $3n - 7$ convergence bound (`berlow_convergence_3n_minus_7`, $n \ge 3$), and full periodic-point classification (`berlow_conjecture_5_1_213_231`, $n \ge 1$) for $T = \{213, 231\}$.
- Track `10` covers $T = \{132, 213\}$ / $\{231, 312\}$; general period $\ge 4$ for $n \ge 13$ remains open.
- Tracks `11` and `12` explicitly state their settled cases and open gaps inside their `NOTES.md` files.

## Primary sources

- J. Grytczuk, B. Pawlik, M. Pleszczynski, *Variations on shuffle squares*, https://arxiv.org/abs/2308.13882v2 (Tracks `01`, `09`)
- N. Johnston, MathOverflow #476077, https://mathoverflow.net/questions/476077/bounding-elementary-symmetric-polynomials-away-from-zero (Track `05`)
- K. Berlow, *Restricted stacks as functions*, https://arxiv.org/abs/2008.01164 (Tracks `06`, `10`)
- O. Zhang, *The Order of the (123, 132)-Avoiding Stack Sort*, https://arxiv.org/abs/2405.01854 (Tracks `06`, `10`)
- R. P. Stanley, MathOverflow #475478, https://mathoverflow.net/questions/475478 & https://arxiv.org/html/2511.08969#S5 (Track `11`)
- V. Phan, MathOverflow #507835, https://mathoverflow.net/questions/507835 (Track `12`)
- OEIS sequences [A382427](https://oeis.org/A382427), [A381717](https://oeis.org/A381717), [A377090](https://oeis.org/A377090), [A384890](https://oeis.org/A384890), [A384350](https://oeis.org/A384350), [A383093](https://oeis.org/A383093), [A323774](https://oeis.org/A323774) (Tracks `02`, `03`, `04`, `07`, `08`)
