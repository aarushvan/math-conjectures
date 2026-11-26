# MathOverflow #476077 Computational Search Report

> **Historical note:** This report documents the preliminary computational sweep and adversarial search that preceded the complete general proof (for all $2 \le m \le n$) now presented in [`../PROOF.md`](../PROOF.md).

**Problem:** Nathaniel Johnston, *"Bounding elementary symmetric polynomials away from zero"* ([MathOverflow #476077](https://mathoverflow.net/questions/476077)).

**Rescaled Statement ($d = m - 1$, $y_i = d x_i$):**
For $2 \le m \le n$ and $y \in \mathbb{R}^n$ satisfying:
1. $y_i \le 1$ for all $i = 1, \dots, n$,
2. $e_1(y) = d$,
3. $e_j(y) \ge 0$ for all $1 \le j \le m$,

conjecturally $e_k(y) \ge \binom{d}{k}$ for all $1 \le k \le d$, with equality at $y^* = (1^d, 0^{n-d})$.

## Tools Built and Verified

1. **Exact Rational Verifier:** `05-mo476077-johnston/python/verify_mo476077.py`
   - Uses `fractions.Fraction` exact arithmetic on $\prod_{i=1}^n (1 + t y_i)$.
   - Command: `python3 05-mo476077-johnston/python/verify_mo476077.py --self-test`
   - Result: `verify_mo476077.py self-tests PASSED.`

2. **High-Speed C++20 Search Engine:** `05-mo476077-johnston/cpp/mo476077_search.cpp`
   - Compiled with: `clang++ -O3 -std=c++20 -pthread -march=native 05-mo476077-johnston/cpp/mo476077_search.cpp -o 05-mo476077-johnston/cpp/mo476077_search`

## Search Results

### 1. Structured Block & Poisson-Limit Sweep (`--blocks 3 25`)
- **Elapsed time:** `5.3624s` (10 threads)
- **Families searched:**
  - **3-block vectors** $y = (1^a, u^b, (-v)^c)$ for $m = 3 \dots 25$, $c \in \{1..6\}$, $a \in [0, m+c]$, $b \in \{1..2m, 3m, 5m, 10m\}$, solving $e_m(v) = 0$ and $e_{m-1}(v) = 0$ via grid bracketing + 65-step bisection.
  - **Continuous Poisson limits** $F(t) = (1+t)^a e^{\lambda t} (1 - vt)^c$ with $\lambda = d - a + cv$ for $m = 3 \dots 25$, $c \in \{1..8\}$, $a \in [0, m+c]$.
  - **4-block vectors** $(1^a, u_1^{b_1}, u_2^{b_2}, (-v)^c)$ and $(1^a, u^b, (-v_1)^{c_1}, (-v_2)^{c_2})$ for $m = 3 \dots 14$.
- **Outcome:** **0 counterexamples found across all $m = 3 \dots 25$.** Every family achieved `min_ratio = 1` (`gap = 0`) strictly at the boundary $v = 0$ ($y^* = (1^d, 0^{n-d})$).

### 2. Multi-Start Constrained Optimization (`--opt 6 10`)
- **Elapsed time:** `0.0605s` (10 threads)
- **Scope:** $m \in \{6, 7, 8, 9, 10\}$, $n \in \{m+1, m+2, m+3, m+4, m+6\}$, target $k \in \{2, \lfloor m/2 \rfloor, d-1, d\}$, 180 restarts per $(m, n, k)$ (total 80 `(m, n, k)` combinations, 14,400 optimization trajectories) using augmented-Lagrangian $O(m)$-delta coordinate-pair updates followed by strict-feasibility projection.
- **Outcome:** **0 counterexamples found.** All minimum ratios satisfied `min_ratio >= 1` (minimum gaps for $n = m+1$ hit $0$ within `long double` roundoff $\sim -7.1 \times 10^{-15}$ at $y^*$; for larger $n$, best feasible ratios remained $\ge 1.0000000$).

## Conclusion from Computational Phase
Both structured algebraic families (up to $m = 25$) and unconstrained numerical minimization with negative entries (for $m = 6 \dots 10$) supported MathOverflow #476077 in full generality; the complete general proof for all $2 \le m \le n$ and $1 \le k < m$ (together with uniqueness of the equality case) was subsequently completed and audited in [`../PROOF.md`](../PROOF.md).
