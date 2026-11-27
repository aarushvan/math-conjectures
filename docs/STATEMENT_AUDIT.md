# Statement Faithfulness Audit

[Home](../README.md) · [Full catalogue](../CONTENTS.md) · [Verification guide](verification.md) · [Lean status](lean-status.md)

In formal verification, a compiling proof only matters if the Lean 4 theorem statement matches the original mathematical conjecture without weakening quantifiers, excluding corner cases, or swapping in a buggy definition. This audit maps each primary source verbatim to its exact Lean 4 symbols.

---

## Track 01: Dihedral Shuffle Squares for Ternary Words ✅

- **Source:** J. Grytczuk, B. Pawlik, and M. Pleszczynski, *Variations on shuffle squares* ([arXiv:2308.13882v2](https://arxiv.org/abs/2308.13882v2), Section 2.3, Conjecture 2): *"Every even ternary word of length $2n$ is a shuffle $\gamma$-square for some dihedral permutation $\gamma \in D_n$."*
- **Lean file:** [`01-dihedral-shuffle-squares/DihedralShuffleDisproof.lean`](../01-dihedral-shuffle-squares/DihedralShuffleDisproof.lean)
- **Definition mapping:**
  - **Even ternary word of length $2n$:** `W_n n : List (Fin 3)` has alphabet `Fin 3 = {0, 1, 2}`, exact length `(W_n n).length = 2 * n` (`W_n_length`), and even symbol counts `2*n - 4`, `2`, `2` (`W_n_even`).
  - **Disjoint length-$n$ subsequence partition:** `splitTrue mask W` and `splitFalse mask W` over an unrestricted `mask : List Bool` of length `2 * n` with both halves required to have length `n`.
  - **Dihedral group $D_n$:** `DihedralPerm n` has both rotations `rot k` ($i \mapsto (i + k) \bmod n$) and reflections `refl k` ($i \mapsto (k + n - (i \bmod n)) \bmod n$), with bijectivity on `{0, ..., n-1}` proved in `applyIdx_perm` and permutation preservation proved in `DihedralPerm.apply_perm`.
  - **Dihedral similarity:** `IsDihedralShuffleSquare n W` allows *either* `splitFalse mask W = γ.apply (splitTrue mask W)` *or* `splitTrue mask W = γ.apply (splitFalse mask W)`.
- **Verified conclusions:** `dihedral_conjecture_false` proves `¬ IsDihedralShuffleSquare n (W_n n)` universally for every `n ≥ 4`, and `minimal_counterexample_00011022` instantiates `n = 4` (`[0, 0, 0, 1, 1, 0, 2, 2]`). No edge cases are excluded ($n \le 3$ has `0` counterexamples as verified exhaustively in [`verify_dihedral.py`](../01-dihedral-shuffle-squares/verify_dihedral.py)).

---

## Track 02: Constant-Block vs. Distinct Run-Sum Partitions ✅

- **Source:** Gus Wiseman, [OEIS A382427](https://oeis.org/A382427) / [OEIS A381717](https://oeis.org/A381717) (2025): *"A partition of positive integers can be partitioned into constant blocks with pairwise distinct sums iff it admits a permutation whose maximal constant runs have pairwise distinct sums."*
- **Lean file:** [`02-oeis-a382427-a381717/WisemanA382427.lean`](../02-oeis-a382427-a381717/WisemanA382427.lean)
- **Definition mapping:**
  - **Integer partition:** Arbitrary `parts : List Nat` paired with positivity `∀ x ∈ parts, x > 0`, unordered up to `List.Perm`.
  - **Constant-block decomposition with distinct sums:** `bs : List Block` (each `Block` has `val > 0` and `count > 0`) whose expanded multiset `(bs.flatMap Block.expand).Perm parts` matches `parts` and `(bs.map Block.sum).Nodup` (`DistinctSums bs`).
  - **Permutation with distinct maximal run sums:** `w : List Nat` with `w.Perm parts` and `((maxRuns w).map (fun r => r.1 * r.2)).Nodup`, where `maxRuns` groups strictly maximal contiguous equal-value runs.
- **Verified conclusions:** `wiseman_A382427_iff` proves the full iff equivalence for all nonempty and empty positive-integer lists (and `wiseman_A381717_iff` proves the negated complement equivalence). Cross-checked exhaustively across all partitions for $n = 0 \dots 22$ in [`verify_a382427.py`](../02-oeis-a382427-a381717/verify_a382427.py).

---

## Track 04: Anti-Run Constant-Run Lengths in OEIS A384890 ✅

- **Source:** Gus Wiseman, [OEIS A384890](https://oeis.org/A384890) (2025): *"Number of maximal anti-runs (increasing by more than 1) in the binary indices of $n$. Comment: Do all constant runs in this sequence have lengths 1, 2, or 3?"*
- **Lean file:** [`04-oeis-a384890/WisemanA384890.lean`](../04-oeis-a384890/WisemanA384890.lean)
- **Definition mapping & explicit scope note:**
  - **Bitwise characterization:** For $n = 0$, $I(0) = \emptyset$ has `0` anti-runs (`a 0 = 0`). For $n \ge 1$, every adjacent step in the sorted 1-based binary indices $i_1 < i_2 < \dots < i_m$ is either an anti-run break ($i_{j+1} - i_j > 1$, starting a new maximal anti-run) or a non-break ($i_{j+1} - i_j = 1$, i.e., an adjacent `11` pair in binary). Since the first element always starts a maximal anti-run, the total count of maximal anti-runs is $1 + \#\{j : i_{j+1} - i_j = 1\} = 1 + \operatorname{popcount}(n \mathbin{\&} \lfloor n/2 \rfloor)$.
  - **In Lean 4:** `def a (n : Nat) := if n = 0 then 0 else 1 + adjOnes n` together with `adjOnes_eq_popcount_and_shr` (`adjOnes n = popcount (n &&& (n >>> 1))`). Note that the elementary bijection between bit-index gaps $i_{j+1} - i_j = 1$ and `adjOnes n` is proved in [`04-oeis-a384890/PROOF.md`](../04-oeis-a384890/PROOF.md) and independently verified on all 87 live OEIS terms and $1 \le n \le 20{,}000$ in [`verify_a384890.py`](../04-oeis-a384890/verify_a384890.py) (`a384890_direct`).
- **Verified conclusions:** `wiseman_A384890_no_run_len_4` proves `¬ (a n = a (n+1) ∧ a (n+1) = a (n+2) ∧ a (n+2) = a (n+3))` for every `n : Nat`, while `witness_run_len_1_and_2` and `witness_run_len_3` exhibit runs of lengths `1`, `2`, and `3`.

---

## Track 05: Elementary Symmetric Polynomial Lower Bounds (MO #476077) 🟡 Partial

- **Source:** Nathaniel Johnston, [MathOverflow #476077](https://mathoverflow.net/questions/476077/bounding-elementary-symmetric-polynomials-away-from-zero) (2024): *"For real $x \in \mathbb{R}^n$ with $x_i \le \frac{1}{m-1}$, $e_1(x) = 1$, and $e_j(x) \ge 0$ ($1 \le j \le m$), prove $e_k(x) \ge \binom{m-1}{k}/(m-1)^k$ for $1 \le k < m$."*
- **Lean file:** [`05-mo476077-johnston/JohnstonEsymmM345.lean`](../05-mo476077-johnston/JohnstonEsymmM345.lean) (🟡 Partial)
- **What IS formalized in Lean 4:** Exact integer polynomial-ring identities (`identity_m3_e2`, `identity_m4_e2`, `identity_m4_e3`, `identity_m5_e2`, `identity_m5_e3`, `identity_m5_e4`, `m5_quadratic_pos`) over symbolic `e2 e3 e4 e5 : Int`, expressing multiples of $e_k(y) - \binom{m-1}{k}$ as positive combinations of $e_m$ and quadratic-weighted power sums `S21`, `S22`, `S23`. Because polynomial identities over `Int` hold identically in $\mathbb{Z}[e_2, \dots, e_m]$, they lift directly to $\mathbb{R}$.
- **What is NOT yet formalized in Lean 4 (proved in [`05-mo476077-johnston/PROOF.md`](../05-mo476077-johnston/PROOF.md)):**
  1. Connecting `S2r` to $\sum_{i=1}^n y_i^2 (1 - y_i)^r \ge 0$ over $\mathbb{R}^n$ for $y_i \le 1$ via Newton's identities.
  2. Arbitrary-$m$ compactness, Rolle/Hermite-Biehler/Gauss-Lucas Strong Dropping Lemma for boundary minimizers ($y_i = 1$).
  3. Newton's inequalities and the IVT 3-variable cubic perturbation eliminating interior minimizers ($y_i < 1$).

---

## Track 06: Periodic Points of `{213, 231}`-Avoiding Stack Sorting ✅

- **Source:** Katalin Berlow, *Restricted stacks as functions* ([arXiv:2008.01164v2](https://arxiv.org/abs/2008.01164), Conjecture 5.1); Owen Zhang ([arXiv:2405.01854](https://arxiv.org/abs/2405.01854), Conjecture 4.2): under the top-to-bottom stack convention and right-greedy push rule, the only periodic points of $s_{\{213, 231\}} : S_n \to S_n$ are $\mathrm{id}_n$ and $\mathrm{id}_n^r$.
- **Lean file:** [`06-berlow-stack-sorting/BerlowStackSorting.lean`](../06-berlow-stack-sorting/BerlowStackSorting.lean)
- **Definition mapping:**
  - **Literal `{213, 231}` pattern avoidance on stack + next element:** `hasPairBetween x stack` and `has213or231 x stack` directly check for $3$-tuples violating `213` or `231` when placing `x` on `stack` (`avoids213_231 x stack = !has213or231 x stack`); `popLoopLit`, `runStackLit`, `s213_231_literal`, and `iterSortLit` define iterated sorting with this literal rule.
  - **Equivalence with min/max transition:** `s213_231_literal_eq` proves `s213_231_literal xs = s213_231 xs` (`min(S) < x < max(S)`) for every `xs : List Nat`.
  - **Symmetric group $S_n$:** `idPerm n` (`[1, ..., n]`), `revPerm n` (`[n, ..., 1]`), and `IsPerm n π` (`π.Perm (idPerm n)`).
- **Verified conclusions:**
  - `s213_231_last_eq_head` proves the bottom-of-stack elimination lemma for arbitrary `List Nat` inputs.
  - `berlow_convergence_3n_minus_7` proves `iterSortLit (3 * n - 7) π = idPerm n ∨ iterSortLit (3 * n - 7) π = revPerm n` for all `n ≥ 3` and `IsPerm n π`.
  - `berlow_conjecture_5_1_213_231` proves that for all `n ≥ 1`, `IsPerm n π`, and period `p ≥ 1`, `iterSortLit p π = π → π = idPerm n ∨ π = revPerm n`.
  - Cross-checked exhaustively through $S_7$ in [`verify_berlow.py`](../06-berlow-stack-sorting/verify_berlow.py).

---

## Track 09: Binary Shuffle Anti-Squares ✅

- **Source:** J. Grytczuk, B. Pawlik, and M. Pleszczynski, *Variations on shuffle squares* ([arXiv:2308.13882v2](https://arxiv.org/abs/2308.13882v2), Section 2.2, Conjecture 1): *"There exists a shuffle anti-square of length $2n$ for every $n \ge 12$."*
- **Lean file:** [`09-shuffle-antisquares/ShuffleAntiSquares.lean`](../09-shuffle-antisquares/ShuffleAntiSquares.lean)
- **Definition mapping:**
  - **Binary alphabet & even word of length $2n$:** `W t : List Bool` (`t = n - 12`), proved to satisfy `(W (n - 12)).length = 2 * n`, `(W (n - 12)).count true = 12`, and `(W (n - 12)).count false = 2 * n - 12` for every `n ≥ 12`.
  - **Shuffle square:** `IsShuffleSplit w u v` partitions `w` bit-by-bit (`left` / `right` constructors) into two disjoint subsequences `u` and `v`; `IsShuffleSquare w` asserts `∃ u, IsShuffleSplit w u u`.
  - **Cyclic rotation & shuffle anti-square:** `rotate w s = w.drop s ++ w.take s`; `IsShuffleAntiSquare w` asserts `∀ s < w.length, ¬ IsShuffleSquare (rotate w s)`, covering every cyclic shift `0 ≤ s < 2n`.
- **Verified conclusion:** `grytczuk_conjecture_1_true` universally proves length, even binary counts, and `IsShuffleAntiSquare (W (n - 12))` for every `n ≥ 12`, checking all `12` cyclic cut templates and all `568` integer Farkas dual certificates (`t0_ok`..`t11_ok`) inside the Lean 4 kernel.
