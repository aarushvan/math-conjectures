# Lean 4 Verification Status

[Home](../README.md) · [Full catalogue](../CONTENTS.md) · [Verification guide](verification.md) · [Statement audit](STATEMENT_AUDIT.md)

All formalizations target `leanprover/lean4:v4.36.0` (pinned in [`lean-toolchain`](../lean-toolchain)), import only Lean 4 core `Init` (zero Mathlib or third-party dependencies), contain zero `sorry`, `admit`, custom `axiom`, or `unsafe` tokens, and pass `#print axioms` showing only standard Lean core axioms (`propext`, `Classical.choice`, `Quot.sound` as needed).

## Summary

| Track | Module | Status | Main Kernel-Checked Declarations | Checked Scope |
| :---: | :--- | :---: | :--- | :--- |
| **01** | [`DihedralShuffleDisproof.lean`](../01-dihedral-shuffle-squares/DihedralShuffleDisproof.lean) | ✅ | `dihedral_conjecture_false`, `minimal_counterexample_00011022` | Full infinite counterexample family $W_n$ for all $n \ge 4$ (`2n >= 8`) and minimal $n = 4$ counterexample |
| **02** | [`WisemanA382427.lean`](../02-oeis-a382427-a381717/WisemanA382427.lean) | ✅ | `wiseman_A382427_iff`, `wiseman_A381717_iff` | Complete iff characterization for all nonempty positive-integer lists via Pigeonhole merge (`pigeonhole_reduce`) and conflict-free interleaving (`interleave_blocks`) |
| **04** | [`WisemanA384890.lean`](../04-oeis-a384890/WisemanA384890.lean) | ✅ | `adjOnes_eq_popcount_and_shr`, `wiseman_A384890_no_run_len_4`, `witness_run_len_1_and_2`, `witness_run_len_3` | Exact bitwise popcount identity and complete proof that no constant run of length $\ge 4$ exists for any $n : \mathbb{N}$ |
| **05** | [`JohnstonEsymmM345.lean`](../05-mo476077-johnston/JohnstonEsymmM345.lean) | 🟡 | `identity_m3_e2`, `identity_m4_e2`, `identity_m4_e3`, `identity_m5_e2`, `identity_m5_e3`, `identity_m5_e4`, `m5_quadratic_pos` | Pure polynomial-ring identities proving the $m = 3, 4, 5$ cases without calculus; general $2 \le m \le n$ proved in [`PROOF.md`](../05-mo476077-johnston/PROOF.md) |
| **06** | [`BerlowStackSorting.lean`](../06-berlow-stack-sorting/BerlowStackSorting.lean) | ✅ | `s213_231_literal_eq`, `berlow_convergence_3n_minus_7`, `berlow_conjecture_5_1_213_231`, `s213_231_last_eq_head`, `cycle_S4`, `worst_case_S5` | Full end-to-end proof for all $n \ge 1$ and $T = \{213, 231\}$, proving exact equivalence between the literal pattern-avoiding stack (`has213or231`) and `min(S) < x < max(S)`, the $3n - 7$ convergence bound ($n \ge 3$), and periodic-point classification |
| **09** | [`ShuffleAntiSquares.lean`](../09-shuffle-antisquares/ShuffleAntiSquares.lean) | ✅ | `grytczuk_conjecture_1_true` | Complete end-to-end proof that `W(n - 12)` has length $2n$, `12` ones, and is a shuffle anti-square for every $n \ge 12$, checking all `568` Farkas duals in the Lean kernel (`t0_ok`..`t11_ok`) |

## Tracks Without Lean Formalizations (⬜)

Tracks `03`, `07`, `08`, `10`, `11`, and `12` are verified in prose and executable Python or C verifiers (see [the verification guide](verification.md)).
