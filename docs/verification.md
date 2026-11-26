# Verification Guide

[Home](../README.md) · [Full catalogue](../CONTENTS.md) · [Lean status](lean-status.md)

Every resolution and computational claim in this repository can be reproduced from a single script in the repository root.

## Prerequisites

- **Lean 4:** `leanprover/lean4:v4.36.0` (automatically selected by [`lean-toolchain`](../lean-toolchain) if `elan` is installed). Zero external libraries or Mathlib downloads are required; every `.lean` file imports only Lean 4 core `Init`.
- **Python:** Python 3.9+ using the standard library only (no `pip` packages required for `verify_all.sh`).
- **C / C++:** `clang` and `clang++` with C++20 and pthreads support.

## Full Suite

```bash
bash verify_all.sh
```

`verify_all.sh` runs five sequential stages and exits non-zero if any step fails:
1. Scans all 6 `.lean` files for `sorry`, `admit`, `axiom`, or `unsafe`.
2. Scans all source and Markdown files across the repository for forbidden U+2014 em dashes.
3. Kernel-compiles all 6 Lean 4 files directly under `lean` and checks `#print axioms` output for `sorryAx`.
4. Executes all 12 Python verifiers across Tracks `01` to `12`.
5. Compiles with warnings-as-errors (`clang -O3 -Wall -Wextra -Werror`) / C++20 (`clang++ -O3 -std=c++20 -pthread -march=native`) and runs the two C/C++ verifiers.

## Per-Track Verification Scope

| Track | Command | Verified Scope |
| :---: | :--- | :--- |
| **01** | `lean 01-dihedral-shuffle-squares/DihedralShuffleDisproof.lean && python3 01-dihedral-shuffle-squares/verify_dihedral.py` | Lean proof for all $n \ge 4$; exhaustive $n = 3$ (`90` words) and $n = 4$ (`1260` words, `48` failures, 1 canonical orbit) |
| **02** | `lean 02-oeis-a382427-a381717/WisemanA382427.lean && python3 02-oeis-a382427-a381717/verify_a382427.py` | Full Lean iff theorems; exhaustive partition check for $n = 0 \dots 22$ matching live OEIS |
| **03** | `clang -O3 -Wall -Wextra -Werror 03-oeis-a377090/verify_a377090.c -lm -o 03-oeis-a377090/verify_a377090 && ./03-oeis-a377090/verify_a377090` | Exact OEIS `a(0..39)` and Hasler record cross-check, then full sweep to $n = 10^7$ finding `361` violations |
| **04** | `lean 04-oeis-a384890/WisemanA384890.lean && python3 04-oeis-a384890/verify_a384890.py` | Full Lean proof + popcount check ($n \le 20{,}000$), 87 OEIS terms, and run-length scan ($n \le 10^6$) |
| **05** | `lean 05-mo476077-johnston/JohnstonEsymmM345.lean && python3 05-mo476077-johnston/python/verify_mo476077.py --self-test && python3 05-mo476077-johnston/python/verify_identities_m345.py` | Lean ring certificates ($m = 3, 4, 5$); exact rational verifier + cubic perturbation test ($m = 3 \dots 8$); C++20 block search (`--blocks 3 12`) |
| **06** | `lean 06-berlow-stack-sorting/BerlowStackSorting.lean && python3 06-berlow-stack-sorting/verify_berlow.py` | Lean formalization of Lemma 3 (`s213_231_last_eq_head`) + $S_4, S_5$ witnesses; exhaustive $S_3 \dots S_7$ Python check |
| **07** | `python3 07-oeis-a384350/verify_a384350.py` | Exhaustive subset-by-subset verification for $n = 0 \dots 11$ matching live OEIS A384350 |
| **08** | `python3 08-oeis-a383093/verify_a383093.py` | Exact Mobius identity verification for $n = 0 \dots 24$ matching live OEIS A383093 and A323774 |
| **09** | `lean 09-shuffle-antisquares/ShuffleAntiSquares.lean && python3 09-shuffle-antisquares/verify_antisquares.py` | Full Lean end-to-end proof (`grytczuk_conjecture_1_true` for $n \ge 12$, `568` Farkas duals); DP check ($n = 12 \dots 45$) + brute-force oracle ($2m \le 10$) |
| **10** | `python3 10-berlow-stack-sorting-132-213/verify_berlow_132_213.py --through-12` | Literal triple-check dynamics on $S_1 \dots S_7$ (`5040` perms); reduced orbit exhaustion through $n = 12$ (`578,290` states at $n = 12$) |
| **11** | `python3 11-mo475478-stanley-bivariate/stanley_verify.py --degree 8` | Exact integer matrix verification of all `15,859` ordered classes through degree $d = 8$ |
| **12** | `python3 12-mo507835-phan-lattice/phan_periodic.py --dimensions 2 3 4 --periods 3 4 6 --steps 6000 --restarts 3` | Quotient $C_4$-free checker, exact $n = 4$ $\mathbb{F}_2^2$-parity construction, and periodic search (`colab_phan_gpu.ipynb` uses PyTorch for $n = 5$) |
