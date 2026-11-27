# Solved Conjectures in Combinatorics, Algebra & Number Theory

[![Verify Proofs and Scripts](https://github.com/aarushvan/math-conjectures/actions/workflows/verify.yml/badge.svg)](https://github.com/aarushvan/math-conjectures/actions/workflows/verify.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)

Mathematical proofs, counterexamples, and partial results in combinatorics, symmetric functions, and number theory, paired with zero-dependency Lean 4 (`v4.36.0`) formalizations and reproducible exact verification scripts.

Authored by **Aarush Vankadari (`@aarushvan`)** and **Neon**.

[Full catalogue](CONTENTS.md) · [Verification](docs/verification.md) · [Lean status](docs/lean-status.md) · [Statement audit](docs/STATEMENT_AUDIT.md)

## Complete results

| # | Problem | Source | Verdict | Lean |
| ---: | :--- | :--- | :--- | :---: |
| **1.** | [Dihedral shuffle squares for ternary words](01-dihedral-shuffle-squares/) | [arXiv:2308.13882v2](https://arxiv.org/abs/2308.13882v2), Conj. 2 | Disproved ($2n \ge 8$) | ✅ |
| **2.** | [Constant-block vs. distinct run-sum partitions](02-oeis-a382427-a381717/) | [OEIS A382427](https://oeis.org/A382427) / [A381717](https://oeis.org/A381717) | Proved (all $n$) | ✅ |
| **3.** | [Prime-difference greedy deviation bound](03-oeis-a377090/) | [OEIS A377090](https://oeis.org/A377090) | Disproved ($n \ge 370{,}313$) | ⬜ |
| **4.** | [Anti-run constant-run lengths](04-oeis-a384890/) | [OEIS A384890](https://oeis.org/A384890) | Proved (all $n$) | ✅ |
| **5.** | [Elementary symmetric polynomial lower bounds](05-mo476077-johnston/) | [MathOverflow #476077](https://mathoverflow.net/questions/476077/bounding-elementary-symmetric-polynomials-away-from-zero) | Proved ($2 \le m \le n$) | 🟡 |
| **6.** | [Periodic points of `{213, 231}`-avoiding stack sorting](06-berlow-stack-sorting/) | [arXiv:2008.01164v2](https://arxiv.org/abs/2008.01164), Conj. 5.1 | Proved (all $n \ge 1$) | ✅ |
| **7.** | [Disjoint strict-partition families](07-oeis-a384350/) | [OEIS A384350](https://oeis.org/A384350) | Proved (all $n$) | ⬜ |
| **8.** | [Common-sum block partitions Möbius identity](08-oeis-a383093/) | [OEIS A383093](https://oeis.org/A383093) / [A323774](https://oeis.org/A323774) | Proved (all $n \ge 1$) | ⬜ |
| **9.** | [Binary shuffle anti-squares](09-shuffle-antisquares/) | [arXiv:2308.13882v2](https://arxiv.org/abs/2308.13882v2), Conj. 1 | Proved (all $n \ge 12$) | ✅ |

Numbers (`1.` to `9.` and `10.` to `12.`) are sequential catalogue indices matching repository directory order (`01-` to `12-`), not importance rankings.

- ✅ Fully Lean-verified (end-to-end theorem proved in zero-dependency Lean `v4.36.0` core; zero `sorry`, zero custom axioms).
- 🟡 Partially Lean-verified (core lemma or algebraic sub-cases formalized in Lean `v4.36.0` core; full result proved in prose and checked by exact Python/C/C++ verifiers).
- ⬜ No Lean verification (line-by-line audited proof or disproof with reproducible Python or C verifier).

## Partial results and reductions

| # | Problem | Source | Verified scope | Lean |
| ---: | :--- | :--- | :--- | :---: |
| **10.** | [Periodic points of `{132, 213}`-avoiding stack sorting](10-berlow-stack-sorting-132-213/) | [arXiv:2008.01164v2](https://arxiv.org/abs/2008.01164), Conj. 5.1 | First-return reduction, periods $1$ to $3$ excluded for all $n$, exhausted through $n = 12$; open for $n \ge 13$, period $\ge 4$ | ⬜ |
| **11.** | [Stanley bivariate monomial positivity](11-mo475478-stanley-bivariate/) | [MathOverflow #475478](https://mathoverflow.net/questions/475478) / [arXiv:2511.08969](https://arxiv.org/html/2511.08969#S5), Conj. 5.2 | Dominance vanishing and principal slice proved for all $d \ge 0$; `15,859` classes verified through $d = 8$; interior open | ⬜ |
| **12.** | [Phan three-layer lattice C₄-free density](12-mo507835-phan-lattice/) | [MathOverflow #507835](https://mathoverflow.net/questions/507835) | Upper bound proved for $n = 2, 3, 4$ with exact $\mathbb{F}_2^2$-parity construction at $3/4$ for $n = 4$; open for $n \ge 5$ | ⬜ |

## Layout

- `01-.../` to `09-.../`: complete proofs and counterexamples (`PROOF.md` or `DISPROOF.md`, `.lean` formalizations, and `.py` / `.c` / `.cpp` verifiers).
- `10-.../` to `12-.../`: verified partial theorems, structural reductions, and computational searches (`PARTIAL_PROOF.md` or `NOTES.md`, verifiers, and GPU notebook).
- `docs/`: [verification guide](docs/verification.md), [Lean verification status](docs/lean-status.md), and [statement faithfulness audit](docs/STATEMENT_AUDIT.md).
- `verify_all.sh` and `lean-toolchain`: pinned `leanprover/lean4:v4.36.0` and one-command full verification runner.

## Verification

Requires Lean `leanprover/lean4:v4.36.0` (managed automatically by `elan` via `lean-toolchain`; zero Mathlib downloads), Python 3.9+ (standard library only), and `clang` / `clang++`:

```bash
bash verify_all.sh
```

See [the verification guide](docs/verification.md) for per-track commands and [the Lean status ledger](docs/lean-status.md) for every formal theorem signature and axiom check.

## Methodology and Statement Faithfulness

- **Human-AI workflow:** Aarush Vankadari directs conjecture selection, reviews every mathematical argument and boundary condition, and maintains the repository. **Neon** assists with proof discovery, Lean 4 formalization, and verifier engineering.
- **Independent verification:** Every `.lean` proof compiles standalone against Lean `v4.36.0` core `Init` (zero Mathlib) and runs `#print axioms` in CI to ensure zero `sorryAx` or custom axioms, while every computational track includes an independent exact Python or C/C++ verifier.
- **Statement faithfulness:** [docs/STATEMENT_AUDIT.md](docs/STATEMENT_AUDIT.md) maps each original arXiv, MathOverflow, or OEIS problem statement verbatim to the formalized Lean 4 definitions and theorems, explicitly noting any partial-track scope boundaries (`🟡`).

## License

Code, Lean 4 formalizations, verification scripts, and workflows are licensed under the [MIT License](LICENSE). Mathematical exposition and proof notes (`*.md`) are licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

<details>
<summary>Citation and sources</summary>

If you use or cite this collection, please credit **Aarush Vankadari (`@aarushvan`)** and **Neon**, and cite the original conjecture source separately (see [`CONTENTS.md`](CONTENTS.md#primary-sources) and [`CITATION.cff`](CITATION.cff)).

Suggested BibTeX:

```bibtex
@misc{vankadari2026mathconjectures,
  author       = {Vankadari, Aarush and {Neon}},
  title        = {Solved Conjectures in Combinatorics, Algebra & Number Theory},
  year         = {2026},
  howpublished = {GitHub repository},
  url          = {https://github.com/aarushvan/math-conjectures},
  note         = {Proofs, counterexamples, zero-dependency Lean 4 formalizations, and reproducible verifiers}
}
```

</details>
