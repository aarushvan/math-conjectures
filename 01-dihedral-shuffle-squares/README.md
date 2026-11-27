# 01. Dihedral Shuffle Squares for Ternary Words

Disproof of Conjecture 2 from Grytczuk, Pawlik, and Pleszczynski, *Variations on shuffle squares* ([arXiv:2308.13882v2](https://arxiv.org/abs/2308.13882v2), Section 2.3), for every even length $2n \ge 8$ ($n \ge 4$).

The explicit family $W_n = \mathtt{0}^{2n-5}\mathtt{11022}$ always forces any balanced length-$n$ partition to split into $\mathtt{0}^{n-2}\mathtt{12}$ and $\mathtt{0}^{n-3}\mathtt{102}$, whose cyclic adjacent-$\mathtt{00}$ counts $n - 3 \ne n - 4$ forbid dihedral equivalence. Exhaustive search confirms `0` counterexamples at $n = 3$ and a unique $S_3 \times D_8$ orbit of `48` counterexamples at $n = 4$ represented by `00011022`.

- [Complete proof](PROOF.md)
- [Lean 4 formalization (`dihedral_conjecture_false`, `minimal_counterexample_00011022`) ✅](DihedralShuffleDisproof.lean)
- [Exhaustive Python verifier](verify_dihedral.py)
- [Statement Audit](../docs/STATEMENT_AUDIT.md#track-01-dihedral-shuffle-squares-for-ternary-words-)

Run `lean DihedralShuffleDisproof.lean && python3 verify_dihedral.py` (with Lean `v4.36.0` and Python 3).

## Statement Audit

- **Alphabet & length:** `W_n n : List (Fin 3)` has proved length `2 * n` (`W_n_length`) and even counts `(2*n - 4, 2, 2)` (`W_n_even`).
- **Partition & dihedral group:** `IsDihedralShuffleSquare` quantifies over all boolean splits (`splitTrue` / `splitFalse`) and both rotations and reflections in `DihedralPerm n` (`rot k`, `refl k`, bijection proved in `applyIdx_perm`), matching `arXiv:2308.13882v2` Section 2.1/2.3 verbatim.
