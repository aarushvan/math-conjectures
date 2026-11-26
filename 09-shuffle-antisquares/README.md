# 09. Binary Shuffle Anti-Squares

Complete proof of Conjecture 1 from Grytczuk, Pawlik, and Pleszczynski, *Variations on shuffle squares* ([arXiv:2308.13882v2](https://arxiv.org/abs/2308.13882v2), Section 2.2), for every integer $n \ge 12$.

Every cyclic shift of the explicit family $W_n = \mathtt{0}^{n-7}\mathtt{10}^2\mathtt{1}^4\mathtt{0}^{n-8}\mathtt{1}^3\mathtt{01}^4$ falls into one of `12` symbolic cut templates and `568` linear flow systems over $(t = n - 12, x_j, y_j) \ge 0$, every one certified infeasible over $\mathbb{R}_{\ge 0}$ for all $t \ge 0$ by an exact integer Farkas dual in $\{-1, 0, 1\}^{11}$. Together with [Track 01](../01-dihedral-shuffle-squares/), both Conjectures 1 and 2 of `arXiv:2308.13882v2` are completely resolved.

- [Complete proof](PROOF.md)
- [Lean 4 end-to-end formalization (`grytczuk_conjecture_1_true` for all $n \ge 12$) ✅](ShuffleAntiSquares.lean)
- [Exact Farkas & DP Python verifier](verify_antisquares.py)

Run `lean ShuffleAntiSquares.lean && python3 verify_antisquares.py`.
