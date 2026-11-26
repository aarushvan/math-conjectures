# 11. Stanley Bivariate Monomial Positivity

Verified partial theorems and exact degree-8 integer checks for Richard P. Stanley's bivariate homomorphism positivity conjecture ([MathOverflow #475478](https://mathoverflow.net/questions/475478) / [arXiv:2511.08969](https://arxiv.org/html/2511.08969#S5), Conjecture 5.2).

For all degrees $d \ge 0$, proves dominance vanishing ($c^\lambda_{\alpha,\beta} = 0$ unless $\alpha, \beta \preceq \lambda$) and principal-slice nonnegativity ($c^\lambda_{\lambda,\beta} = A_{\beta\lambda} \ge 0$, $c^\lambda_{\lambda,\lambda} = 1$). Exact integer computation confirms nonnegativity across all `15,859` ordered classes through $d = 8$ (`0` negatives; all `10,535` zeros matching dominance). General interior positivity ($\alpha, \beta \prec \lambda$) remains open.

- [Partial proofs and exact degree table](NOTES.md)
- [Exact integer matrix verifier ⬜](stanley_verify.py)

Run `python3 stanley_verify.py --degree 8`.
