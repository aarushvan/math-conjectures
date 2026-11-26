# Partial Proofs & Exact Verification: Stanley's Bivariate Monomial Positivity (MO #475478 / arXiv:2511.08969 Conj. 5.2)

- **Sources:**
  - Richard P. Stanley, [MathOverflow #475478](https://mathoverflow.net/questions/475478).
  - *arXiv:2511.08969*, [Conjecture 5.2](https://arxiv.org/html/2511.08969#S5).
- **Conjecture:** Let $\Phi : \Lambda \to \Lambda_x \otimes \Lambda_y$ be the ring homomorphism defined on elementary symmetric functions by $\Phi(e_r) = e_r(x)\, e_r(y)$. Then for every partition $\lambda \vdash d$, the bivariate expansion
  $$\Phi(m_\lambda) = \sum_{\alpha, \beta \vdash d} c^\lambda_{\alpha, \beta}\, m_\alpha(x)\, m_\beta(y)$$
  has nonnegative integer coefficients ($c^\lambda_{\alpha, \beta} \ge 0$).
- **Scope & Status:** **Verified Partial Results (Open in General).**
  1. **Dominance vanishing theorem (all $d \ge 0$):** Proved $c^\lambda_{\alpha, \beta} = 0$ whenever $\alpha \not\preceq \lambda$ or $\beta \not\preceq \lambda$ in dominance order.
  2. **Principal-slice positivity theorem (all $d \ge 0$):** Proved $c^\lambda_{\lambda, \beta} = c^\lambda_{\beta, \lambda} = A_{\beta\lambda} \ge 0$ (equal to the count of binary $0/1$ matrices with row sums $\beta$ and column sums $\lambda'$), and $c^\lambda_{\lambda, \lambda} = 1$.
  3. **Exact verification through degree $d = 8$:** Checked all $15{,}859$ ordered classes $(\lambda, \alpha, \beta)$ via [`stanley_verify.py`](stanley_verify.py) (zero negative coefficients; $10{,}535$ zeros, all explained by dominance; $5{,}324$ strictly positive).
  - **Open Gap:** Proving $c^\lambda_{\alpha, \beta} \ge 0$ in the interior region where both $\alpha \prec \lambda$ and $\beta \prec \lambda$.

---

## Algebraic Structure & Partial Proofs

Write the elementary-to-monomial transition matrix at degree $d$ as $e_{\mu'} = \sum_{\alpha \vdash d} A_{\alpha\mu} m_\alpha$, where $\mu'$ is the conjugate of $\mu$ and $A_{\alpha\mu} \ge 0$ counts binary matrices with row sums $\alpha$ and column sums $\mu'$. By Gale-Ryser / conjugate Ferrers diagram positivity:
1. $A_{\alpha\mu} \ne 0 \implies \alpha \preceq \mu$ in dominance order, and $A_{\mu\mu} = 1$.
2. Because $A$ is unit upper-triangular in any linear extension of dominance order, its inverse satisfies $m_\lambda = \sum_{\mu \preceq \lambda} b_{\lambda\mu} e_{\mu'}$ with $b_{\lambda\lambda} = 1$ (though $b_{\lambda\mu}$ is alternating in sign).

Applying $\Phi(e_{\mu'}) = e_{\mu'}(x) e_{\mu'}(y)$ yields the exact matrix representation of the coefficient tensor for fixed $\lambda$:
$$c^\lambda_{\alpha, \beta} = \sum_{\mu \preceq \lambda} b_{\lambda\mu}\, A_{\alpha\mu}\, A_{\beta\mu} = \bigl(A \operatorname{diag}(b_{\lambda\bullet}) A^{\mathsf{T}}\bigr)_{\alpha,\beta}.$$

From this representation we immediately obtain for **all degrees $d \ge 0$**:
- **Dominance vanishing:** Any nonzero summand requires $\alpha \preceq \mu \preceq \lambda$ and $\beta \preceq \mu \preceq \lambda$. Hence $c^\lambda_{\alpha,\beta} = 0$ unless both $\alpha \preceq \lambda$ and $\beta \preceq \lambda$.
- **Principal slice:** When $\alpha = \lambda$, the factor $A_{\lambda\mu} \ne 0$ forces $\lambda \preceq \mu$, which combined with $\mu \preceq \lambda$ forces $\mu = \lambda$. Thus
  $$c^\lambda_{\lambda,\beta} = b_{\lambda\lambda}\, A_{\lambda\lambda}\, A_{\beta\lambda} = A_{\beta\lambda} \ge 0, \qquad c^\lambda_{\lambda,\lambda} = A_{\lambda\lambda} = 1.$$

---

## Exact Verification Table (Degrees $d = 0 \dots 8$)

Run `python3 11-mo475478-stanley-bivariate/stanley_verify.py --degree 8`:

| Degree $d$ | Partitions $p(d)$ | Total Classes | Zeros (Dominance) | Positives | Count at $1$ | Count at $2$ |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| $0$ | $1$ | $1$ | $0$ | $1$ | $1$ | $0$ |
| $1$ | $1$ | $1$ | $0$ | $1$ | $1$ | $0$ |
| $2$ | $2$ | $8$ | $3$ | $5$ | $2$ | $3$ |
| $3$ | $3$ | $27$ | $13$ | $14$ | $3$ | $0$ |
| $4$ | $5$ | $125$ | $70$ | $55$ | $5$ | $6$ |
| $5$ | $7$ | $343$ | $203$ | $140$ | $7$ | $6$ |
| $6$ | $11$ | $1{,}331$ | $849$ | $482$ | $11$ | $12$ |
| $7$ | $15$ | $3{,}375$ | $2{,}199$ | $1{,}176$ | $15$ | $15$ |
| $8$ | $22$ | $10{,}648$ | $7{,}198$ | $3{,}450$ | $22$ | $30$ |
| **Total** | **$67$** | **$15{,}859$** | **$10{,}535$** | **$5{,}324$** | **$67$** | **$72$** |

Through $d \le 8$: zero negative classes occur, every non-dominance zero is non-zero (strict positivity on all pairs $\alpha, \beta \preceq \lambda$), and $c^\lambda_{\alpha,\beta} = 1$ occurs exclusively on the joint diagonal $\alpha = \beta = \lambda$.
