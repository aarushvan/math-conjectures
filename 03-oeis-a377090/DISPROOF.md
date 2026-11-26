# Disproof of M. F. Hasler's Deviation Bound on OEIS A377090

**Source:** [OEIS A377090](https://oeis.org/A377090), FORMULA comment by M. F. Hasler (Feb 21, 2025):
> `||a(n)| - n/2| = O(log(n)), probably ||a(n)| - n/2| < 2*log(n+2) for all n. (Conjectured; verified up to n = 10^5.)`

## Definition of A377090
$a(0) = 0$; for $n > 0$, $a(n)$ is the integer not yet in $\{a(0), \dots, a(n-1)\}$ with minimal $|a(n)|$ (breaking ties in favor of $+|a(n)|$) such that $|a(n) - a(n-1)|$ is prime.

## Verdict: False
Using [verify_a377090.c](verify_a377090.c), we cross-checked all 40 listed OEIS terms (`a(0..39)`) and all 14 published Hasler deviation records up to `n = 9568`, then computed through $n = 10{,}000{,}000$:

- **First counterexample:** $n = 370{,}313$, where
  $$a(370{,}313) = -185{,}183, \qquad d(370{,}313) = |a(370{,}313)| - \frac{370{,}313}{2} = 26.5,$$
  so $\bigl||a(n)| - n/2\bigr| = 26.5 \ge 2\ln(370{,}315) \approx 25.644219$.
- **Violations up to $n = 10^7$:** `361` total violations of $\bigl||a(n)| - n/2\bigr| < 2\ln(n+2)$.
- **Peak ratio vs. $2\ln(n+2)$ in $1 \le n \le 10^7$:** `1.309077` at $n = 2{,}010{,}806$, where $a(2{,}010{,}806) = -1{,}005{,}441$, $|d(n)| = 38.0$, and $2\ln(2{,}010{,}808) \approx 29.028094$ (equivalently $|d(n)|/\ln(n+2) \approx 2.618153$).
- **Largest absolute deviation in $1 \le n \le 10^7$:** $|d(n)| = 39.0$ at $n = 4{,}652{,}436$ ($a(4{,}652{,}436) = 2{,}326{,}179$, vs. $2\ln(n+2) \approx 30.706154$).

*(Note: N. J. A. Sloane's separate conjecture on A377090, that every integer eventually appears in the sequence, remains open.)*
