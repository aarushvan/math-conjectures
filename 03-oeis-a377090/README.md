# 03. Prime-Difference Greedy Deviation Bound

Disproof of M. F. Hasler's conjectured bound $\bigl\lvert\lvert a(n)\rvert - n/2\bigr\rvert < 2\ln(n+2)$ on [OEIS A377090](https://oeis.org/A377090).

The bound first fails at $n = 370{,}313$ ($a(370{,}313) = -185{,}183$, $\lvert d(n)\rvert = 26.5 \ge 2\ln(370{,}315) \approx 25.644219$). Up to $n = 10{,}000{,}000$, there are `361` violations, reaching peak ratio `1.309077` against $2\ln(n+2)$ at $n = 2{,}010{,}806$ and max deviation `39.0` at $n = 4{,}652{,}436$.

- [Disproof and summary](DISPROOF.md)
- [C verifier (`verify_a377090.c`) ⬜](verify_a377090.c)

Run `clang -O3 -Wall -Wextra -Werror verify_a377090.c -lm -o verify_a377090 && ./verify_a377090`.
