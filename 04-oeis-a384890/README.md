# 04. Anti-Run Constant-Run Lengths

Complete proof of Gus Wiseman's 2025 question on [OEIS A384890](https://oeis.org/A384890): every constant run in A384890 has length $1, 2,$ or $3$.

Using $a(n) = 1 + \operatorname{popcount}(n \mathbin{\&} \lfloor n/2\rfloor)$ ($n \ge 1$), modulo-4 and modulo-8 carry recursions exclude $4$ equal consecutive terms globally, while small indices witness lengths $1, 2,$ and $3$.

- [Complete proof](PROOF.md)
- [Lean 4 formalization (`adjOnes_eq_popcount_and_shr`, `wiseman_A384890_no_run_len_4`) ✅](WisemanA384890.lean)
- [Python verifier](verify_a384890.py) (87 OEIS terms, $n \le 10^6$)
- [Statement Audit](../docs/STATEMENT_AUDIT.md#track-04-anti-run-constant-run-lengths-in-oeis-a384890-)

Run `lean WisemanA384890.lean && python3 verify_a384890.py`.

## Statement Audit

- **Formalized definition:** `a 0 = 0` and `a n = 1 + adjOnes n` ($n \ge 1$), with `adjOnes_eq_popcount_and_shr` proving `adjOnes n = popcount (n &&& (n >>> 1))`.
- **Source bridge:** Equating maximal anti-runs ($i_{j+1} - i_j > 1$) in the binary indices of $n \ge 1$ with $1 + \operatorname{popcount}(n \mathbin{\&} \lfloor n/2 \rfloor)$ is proved in [PROOF.md](PROOF.md) and checked against all 87 OEIS terms and $n \le 20{,}000$ by `a384890_direct` in [verify_a384890.py](verify_a384890.py).
