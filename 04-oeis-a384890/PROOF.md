# Proof of Gus Wiseman's Question on OEIS A384890

**Source:** [OEIS A384890](https://oeis.org/A384890) (Gus Wiseman, 2025):
> *Name:* Number of maximal anti-runs (increasing by more than 1) in the binary indices of $n$.
> *Comment:* Do all constant runs in this sequence have lengths 1, 2, or 3?

## Verdict: Yes

Let $I(n) = \{i_1 < i_2 < \dots < i_m\}$ be the binary indices of $n$ (1-based bit positions of `1`s in the binary expansion of $n$).

1. **Bitwise popcount formula:** For $n = 0$, $a(0) = 0$. For $n \ge 1$, the number of maximal anti-runs ($i_{j+1} - i_j > 1$) in $I(n)$ is $1$ plus the number of non-anti-run steps ($i_{j+1} - i_j = 1$), i.e., adjacent `11` pairs in the binary expansion of $n$:
   $$a(n) = 1 + \operatorname{popcount}\bigl(n \mathbin{\&} (n \gg 1)\bigr) \qquad (n \ge 1).$$
2. **Mod-4 / Mod-8 carry analysis:** Writing $\operatorname{adj}(n) = \operatorname{popcount}(n \mathbin{\&} (n \gg 1))$, the recurrence splits by $n \bmod 4$:
   - $\operatorname{adj}(4q) = \operatorname{adj}(2q)$,
   - $\operatorname{adj}(4q+1) = \operatorname{adj}(2q)$,
   - $\operatorname{adj}(4q+2) = \operatorname{adj}(2q+1)$,
   - $\operatorname{adj}(4q+3) = 1 + \operatorname{adj}(2q+1)$,
   and by induction $\operatorname{adj}(k+1) \le \operatorname{adj}(k) + 1$ for all $k \ge 0$.
3. **No constant run of length $\ge 4$:** Suppose $a(n) = a(n+1) = a(n+2) = a(n+3)$. Since $a(0) = 0 \ne 1 = a(1)$, we have $n \ge 1$, so $\operatorname{adj}(n) = \operatorname{adj}(n+1) = \operatorname{adj}(n+2) = \operatorname{adj}(n+3)$.
   - If $n \equiv 0, 1, 2 \pmod 4$, two of $\{n, n+1, n+2, n+3\}$ are $4q+2$ and $4q+3$, whose $\operatorname{adj}$ values differ by exactly $1$.
   - If $n = 4q+3$, then $\operatorname{adj}(4q+3) = 1 + \operatorname{adj}(2q+1)$ must equal $\operatorname{adj}(4q+4) = \operatorname{adj}(2q+2) = \operatorname{adj}(2q+3)$.
     - If $q = 2m$ is even, $\operatorname{adj}(4m+2) = \operatorname{adj}(2m+1)$ cannot equal $\operatorname{adj}(4m+3) = 1 + \operatorname{adj}(2m+1)$.
     - If $q = 2m+1$ is odd, $1 + \operatorname{adj}(4m+3) = 2 + \operatorname{adj}(2m+1)$, whereas $\operatorname{adj}(4m+4) = \operatorname{adj}(2m+2) \le 1 + \operatorname{adj}(2m+1)$.
4. **All lengths 1, 2, 3 occur:** For example, $a(0)=0$, $a(1)=a(2)=1$, $a(3)=2$, and $a(7)=3, a(8)=a(9)=a(10)=1, a(11)=2$. Hence every constant run has length $1, 2,$ or $3$. $\blacksquare$

## Verification
- **Lean 4 kernel check:** [WisemanA384890.lean](WisemanA384890.lean) proves `adjOnes_eq_popcount_and_shr`, `wiseman_A384890_no_run_len_4`, and run-length witnesses with zero external dependencies and zero `sorry`s.
- **Python verification (`verify_a384890.py`):** Verified against all 87 published OEIS A384890 terms, the popcount identity up to $20{,}000$, and run lengths $\in \{1, 2, 3\}$ through $1{,}000{,}000$.
