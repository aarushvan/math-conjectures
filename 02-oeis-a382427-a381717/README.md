# 02. Constant-Block vs. Distinct Run-Sum Partitions

Complete proof of Gus Wiseman's 2025 conjectures on [OEIS A382427](https://oeis.org/A382427) and [OEIS A381717](https://oeis.org/A381717).

A partition admits a decomposition into constant blocks of pairwise distinct sums iff it has a permutation whose maximal constant runs have pairwise distinct sums. Any minimum-block decomposition of size $m$ satisfies $2k_v \le m + 1$ by Pigeonhole merging, permitting conflict-free interleaving of all blocks.

- [Complete proof](PROOF.md)
- [Lean 4 formalization (`wiseman_A382427_iff`, `wiseman_A381717_iff`) ✅](WisemanA382427.lean)
- [Exhaustive Python verifier](verify_a382427.py) ($n \le 22$)
- [Statement Audit](../docs/STATEMENT_AUDIT.md#track-02-constant-block-vs-distinct-run-sum-partitions-)

Run `lean WisemanA382427.lean && python3 verify_a382427.py`.

## Statement Audit

- **Partitions & blocks:** `parts : List Nat` with positivity `∀ x ∈ parts, x > 0` up to `List.Perm`; `Block` enforces positive part values and positive block multiplicities, matching OEIS A382427/A381717 directly.
- **Runs vs. blocks:** `maxRuns` groups strictly maximal contiguous equal-value runs and checks `(bs.map Block.sum).Nodup` vs. `((maxRuns w).map (fun r => r.1 * r.2)).Nodup`.
