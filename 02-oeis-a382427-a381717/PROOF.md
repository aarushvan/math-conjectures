# Proof of Gus Wiseman's 2025 Conjectures on OEIS A382427 & A381717

## Statements
For an integer partition $\lambda$ of $n$:
- **[OEIS A382427](https://oeis.org/A382427):** Number of integer partitions of $n$ that can be partitioned into constant blocks (multisets of equal parts) with pairwise distinct sums. Conjecture (Gus Wiseman, 2025): equals the number of integer partitions of $n$ having a permutation whose maximal constant runs have pairwise distinct sums.
- **[OEIS A381717](https://oeis.org/A381717):** Exact complement (*cannot* be partitioned into constant blocks with distinct sums iff *no* permutation has all distinct run-sums).

## Theorem
A finite multiset of positive integers $\lambda$ can be partitioned into constant blocks with pairwise distinct sums **if and only if** $\lambda$ admits a permutation whose maximal constant runs have pairwise distinct sums.

## Proof

### ($\Leftarrow$) Permutation $\implies$ Block partition
Let $w$ be a permutation of $\lambda$ whose maximal constant runs have pairwise distinct sums. Taking each maximal constant run of $w$ as a constant block immediately partitions $\lambda$ into constant blocks with pairwise distinct sums.

### ($\Rightarrow$) Block partition $\implies$ Permutation
Suppose $\lambda$ admits a partition into constant blocks with pairwise distinct sums. Among all such partitions of $\lambda$, choose one with the **minimum number of blocks**, say $m$. For each positive integer $v$, let $k_v$ denote the number of $v$-blocks in this partition, and let $r_v = m - k_v$ denote the number of blocks of value $\ne v$.

**Claim (Pigeonhole Merge):** For every value $v$, $2k_v \le m + 1$ (equivalently, $k_v \le r_v + 1$).

*Proof of Claim.* Suppose for contradiction that $k_v \ge r_v + 2$ for some $v$. Let $b_{\max}$ be the $v$-block with maximum sum $s_{\max}$ among the $k_v$ blocks of value $v$. Every other $v$-block $b$ satisfies $0 < \operatorname{sum}(b) < s_{\max}$, and there are $k_v - 1$ such blocks. Forming the merged sums
$$s_{\max} + \operatorname{sum}(b)$$
over these $k_v - 1$ remaining $v$-blocks yields $k_v - 1$ pairwise distinct integers strictly greater than $s_{\max}$. None of them can collide with any remaining $v$-block (whose sums are all $\le s_{\max}$). Because $k_v - 1 \ge r_v + 1 > r_v$, by the Pigeonhole Principle at least one of these $k_v - 1$ merged sums does not appear among the $r_v$ blocks of value $\ne v$. Merging $b_{\max}$ with that $v$-block yields a valid partition of $\lambda$ into $m - 1$ constant blocks with pairwise distinct sums, contradicting the minimality of $m$. $\square$

**Constructing a Valid Ordering (No Adjacent Equal Values):**
Given $m$ blocks satisfying $2k_v \le m + 1$ for every $v$, we can arrange all $m$ blocks in sequence with no two adjacent blocks having the same value (for instance, greedily picking at each step a remaining block of maximum multiplicity among values distinct from the previous block, which preserves $2k_v \le m' + 1$ and $2k_{\text{prev}} \le m'$ inductively, or placing sorted value groups into odd positions $1, 3, 5, \dots$ and then even positions $2, 4, 6, \dots$). Concatenating the blocks in this order yields a permutation of $\lambda$ whose maximal constant runs are precisely those $m$ blocks, so their run-sums are pairwise distinct. $\blacksquare$

## Verification
- **Lean 4 kernel check:** [WisemanA382427.lean](WisemanA382427.lean) proves `wiseman_A382427_iff` and `wiseman_A381717_iff` with zero external dependencies and zero `sorry`s.
- **Exhaustive Python verification (`verify_a382427.py`):** Verified equivalence across every integer partition for $n = 0 \dots 22$, matching every published term of OEIS A382427 and A381717.
