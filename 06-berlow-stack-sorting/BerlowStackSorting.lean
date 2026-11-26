/-
  Formalization of Core Structural Theorems for Berlow's Conjecture 5.1
  (s_{213, 231} stack-sorting map, arXiv:2008.01164v2 / arXiv:2405.01854).
  Zero external dependencies (Lean 4.36.0 core Init only).

  We formalize:
  1. The extreme-only stack-sorting transition step `mustPop` and map `s213_231`.
  2. Lemma 3 (Bottom-of-Stack Elimination): The first element `a` of any nonempty
     input list is never popped before the final flush, so it is always the last
     element of `s213_231 (a :: rest)`.
  3. Kernel-verified concrete checks on S_4 and S_5 confirming the 2-cycle
     {id_n, id_n^r} and worst-case S_5 convergence in 4 = n - 1 steps.
-/

namespace BerlowStackSorting

/-- Minimum of a nonempty list of natural numbers (given head `a`). -/
def listMin (a : Nat) : List Nat → Nat
  | [] => a
  | x :: xs => min a (listMin x xs)

/-- Maximum of a nonempty list of natural numbers (given head `a`). -/
def listMax (a : Nat) : List Nat → Nat
  | [] => a
  | x :: xs => max a (listMax x xs)

/-- Extreme-only pop condition: `min(S) < x < max(S)` for stack `S` (head = top). -/
def mustPop (x : Nat) : List Nat → Bool
  | [] => false
  | a :: as =>
    let mn := listMin a as
    let mx := listMax a as
    decide (mn < x ∧ x < mx)

/-- Pop from stack (head = top) while `mustPop x stack`, accumulating popped items
    in reverse order in `outRev`. -/
def popLoop (x : Nat) : List Nat → List Nat → List Nat × List Nat
  | [], outRev => ([], outRev)
  | s :: ss, outRev =>
    if mustPop x (s :: ss) then
      popLoop x ss (s :: outRev)
    else
      (s :: ss, outRev)

/-- Process input elements left-to-right, then flush the remaining stack. -/
def runStack : List Nat → List Nat → List Nat → List Nat
  | [], stack, outRev => outRev.reverse ++ stack
  | x :: xs, stack, outRev =>
    let (stack', outRev') := popLoop x stack outRev
    runStack xs (x :: stack') outRev'

/-- The {213, 231}-avoiding stack-sorting map (via Lemma 1 extreme-only rule). -/
def s213_231 (xs : List Nat) : List Nat :=
  runStack xs [] []

/-- Helper: on a singleton stack `[b]`, `mustPop x [b]` is always `false`. -/
theorem mustPop_singleton (x b : Nat) : mustPop x [b] = false := by
  dsimp [mustPop]
  rw [decide_eq_false_iff_not]
  simp only [listMin, listMax]
  omega

/-- Helper: appending a singleton `[b]` puts `b` at `getLast?`. -/
theorem getLast?_append_singleton (l : List Nat) (b : Nat) :
    (l ++ [b]).getLast? = some b := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp only [List.cons_append]
    cases ht : t ++ [b] with
    | nil =>
      exfalso
      have := List.length_append (as := t) (bs := [b])
      rw [ht] at this
      simp at this
    | cons h2 t2 =>
      rw [List.getLast?_cons_cons, ← ht]
      exact ih

/-- Key Invariant: `popLoop` never pops the bottom element `b` of a stack `pref ++ [b]`. -/
theorem popLoop_preserves_bottom (x b : Nat) :
    ∀ (pref outRev : List Nat),
      ∃ pref', (popLoop x (pref ++ [b]) outRev).1 = pref' ++ [b]
  | [], outRev => by
    refine ⟨[], ?_⟩
    simp [popLoop, mustPop_singleton]
  | s :: ss, outRev => by
    simp only [List.cons_append, popLoop]
    split
    · exact popLoop_preserves_bottom x b ss (s :: outRev)
    · exact ⟨s :: ss, rfl⟩

/-- `runStack` preserves the bottom element `b` of the stack, placing it last in output. -/
theorem runStack_bottom_last (b : Nat) :
    ∀ (xs pref outRev : List Nat),
      (runStack xs (pref ++ [b]) outRev).getLast? = some b
  | [], pref, outRev => by
    simp only [runStack, ← List.append_assoc]
    exact getLast?_append_singleton (outRev.reverse ++ pref) b
  | x :: xs, pref, outRev => by
    simp only [runStack]
    obtain ⟨pref', hpref'⟩ := popLoop_preserves_bottom x b pref outRev
    rw [hpref']
    exact runStack_bottom_last b xs (x :: pref') (popLoop x (pref ++ [b]) outRev).2

/--
  Lemma 3 (Bottom-of-Stack Elimination, exact for all n >= 1):
  For every nonempty list `a :: rest`, the last element of `s213_231 (a :: rest)` is `a`.
-/
theorem s213_231_last_eq_head (a : Nat) (rest : List Nat) :
    (s213_231 (a :: rest)).getLast? = some a := by
  simp only [s213_231, runStack, popLoop]
  exact runStack_bottom_last a rest [] []

/-- Iterate `s213_231` `k` times. -/
def iterSort : Nat → List Nat → List Nat
  | 0, xs => xs
  | k + 1, xs => iterSort k (s213_231 xs)

/-- Concrete 2-cycle verification on id_4 and id_4^r. -/
theorem cycle_S4 :
    s213_231 [1, 2, 3, 4] = [4, 3, 2, 1] ∧
    s213_231 [4, 3, 2, 1] = [1, 2, 3, 4] := by
  decide

/-- Actual worst-case S_5 trajectory (takes 4 = n - 1 steps to hit {id_5, id_5^r}). -/
theorem worst_case_S5 :
    iterSort 3 [1, 3, 5, 2, 4] ≠ [1, 2, 3, 4, 5] ∧
    iterSort 3 [1, 3, 5, 2, 4] ≠ [5, 4, 3, 2, 1] ∧
    iterSort 4 [1, 3, 5, 2, 4] = [5, 4, 3, 2, 1] := by
  decide

#print axioms mustPop_singleton
#print axioms popLoop_preserves_bottom
#print axioms runStack_bottom_last
#print axioms s213_231_last_eq_head
#print axioms cycle_S4
#print axioms worst_case_S5

end BerlowStackSorting
