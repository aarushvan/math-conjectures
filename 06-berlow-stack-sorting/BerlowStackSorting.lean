/-
  Complete End-to-End Formalization of Berlow's Conjecture 5.1 / Zhang's Conjecture 4.2
  for the {213, 231}-avoiding stack-sorting map (arXiv:2008.01164v2 / arXiv:2405.01854).
  Zero external dependencies (Lean 4.36.0 core Init only). Zero sorrys, zero custom axioms.

  Formalized components:
  1. Literal top-to-bottom {213, 231}-avoiding stack-sorting definition `s213_231_literal`
     and equivalence theorem `s213_231_literal_eq` with the extreme-only rule `s213_231`
     (Lemma 1).
  2. Permutation invariance (`s213_231_perm`) and explicit action on `idPerm n` and `revPerm n`.
  3. Lemma 2 (`isRightExtreme_s213_231`): preservation of right-to-left extremes without
     complementation arithmetic, yielding `badCount (s213_231 pi) <= badCount pi`.
  4. Lemma 3 (`s213_231_last_eq_head`) and strict `badCount` drop on non-extreme starts.
  5. Lemma 4 (`lemma4_consecutive_extreme_starts`): at most two consecutive extreme starts
     outside {idPerm n, revPerm n}.
  6. Lemma 5 (`lemma5_no_bad_one_step`): one-step convergence from `badCount pi = 0`.
  7. Main theorems for all n >= 1 / n >= 3:
     - `berlow_conjecture_5_1_213_231` (exact periodic-point classification for all p >= 1)
     - `berlow_convergence_3n_minus_7` (exact 3n - 7 convergence bound for all n >= 3)
-/

namespace BerlowStackSorting

/-! ### Part 1: Core Definitions, Extreme-Only Rule, and Bottom-of-Stack Elimination -/

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

/-! ### Part 2: Literal {213, 231}-Avoiding Stack Definition & Lemma 1 Equivalence -/

/-- Checks if list `s` (read top-to-bottom) contains an ordered pair `(b, c)` with `b < x < c` (213)
    or `c < x < b` (231) when `x` sits above `s`. -/
def hasPairBetween (x : Nat) : List Nat → Bool
  | [] => false
  | b :: bs =>
    bs.any (fun c => decide ((b < x ∧ x < c) ∨ (c < x ∧ x < b))) || hasPairBetween x bs

/-- Literal check whether a top-to-bottom stack contains a 213 or 231 subsequence. -/
def has213or231 : List Nat → Bool
  | [] => false
  | a :: as => hasPairBetween a as || has213or231 as

/-- A top-to-bottom stack avoids `{213, 231}` iff `has213or231` is `false`. -/
def avoids213_231 (s : List Nat) : Bool :=
  !has213or231 s

/-- Literal `{213, 231}`-avoiding pop loop. -/
def popLoopLit (x : Nat) : List Nat → List Nat → List Nat × List Nat
  | [], outRev => ([], outRev)
  | s :: ss, outRev =>
    if has213or231 (x :: s :: ss) then
      popLoopLit x ss (s :: outRev)
    else
      (s :: ss, outRev)

/-- Literal stack-sorting state machine matching Berlow's top-to-bottom definition. -/
def runStackLit : List Nat → List Nat → List Nat → List Nat
  | [], stack, outRev => outRev.reverse ++ stack
  | x :: xs, stack, outRev =>
    let (stack', outRev') := popLoopLit x stack outRev
    runStackLit xs (x :: stack') outRev'

/-- Literal `{213, 231}`-avoiding stack-sorting map. -/
def s213_231_literal (xs : List Nat) : List Nat :=
  runStackLit xs [] []

/-- Iterate the literal `{213, 231}`-avoiding stack-sorting map `k` times. -/
def iterSortLit : Nat → List Nat → List Nat
  | 0, xs => xs
  | k + 1, xs => iterSortLit k (s213_231_literal xs)

theorem listMin_mem (a : Nat) (as : List Nat) : listMin a as = a ∨ listMin a as ∈ as := by
  induction as generalizing a with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    simp only [listMin]
    by_cases h : a ≤ listMin b bs
    · rw [Nat.min_eq_left h]
      exact Or.inl rfl
    · rw [Nat.min_eq_right (Nat.le_of_not_le h)]
      rcases ih b with h1 | h2
      · rw [h1]; exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem b h2)

theorem listMax_mem (a : Nat) (as : List Nat) : listMax a as = a ∨ listMax a as ∈ as := by
  induction as generalizing a with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    simp only [listMax]
    by_cases h : a ≤ listMax b bs
    · rw [Nat.max_eq_right h]
      rcases ih b with h1 | h2
      · rw [h1]; exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem b h2)
    · rw [Nat.max_eq_left (Nat.le_of_not_le h)]
      exact Or.inl rfl

theorem listMin_le (a x : Nat) (as : List Nat) (hx : x = a ∨ x ∈ as) : listMin a as ≤ x := by
  induction as generalizing a with
  | nil =>
    rcases hx with rfl | h
    · exact Nat.le_refl _
    · cases h
  | cons b bs ih =>
    simp only [listMin]
    rcases hx with hxa | hmem
    · subst hxa; exact Nat.min_le_left _ _
    · rcases List.mem_cons.mp hmem with hxb | hmem2
      · exact Nat.le_trans (Nat.min_le_right _ _) (ih b (Or.inl hxb))
      · exact Nat.le_trans (Nat.min_le_right _ _) (ih b (Or.inr hmem2))

theorem le_listMax (a x : Nat) (as : List Nat) (hx : x = a ∨ x ∈ as) : x ≤ listMax a as := by
  induction as generalizing a with
  | nil =>
    rcases hx with rfl | h
    · exact Nat.le_refl _
    · cases h
  | cons b bs ih =>
    simp only [listMax]
    rcases hx with hxa | hmem
    · subst hxa; exact Nat.le_max_left _ _
    · rcases List.mem_cons.mp hmem with hxb | hmem2
      · exact Nat.le_trans (ih b (Or.inl hxb)) (Nat.le_max_right _ _)
      · exact Nat.le_trans (ih b (Or.inr hmem2)) (Nat.le_max_right _ _)

/-- Ordered pair `(b, c)` appearing in list `s`. -/
def OrdPair (p : Nat → Nat → Prop) : List Nat → Prop
  | [] => False
  | b :: bs => (∃ c ∈ bs, p b c) ∨ OrdPair p bs

theorem hasPairBetween_iff_ordPair (x : Nat) (s : List Nat) :
    hasPairBetween x s = true ↔ OrdPair (fun b c => (b < x ∧ x < c) ∨ (c < x ∧ x < b)) s := by
  induction s with
  | nil => simp [hasPairBetween, OrdPair]
  | cons b bs ih =>
    simp only [hasPairBetween, OrdPair, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, ih]

theorem ordPair_distinct_mem (u v : Nat) (hne : u ≠ v) (s : List Nat) (hu : u ∈ s) (hv : v ∈ s) :
    OrdPair (fun b c => (b = u ∧ c = v) ∨ (b = v ∧ c = u)) s := by
  induction s with
  | nil => cases hu
  | cons a as ih =>
    rcases List.mem_cons.mp hu with rfl | hu'
    · rcases List.mem_cons.mp hv with h | hv'
      · exact absurd h.symm hne
      · exact Or.inl ⟨v, hv', Or.inl ⟨rfl, rfl⟩⟩
    · rcases List.mem_cons.mp hv with rfl | hv'
      · exact Or.inl ⟨u, hu', Or.inr ⟨rfl, rfl⟩⟩
      · exact Or.inr (ih hu' hv')

theorem ordPair_mono {p q : Nat → Nat → Prop} (himp : ∀ b c, p b c → q b c) :
    ∀ s, OrdPair p s → OrdPair q s
  | [], h => h
  | _ :: _bs, Or.inl ⟨c, hc, hp⟩ => Or.inl ⟨c, hc, himp _ _ hp⟩
  | _ :: bs, Or.inr hr => Or.inr (ordPair_mono himp bs hr)

/-- Lemma 1 (Extreme-Only Stack Rule, full Boolean equivalence):
    `hasPairBetween x (a :: as) = mustPop x (a :: as)`. -/
theorem hasPairBetween_eq_mustPop (x a : Nat) (as : List Nat) :
    hasPairBetween x (a :: as) = mustPop x (a :: as) := by
  apply Bool.eq_iff_iff.mpr
  rw [hasPairBetween_iff_ordPair]
  simp only [mustPop, decide_eq_true_eq]
  constructor
  · intro hord
    have hrec : ∀ s, (∀ y ∈ s, y = a ∨ y ∈ as) →
        OrdPair (fun b c => (b < x ∧ x < c) ∨ (c < x ∧ x < b)) s →
        listMin a as < x ∧ x < listMax a as := by
      intro s hs h
      induction s with
      | nil => cases h
      | cons b bs ihs =>
        rcases h with ⟨c, hc, hbc⟩ | hrest
        · have hb : b = a ∨ b ∈ as := hs b List.mem_cons_self
          have hc' : c = a ∨ c ∈ as := hs c (List.mem_cons_of_mem b hc)
          rcases hbc with ⟨hb1, hc1⟩ | ⟨hc1, hb1⟩
          · exact ⟨Nat.lt_of_le_of_lt (listMin_le a b as hb) hb1,
                   Nat.lt_of_lt_of_le hc1 (le_listMax a c as hc')⟩
          · exact ⟨Nat.lt_of_le_of_lt (listMin_le a c as hc') hc1,
                   Nat.lt_of_lt_of_le hb1 (le_listMax a b as hb)⟩
        · exact ihs (fun y hy => hs y (List.mem_cons_of_mem b hy)) hrest
    exact hrec (a :: as) (fun y hy => List.mem_cons.mp hy) hord
  · rintro ⟨hmn, hmx⟩
    let mn := listMin a as
    let mx := listMax a as
    have hne : mn ≠ mx := by omega
    have hmn_mem : mn ∈ a :: as := by
      rcases listMin_mem a as with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem a h
    have hmx_mem : mx ∈ a :: as := by
      rcases listMax_mem a as with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem a h
    have hord := ordPair_distinct_mem mn mx hne (a :: as) hmn_mem hmx_mem
    refine ordPair_mono ?_ (a :: as) hord
    intro b c hbc
    rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hmn, hmx⟩
    · exact Or.inr ⟨hmn, hmx⟩

theorem avoids_tail {a : Nat} {as : List Nat} (hav : avoids213_231 (a :: as) = true) :
    avoids213_231 as = true := by
  simp only [avoids213_231, has213or231, Bool.not_eq_true'] at hav ⊢
  cases hp : hasPairBetween a as <;> cases ht : has213or231 as <;> simp_all

theorem popLoopLit_eq_popLoop (x : Nat) (stack outRev : List Nat)
    (hav : avoids213_231 stack = true) :
    popLoopLit x stack outRev = popLoop x stack outRev ∧
    avoids213_231 (x :: (popLoop x stack outRev).1) = true := by
  induction stack generalizing outRev with
  | nil =>
    simp [popLoopLit, popLoop, avoids213_231, has213or231, hasPairBetween]
  | cons s ss ih =>
    have hav_ss : avoids213_231 ss = true := avoids_tail hav
    have hhas : has213or231 (s :: ss) = false := by
      simpa [avoids213_231] using hav
    have heqCond : has213or231 (x :: s :: ss) = mustPop x (s :: ss) := by
      rw [has213or231, hhas, Bool.or_false, hasPairBetween_eq_mustPop]
    simp only [popLoopLit, popLoop, heqCond]
    split
    · exact ih (s :: outRev) hav_ss
    · next hfalse =>
      refine ⟨rfl, ?_⟩
      rw [avoids213_231, has213or231, hhas, Bool.or_false, hasPairBetween_eq_mustPop,
        Bool.not_eq_true']
      exact Bool.eq_false_iff.mpr hfalse

theorem runStackLit_eq_runStack (xs stack outRev : List Nat)
    (hav : avoids213_231 stack = true) :
    runStackLit xs stack outRev = runStack xs stack outRev := by
  induction xs generalizing stack outRev with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨heq, hav'⟩ := popLoopLit_eq_popLoop x stack outRev hav
    simp only [runStackLit, runStack, heq]
    exact ih (x :: (popLoop x stack outRev).1) (popLoop x stack outRev).2 hav'

/-- Exact equivalence between the literal `{213, 231}`-avoiding stack sort and `s213_231`. -/
theorem s213_231_literal_eq (xs : List Nat) : s213_231_literal xs = s213_231 xs :=
  runStackLit_eq_runStack xs [] [] rfl

theorem iterSortLit_eq_iterSort (k : Nat) (xs : List Nat) :
    iterSortLit k xs = iterSort k xs := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    simp only [iterSortLit, iterSort, s213_231_literal_eq]
    exact ih (s213_231 xs)

/-! ### Part 3: Permutations, `idPerm`, `revPerm`, and Basic Stack Invariants -/

def idPerm (n : Nat) : List Nat :=
  (List.range n).map (· + 1)

def revPerm (n : Nat) : List Nat :=
  (idPerm n).reverse

def IsPerm (n : Nat) (π : List Nat) : Prop :=
  π.Perm (idPerm n)

theorem nodup_map_of_inj_on {α β : Type} (l : List α) (f : α → β)
    (hl : l.Nodup) (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) :
    (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hl.2 (fun x hx y hy => hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy))⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨y, hy, hfy⟩
    have hya : y = a := hinj y (List.mem_cons_of_mem a hy) a List.mem_cons_self hfy
    subst hya
    exact hl.1 hy

theorem mem_idPerm {n x : Nat} : x ∈ idPerm n ↔ 1 ≤ x ∧ x ≤ n := by
  simp only [idPerm, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩

theorem mem_revPerm {n x : Nat} : x ∈ revPerm n ↔ 1 ≤ x ∧ x ≤ n := by
  rw [revPerm, List.mem_reverse]
  exact mem_idPerm

theorem nodup_idPerm (n : Nat) : (idPerm n).Nodup := by
  apply nodup_map_of_inj_on (List.range n) (· + 1) List.nodup_range
  intro x _ y _ h
  omega

theorem length_idPerm (n : Nat) : (idPerm n).length = n := by
  simp [idPerm, List.length_map, List.length_range]

theorem isPerm_nodup {n : Nat} {π : List Nat} (h : IsPerm n π) : π.Nodup :=
  h.nodup_iff.mpr (nodup_idPerm n)

theorem isPerm_length {n : Nat} {π : List Nat} (h : IsPerm n π) : π.length = n := by
  rw [h.length_eq, length_idPerm]

theorem isPerm_mem {n x : Nat} {π : List Nat} (h : IsPerm n π) : x ∈ π ↔ 1 ≤ x ∧ x ≤ n := by
  rw [h.mem_iff]
  exact mem_idPerm

theorem pairwise_range (n : Nat) : (List.range n).Pairwise (· < ·) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.pairwise_append]
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_range] at ha
    simp only [List.mem_singleton] at hb
    subst hb
    exact ha

theorem pairwise_map_of_mono {R S : Nat → Nat → Prop} (f : Nat → Nat)
    (hm : ∀ a b, R a b → S (f a) (f b)) :
    ∀ l, List.Pairwise R l → List.Pairwise S (l.map f)
  | [], _ => List.Pairwise.nil
  | a :: as, h => by
    rw [List.pairwise_cons] at h
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨?_, pairwise_map_of_mono f hm as h.2⟩
    intro b hb
    rcases List.mem_map.mp hb with ⟨a', ha', rfl⟩
    exact hm a a' (h.1 a' ha')

theorem pairwise_idPerm (n : Nat) : (idPerm n).Pairwise (· < ·) :=
  pairwise_map_of_mono (· + 1) (fun _ _ h => by omega) (List.range n) (pairwise_range n)

theorem pairwise_revPerm (n : Nat) : (revPerm n).Pairwise (· > ·) :=
  List.pairwise_reverse.mpr (pairwise_idPerm n)

theorem eq_of_perm_of_pairwise {R : Nat → Nat → Prop}
    (hirr : ∀ a b, R a b → ¬ R b a)
    (htot : ∀ a b : Nat, a ≠ b → R a b ∨ R b a) :
    ∀ {l₁ l₂ : List Nat}, l₁.Perm l₂ → l₁.Pairwise R → l₂.Pairwise R → l₁ = l₂
  | [], l₂, hp, _, _ => hp.nil_eq
  | a :: as, [], hp, _, _ => absurd hp.length_eq (by simp)
  | a :: as, b :: bs, hp, h1, h2 => by
    rw [List.pairwise_cons] at h1 h2
    by_cases heq : a = b
    · subst heq
      have hrest : as.Perm bs := (List.perm_cons a).mp hp
      congr 1
      exact eq_of_perm_of_pairwise hirr htot hrest h1.2 h2.2
    · exfalso
      have ha_in : a ∈ b :: bs := hp.mem_iff.mp List.mem_cons_self
      have hb_in : b ∈ a :: as := hp.mem_iff.mpr List.mem_cons_self
      rcases List.mem_cons.mp ha_in with rfl | ha'
      · exact heq rfl
      · rcases List.mem_cons.mp hb_in with rfl | hb'
        · exact heq rfl
        · exact hirr b a (h2.1 a ha') (h1.1 b hb')

theorem eq_idPerm_of_pairwise {n : Nat} {π : List Nat} (hπ : IsPerm n π)
    (hpw : π.Pairwise (· < ·)) : π = idPerm n :=
  eq_of_perm_of_pairwise (fun _ _ h1 h2 => by omega) (fun a b h => by omega) hπ hpw (pairwise_idPerm n)

theorem eq_revPerm_of_pairwise {n : Nat} {π : List Nat} (hπ : IsPerm n π)
    (hpw : π.Pairwise (· > ·)) : π = revPerm n :=
  eq_of_perm_of_pairwise (fun _ _ h1 h2 => by omega) (fun a b h => by omega)
    (hπ.trans (List.reverse_perm (idPerm n)).symm) hpw (pairwise_revPerm n)

/-- Factored `feedList` exposes modular stack + outRev composition. -/
def feedList : List Nat → List Nat → List Nat → List Nat × List Nat
  | [], stack, outRev => (stack, outRev)
  | x :: xs, stack, outRev =>
    let (stack', outRev') := popLoop x stack outRev
    feedList xs (x :: stack') outRev'

theorem runStack_eq_feedList (xs stack outRev : List Nat) :
    runStack xs stack outRev = (feedList xs stack outRev).2.reverse ++ (feedList xs stack outRev).1 := by
  induction xs generalizing stack outRev with
  | nil => rfl
  | cons x xs ih =>
    simp only [runStack, feedList]
    exact ih (x :: (popLoop x stack outRev).1) (popLoop x stack outRev).2

theorem feedList_append (a b stack outRev : List Nat) :
    feedList (a ++ b) stack outRev =
      feedList b (feedList a stack outRev).1 (feedList a stack outRev).2 := by
  induction a generalizing stack outRev with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, feedList]
    exact ih (x :: (popLoop x stack outRev).1) (popLoop x stack outRev).2

theorem popLoop_inv (x : Nat) (stack outRev : List Nat) :
    (popLoop x stack outRev).2.reverse ++ (popLoop x stack outRev).1 = outRev.reverse ++ stack := by
  induction stack generalizing outRev with
  | nil => rfl
  | cons s ss ih =>
    simp only [popLoop]
    split
    · rw [ih (s :: outRev), List.reverse_cons, List.append_assoc]
      rfl
    · rfl

theorem feedList_perm (xs stack outRev : List Nat) :
    ((feedList xs stack outRev).2.reverse ++ (feedList xs stack outRev).1).Perm
      (outRev.reverse ++ stack ++ xs) := by
  induction xs generalizing stack outRev with
  | nil =>
    simp only [feedList, List.append_nil]
    exact List.Perm.refl _
  | cons x xs ih =>
    simp only [feedList]
    have h1 := ih (x :: (popLoop x stack outRev).1) (popLoop x stack outRev).2
    have h2 : ((popLoop x stack outRev).2.reverse ++ (x :: (popLoop x stack outRev).1) ++ xs).Perm
        (outRev.reverse ++ stack ++ x :: xs) := by
      have hm1 : ((popLoop x stack outRev).2.reverse ++ (x :: (popLoop x stack outRev).1) ++ xs).Perm
          (x :: ((popLoop x stack outRev).2.reverse ++ (popLoop x stack outRev).1 ++ xs)) := by
        simp [List.append_assoc, List.cons_append]
      rw [popLoop_inv] at hm1
      have hm2 : (outRev.reverse ++ stack ++ x :: xs).Perm
          (x :: (outRev.reverse ++ stack ++ xs)) :=
        List.perm_middle (a := x) (l₁ := outRev.reverse ++ stack) (l₂ := xs)
      exact hm1.trans hm2.symm
    exact h1.trans h2

theorem s213_231_perm (xs : List Nat) : (s213_231 xs).Perm xs := by
  simp only [s213_231, runStack_eq_feedList]
  exact feedList_perm xs [] []

theorem s213_231_isPerm {n : Nat} {π : List Nat} (h : IsPerm n π) : IsPerm n (s213_231 π) :=
  (s213_231_perm π).trans h

theorem iterSort_isPerm (k : Nat) {n : Nat} {π : List Nat} (h : IsPerm n π) :
    IsPerm n (iterSort k π) := by
  induction k generalizing π with
  | zero => exact h
  | succ k ih => exact ih (s213_231_isPerm h)

theorem mustPop_of_forall_lt (x : Nat) : ∀ s, (∀ a ∈ s, a < x) → mustPop x s = false
  | [], _ => rfl
  | a :: as, ha => by
    simp only [mustPop, decide_eq_false_iff_not]
    have hmx := listMax_mem a as
    have hle : listMax a as < x := by
      rcases hmx with h | h
      · rw [h]; exact ha a List.mem_cons_self
      · exact ha _ (List.mem_cons_of_mem a h)
    omega

theorem mustPop_of_forall_gt (x : Nat) : ∀ s, (∀ a ∈ s, x < a) → mustPop x s = false
  | [], _ => rfl
  | a :: as, ha => by
    simp only [mustPop, decide_eq_false_iff_not]
    have hmn := listMin_mem a as
    have hlt : x < listMin a as := by
      rcases hmn with h | h
      · rw [h]; exact ha a List.mem_cons_self
      · exact ha _ (List.mem_cons_of_mem a h)
    omega

theorem runStack_id_chain (xs stack : List Nat)
    (h1 : xs.Pairwise (· < ·)) (h2 : ∀ x ∈ xs, ∀ s ∈ stack, s < x) :
    runStack xs stack [] = xs.reverse ++ stack := by
  induction xs generalizing stack with
  | nil => simp [runStack]
  | cons x xs ih =>
    rw [List.pairwise_cons] at h1
    have hmp : mustPop x stack = false :=
      mustPop_of_forall_lt x stack (fun s hs => h2 x List.mem_cons_self s hs)
    have hpop : popLoop x stack [] = (stack, []) := by
      cases stack with
      | nil => rfl
      | cons s ss => simp [popLoop, hmp]
    simp only [runStack, hpop]
    rw [ih (x :: stack) h1.2]
    · simp [List.reverse_cons, List.append_assoc]
    · intro y hy s hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact h1.1 y hy
      · exact h2 y (List.mem_cons_of_mem x hy) s hs'

theorem runStack_rev_chain (xs stack : List Nat)
    (h1 : xs.Pairwise (· > ·)) (h2 : ∀ x ∈ xs, ∀ s ∈ stack, x < s) :
    runStack xs stack [] = xs.reverse ++ stack := by
  induction xs generalizing stack with
  | nil => simp [runStack]
  | cons x xs ih =>
    rw [List.pairwise_cons] at h1
    have hmp : mustPop x stack = false :=
      mustPop_of_forall_gt x stack (fun s hs => h2 x List.mem_cons_self s hs)
    have hpop : popLoop x stack [] = (stack, []) := by
      cases stack with
      | nil => rfl
      | cons s ss => simp [popLoop, hmp]
    simp only [runStack, hpop]
    rw [ih (x :: stack) h1.2]
    · simp [List.reverse_cons, List.append_assoc]
    · intro y hy s hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact h1.1 y hy
      · exact h2 y (List.mem_cons_of_mem x hy) s hs'

theorem s213_231_idPerm (n : Nat) : s213_231 (idPerm n) = revPerm n := by
  simp only [s213_231]
  rw [runStack_id_chain (idPerm n) [] (pairwise_idPerm n) (fun _ _ _ hs => by cases hs)]
  simp [revPerm]

theorem s213_231_revPerm (n : Nat) : s213_231 (revPerm n) = idPerm n := by
  simp only [s213_231]
  rw [runStack_rev_chain (revPerm n) [] (pairwise_revPerm n) (fun _ _ _ hs => by cases hs)]
  simp [revPerm]

theorem iterSort_id_or_rev (k n : Nat) {π : List Nat}
    (h : π = idPerm n ∨ π = revPerm n) :
    iterSort k π = idPerm n ∨ iterSort k π = revPerm n := by
  induction k generalizing π with
  | zero => exact h
  | succ k ih =>
    simp only [iterSort]
    apply ih
    rcases h with rfl | rfl
    · exact Or.inr (s213_231_idPerm n)
    · exact Or.inl (s213_231_revPerm n)

/-! ### Part 4: Lemma 2 (`Bad` Monotonicity / Right-Extreme Preservation) & `badCount` Drop -/

def HasTailAfter (x : Nat) (P : Nat → Prop) (l : List Nat) : Prop :=
  ∃ pref suf, l = pref ++ [x] ++ suf ∧ ∀ y ∈ suf, P y

def IsRLMin (x : Nat) (xs : List Nat) : Prop :=
  HasTailAfter x (fun y => x < y) xs

def IsRLMax (x : Nat) (xs : List Nat) : Prop :=
  HasTailAfter x (fun y => y < x) xs

def IsRightExtreme (x : Nat) (xs : List Nat) : Prop :=
  IsRLMin x xs ∨ IsRLMax x xs

def isRLMinBool (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => if y == x then ys.all (fun z => decide (x < z)) else isRLMinBool x ys

def isRLMaxBool (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => if y == x then ys.all (fun z => decide (z < x)) else isRLMaxBool x ys

def isRightExtremeBool (x : Nat) (xs : List Nat) : Bool :=
  isRLMinBool x xs || isRLMaxBool x xs

def badCount (xs : List Nat) : Nat :=
  xs.countP (fun x => !isRightExtremeBool x xs)

theorem isRLMinBool_iff (x : Nat) :
    ∀ xs : List Nat, xs.Nodup → (isRLMinBool x xs = true ↔ IsRLMin x xs)
  | [], _ => by
    constructor
    · intro h; simp [isRLMinBool] at h
    · rintro ⟨pref, suf, heq, _⟩; cases pref <;> simp at heq
  | y :: ys, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [isRLMinBool]
    by_cases hyx : y = x
    · subst hyx
      simp only [beq_self_eq_true, ↓reduceIte, List.all_eq_true, decide_eq_true_eq]
      constructor
      · intro h
        exact ⟨[], ys, rfl, h⟩
      · rintro ⟨pref, suf, heq, hsuf⟩ z hz
        cases pref with
        | nil =>
          simp only [List.nil_append, List.singleton_append, List.cons.injEq] at heq
          rcases heq with ⟨_, rfl⟩
          exact hsuf z hz
        | cons p ps =>
          simp only [List.cons_append, List.cons.injEq] at heq
          exfalso
          apply hnd.1
          rw [heq.2]
          simp
    · have hbeq : (y == x) = false := beq_false_of_ne hyx
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      rw [isRLMinBool_iff x ys hnd.2]
      constructor
      · rintro ⟨pref, suf, rfl, hsuf⟩
        exact ⟨y :: pref, suf, rfl, hsuf⟩
      · rintro ⟨pref, suf, heq, hsuf⟩
        cases pref with
        | nil =>
          simp at heq
          exact absurd heq.1 hyx
        | cons p ps =>
          simp only [List.cons_append, List.cons.injEq] at heq
          exact ⟨ps, suf, heq.2, hsuf⟩

theorem isRLMaxBool_iff (x : Nat) :
    ∀ xs : List Nat, xs.Nodup → (isRLMaxBool x xs = true ↔ IsRLMax x xs)
  | [], _ => by
    constructor
    · intro h; simp [isRLMaxBool] at h
    · rintro ⟨pref, suf, heq, _⟩; cases pref <;> simp at heq
  | y :: ys, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [isRLMaxBool]
    by_cases hyx : y = x
    · subst hyx
      simp only [beq_self_eq_true, ↓reduceIte, List.all_eq_true, decide_eq_true_eq]
      constructor
      · intro h
        exact ⟨[], ys, rfl, h⟩
      · rintro ⟨pref, suf, heq, hsuf⟩ z hz
        cases pref with
        | nil =>
          simp only [List.nil_append, List.singleton_append, List.cons.injEq] at heq
          rcases heq with ⟨_, rfl⟩
          exact hsuf z hz
        | cons p ps =>
          simp only [List.cons_append, List.cons.injEq] at heq
          exfalso
          apply hnd.1
          rw [heq.2]
          simp
    · have hbeq : (y == x) = false := beq_false_of_ne hyx
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      rw [isRLMaxBool_iff x ys hnd.2]
      constructor
      · rintro ⟨pref, suf, rfl, hsuf⟩
        exact ⟨y :: pref, suf, rfl, hsuf⟩
      · rintro ⟨pref, suf, heq, hsuf⟩
        cases pref with
        | nil =>
          simp at heq
          exact absurd heq.1 hyx
        | cons p ps =>
          simp only [List.cons_append, List.cons.injEq] at heq
          exact ⟨ps, suf, heq.2, hsuf⟩

theorem isRightExtremeBool_iff {x : Nat} {xs : List Nat} (hnd : xs.Nodup) :
    isRightExtremeBool x xs = true ↔ IsRightExtreme x xs := by
  simp only [isRightExtremeBool, Bool.or_eq_true, IsRightExtreme,
    isRLMinBool_iff x xs hnd, isRLMaxBool_iff x xs hnd]

theorem hasTailAfter_insert_middle {x z : Nat} {P : Nat → Prop} (hz : P z) :
    ∀ a b : List Nat, HasTailAfter x P (a ++ b) → HasTailAfter x P (a ++ z :: b)
  | [], b, ⟨pref, suf, heq, hsuf⟩ => by
    rw [List.nil_append] at heq
    exact ⟨z :: pref, suf, by simp [heq], hsuf⟩
  | a :: as, b, ⟨pref, suf, heq, hsuf⟩ => by
    cases pref with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
      rcases heq with ⟨rfl, hbs⟩
      refine ⟨[], as ++ z :: b, ?_, ?_⟩
      · simp
      · intro y hy
        rcases List.mem_append.mp hy with hy1 | hy2
        · exact hsuf y (hbs ▸ List.mem_append_left b hy1)
        · rcases List.mem_cons.mp hy2 with rfl | hy3
          · exact hz
          · exact hsuf y (hbs ▸ List.mem_append_right as hy3)
    | cons p ps =>
      simp only [List.cons_append, List.cons.injEq] at heq
      rcases heq with ⟨rfl, htail⟩
      obtain ⟨pref', suf', heq', hsuf'⟩ := hasTailAfter_insert_middle hz as b ⟨ps, suf, htail, hsuf⟩
      exact ⟨a :: pref', suf', by simp only [List.cons_append, List.append_assoc, heq'], hsuf'⟩

theorem runStack_preserves_hasTailAfter {x : Nat} {P : Nat → Prop} (px : Nat → Nat → Prop)
    (hpx : ∀ z, px z x → P z) :
    ∀ xs stack outRev,
      HasTailAfter x P (outRev.reverse ++ stack) →
      (∀ z ∈ xs, px z x) →
      HasTailAfter x P (runStack xs stack outRev)
  | [], stack, outRev, htail, _ => by
    simpa [runStack] using htail
  | z :: zs, stack, outRev, htail, hzs => by
    simp only [runStack]
    apply runStack_preserves_hasTailAfter px hpx zs _ _ _ (fun w hw => hzs w (List.mem_cons_of_mem z hw))
    have hinv : (popLoop z stack outRev).2.reverse ++ (popLoop z stack outRev).1 =
        outRev.reverse ++ stack := popLoop_inv z stack outRev
    rw [← hinv] at htail
    exact hasTailAfter_insert_middle (hpx z (hzs z List.mem_cons_self)) _ _ htail

theorem popLoop_stops_not_mustPop (x : Nat) :
    ∀ stack outRev, (popLoop x stack outRev).1 = [] ∨
      mustPop x (popLoop x stack outRev).1 = false
  | [], outRev => Or.inl rfl
  | s :: ss, outRev => by
    simp only [popLoop]
    split
    · exact popLoop_stops_not_mustPop x ss (s :: outRev)
    · next hf =>
      exact Or.inr (Bool.eq_false_iff.mpr hf)

theorem popLoop_suffix_gt (z x : Nat) (bot : List Nat) (hbot_ne : bot ≠ [])
    (hbot : ∀ b ∈ bot, b < x) (hz : x < z) :
    ∀ top outRev, ∃ top' outRev',
      popLoop z (top ++ [x] ++ bot) outRev = (top' ++ [x] ++ bot, outRev')
  | [], outRev => by
    refine ⟨[], outRev, ?_⟩
    simp only [List.nil_append, List.singleton_append, popLoop]
    cases bot with
    | nil => exact absurd rfl hbot_ne
    | cons b bs =>
      have hmx : listMax x (b :: bs) ≤ x := by
        rcases listMax_mem x (b :: bs) with h | h
        · omega
        · exact Nat.le_of_lt (hbot _ h)
      have hmp : mustPop z (x :: b :: bs) = false := by
        simp only [mustPop, decide_eq_false_iff_not]
        omega
      simp [hmp]
  | t :: ts, outRev => by
    simp only [List.cons_append, popLoop]
    split
    · exact popLoop_suffix_gt z x bot hbot_ne hbot hz ts (t :: outRev)
    · exact ⟨t :: ts, outRev, rfl⟩

theorem popLoop_suffix_lt (z x : Nat) (bot : List Nat) (hbot_ne : bot ≠ [])
    (hbot : ∀ b ∈ bot, x < b) (hz : z < x) :
    ∀ top outRev, ∃ top' outRev',
      popLoop z (top ++ [x] ++ bot) outRev = (top' ++ [x] ++ bot, outRev')
  | [], outRev => by
    refine ⟨[], outRev, ?_⟩
    simp only [List.nil_append, List.singleton_append, popLoop]
    cases bot with
    | nil => exact absurd rfl hbot_ne
    | cons b bs =>
      have hmn : x ≤ listMin x (b :: bs) := by
        rcases listMin_mem x (b :: bs) with h | h
        · omega
        · exact Nat.le_of_lt (hbot _ h)
      have hmp : mustPop z (x :: b :: bs) = false := by
        simp only [mustPop, decide_eq_false_iff_not]
        omega
      simp [hmp]
  | t :: ts, outRev => by
    simp only [List.cons_append, popLoop]
    split
    · exact popLoop_suffix_lt z x bot hbot_ne hbot hz ts (t :: outRev)
    · exact ⟨t :: ts, outRev, rfl⟩

theorem runStack_never_pops_x_min (x : Nat) (bot : List Nat) (hbot_ne : bot ≠ [])
    (hbot : ∀ b ∈ bot, b < x) :
    ∀ suf top outRev, (∀ z ∈ suf, x < z) →
      HasTailAfter x (fun y => y < x) (runStack suf (top ++ [x] ++ bot) outRev)
  | [], top, outRev, _ => ⟨outRev.reverse ++ top, bot, by simp [runStack, List.append_assoc], hbot⟩
  | z :: zs, top, outRev, hzs => by
    simp only [runStack]
    have hz := hzs z List.mem_cons_self
    obtain ⟨top', outRev', hpop⟩ := popLoop_suffix_gt z x bot hbot_ne hbot hz top outRev
    rw [hpop]
    have heq : z :: (top' ++ [x] ++ bot) = (z :: top') ++ [x] ++ bot := by simp
    rw [heq]
    exact runStack_never_pops_x_min x bot hbot_ne hbot zs (z :: top') outRev'
      (fun w hw => hzs w (List.mem_cons_of_mem z hw))

theorem runStack_never_pops_x_max (x : Nat) (bot : List Nat) (hbot_ne : bot ≠ [])
    (hbot : ∀ b ∈ bot, x < b) :
    ∀ suf top outRev, (∀ z ∈ suf, z < x) →
      HasTailAfter x (fun y => x < y) (runStack suf (top ++ [x] ++ bot) outRev)
  | [], top, outRev, _ => ⟨outRev.reverse ++ top, bot, by simp [runStack, List.append_assoc], hbot⟩
  | z :: zs, top, outRev, hzs => by
    simp only [runStack]
    have hz := hzs z List.mem_cons_self
    obtain ⟨top', outRev', hpop⟩ := popLoop_suffix_lt z x bot hbot_ne hbot hz top outRev
    rw [hpop]
    have heq : z :: (top' ++ [x] ++ bot) = (z :: top') ++ [x] ++ bot := by simp
    rw [heq]
    exact runStack_never_pops_x_max x bot hbot_ne hbot zs (z :: top') outRev'
      (fun w hw => hzs w (List.mem_cons_of_mem z hw))

theorem not_mem_of_nodup_perm {x : Nat} {a b xs : List Nat}
    (hnd : xs.Nodup) (hp : (a ++ x :: b).Perm xs) : ∀ y ∈ a ++ b, y ≠ x := by
  have hnd2 : (a ++ x :: b).Nodup := hp.nodup_iff.mpr hnd
  rw [List.perm_middle.nodup_iff] at hnd2
  rw [List.nodup_cons] at hnd2
  intro y hy hxy
  subst hxy
  exact hnd2.1 hy

theorem exists_not_of_not_forall (p : Nat → Prop) [DecidablePred p] :
    ∀ l : List Nat, (¬ ∀ x ∈ l, p x) → ∃ x ∈ l, ¬ p x
  | [], h => absurd (fun _ hm => by cases hm) h
  | y :: ys, h => by
    by_cases hy : p y
    · obtain ⟨x, hx, hnx⟩ := exists_not_of_not_forall p ys (fun hall => h (fun z hz => by
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact hy
        · exact hall z hz'))
      exact ⟨x, List.mem_cons_of_mem y hx, hnx⟩
    · exact ⟨y, List.mem_cons_self, hy⟩

theorem forall_lt_of_not_mustPop_and_not_all_gt {x b₀ : Nat} {bs : List Nat}
    (hmp : mustPop x (b₀ :: bs) = false)
    (hne : ∀ b ∈ b₀ :: bs, b ≠ x)
    (hnot : ¬ ∀ b ∈ b₀ :: bs, x < b) :
    ∀ b ∈ b₀ :: bs, b < x := by
  obtain ⟨c, hc, hnc⟩ := exists_not_of_not_forall (fun b => x < b) (b₀ :: bs) hnot
  have hcx := hne c hc
  have hmn : listMin b₀ bs < x := by
    have := listMin_le b₀ c bs (List.mem_cons.mp hc)
    omega
  simp only [mustPop, decide_eq_false_iff_not] at hmp
  have hmx_le : listMax b₀ bs ≤ x := by omega
  intro b hb
  have hbx := hne b hb
  have hble := le_listMax b₀ b bs (List.mem_cons.mp hb)
  omega

theorem forall_gt_of_not_mustPop_and_not_all_lt {x b₀ : Nat} {bs : List Nat}
    (hmp : mustPop x (b₀ :: bs) = false)
    (hne : ∀ b ∈ b₀ :: bs, b ≠ x)
    (hnot : ¬ ∀ b ∈ b₀ :: bs, b < x) :
    ∀ b ∈ b₀ :: bs, x < b := by
  obtain ⟨c, hc, hnc⟩ := exists_not_of_not_forall (fun b => b < x) (b₀ :: bs) hnot
  have hcx := hne c hc
  have hmx : x < listMax b₀ bs := by
    have := le_listMax b₀ c bs (List.mem_cons.mp hc)
    omega
  simp only [mustPop, decide_eq_false_iff_not] at hmp
  have hmn_ge : x ≤ listMin b₀ bs := by omega
  intro b hb
  have hbx := hne b hb
  have hble := listMin_le b₀ b bs (List.mem_cons.mp hb)
  omega

/-- Lemma 2 (Monotonicity of Right-Extremes, full list version):
    If `xs.Nodup` and `IsRightExtreme x xs`, then `IsRightExtreme x (s213_231 xs)`. -/
theorem isRightExtreme_s213_231 {x : Nat} {xs : List Nat} (hnd : xs.Nodup)
    (hre : IsRightExtreme x xs) : IsRightExtreme x (s213_231 xs) := by
  rcases hre with ⟨pref, suf, heq, hsuf⟩ | ⟨pref, suf, heq, hsuf⟩
  · -- Case 1: x is RLMin in xs
    have heq' : xs = pref ++ (x :: suf) := by simpa [List.append_assoc] using heq
    rw [s213_231, runStack_eq_feedList, heq', feedList_append, ← runStack_eq_feedList]
    simp only [runStack]
    let st₁ := (feedList pref [] []).1
    let out₁ := (feedList pref [] []).2
    let st' := (popLoop x st₁ out₁).1
    let out' := (popLoop x st₁ out₁).2
    have hperm_step : (out'.reverse ++ st' ++ (x :: suf)).Perm xs := by
      rw [heq']
      change ((popLoop x st₁ out₁).2.reverse ++ (popLoop x st₁ out₁).1 ++ (x :: suf)).Perm _
      rw [popLoop_inv]
      have hf := feedList_perm pref [] []
      simp only [List.reverse_nil, List.nil_append] at hf
      exact hf.append_right (x :: suf)
    have hperm_all : (out'.reverse ++ x :: (st' ++ suf)).Perm xs := by
      have hassoc : out'.reverse ++ x :: (st' ++ suf) = out'.reverse ++ (x :: st') ++ suf := by
        simp [List.append_assoc]
      have hmid : (out'.reverse ++ x :: st' ++ suf).Perm (out'.reverse ++ st' ++ x :: suf) := by
        rw [List.append_assoc, List.append_assoc]
        exact List.Perm.append_left out'.reverse (by simpa [List.append_assoc] using (List.perm_middle (a := x) (l₁ := st') (l₂ := suf)).symm)
      rw [hassoc]
      exact hmid.trans hperm_step
    have hne_x : ∀ b ∈ st', b ≠ x := fun b hb =>
      not_mem_of_nodup_perm hnd hperm_all b (List.mem_append_right _ (List.mem_append_left _ hb))
    by_cases hall : ∀ b ∈ st', x < b
    · left
      exact runStack_preserves_hasTailAfter (fun z y => y < z) (fun _ h => h) suf (x :: st') out'
        ⟨out'.reverse, st', by simp [List.append_assoc], hall⟩ hsuf
    · right
      rcases popLoop_stops_not_mustPop x st₁ out₁ with hnil | hmp
      · change st' = [] at hnil
        exfalso; apply hall; intro b hb; rw [hnil] at hb; cases hb
      · cases hst : st' with
        | nil => exfalso; apply hall; intro b hb; rw [hst] at hb; cases hb
        | cons b₀ bs =>
          have hbot_lt := forall_lt_of_not_mustPop_and_not_all_gt
            (hst ▸ hmp) (fun b hb => hne_x b (hst ▸ hb)) (hst ▸ hall)
          change IsRLMax x (runStack suf (x :: st') out')
          rw [hst]
          simpa [IsRLMax] using
            runStack_never_pops_x_min x (b₀ :: bs) (List.cons_ne_nil b₀ bs) hbot_lt suf [] out' hsuf
  · -- Case 2: x is RLMax in xs
    have heq' : xs = pref ++ (x :: suf) := by simpa [List.append_assoc] using heq
    rw [s213_231, runStack_eq_feedList, heq', feedList_append, ← runStack_eq_feedList]
    simp only [runStack]
    let st₁ := (feedList pref [] []).1
    let out₁ := (feedList pref [] []).2
    let st' := (popLoop x st₁ out₁).1
    let out' := (popLoop x st₁ out₁).2
    have hperm_step : (out'.reverse ++ st' ++ (x :: suf)).Perm xs := by
      rw [heq']
      change ((popLoop x st₁ out₁).2.reverse ++ (popLoop x st₁ out₁).1 ++ (x :: suf)).Perm _
      rw [popLoop_inv]
      have hf := feedList_perm pref [] []
      simp only [List.reverse_nil, List.nil_append] at hf
      exact hf.append_right (x :: suf)
    have hperm_all : (out'.reverse ++ x :: (st' ++ suf)).Perm xs := by
      have hassoc : out'.reverse ++ x :: (st' ++ suf) = out'.reverse ++ (x :: st') ++ suf := by
        simp [List.append_assoc]
      have hmid : (out'.reverse ++ x :: st' ++ suf).Perm (out'.reverse ++ st' ++ x :: suf) := by
        rw [List.append_assoc, List.append_assoc]
        exact List.Perm.append_left out'.reverse (by simpa [List.append_assoc] using (List.perm_middle (a := x) (l₁ := st') (l₂ := suf)).symm)
      rw [hassoc]
      exact hmid.trans hperm_step
    have hne_x : ∀ b ∈ st', b ≠ x := fun b hb =>
      not_mem_of_nodup_perm hnd hperm_all b (List.mem_append_right _ (List.mem_append_left _ hb))
    by_cases hall : ∀ b ∈ st', b < x
    · right
      exact runStack_preserves_hasTailAfter (fun z y => z < y) (fun _ h => h) suf (x :: st') out'
        ⟨out'.reverse, st', by simp [List.append_assoc], hall⟩ hsuf
    · left
      rcases popLoop_stops_not_mustPop x st₁ out₁ with hnil | hmp
      · change st' = [] at hnil
        exfalso; apply hall; intro b hb; rw [hnil] at hb; cases hb
      · cases hst : st' with
        | nil => exfalso; apply hall; intro b hb; rw [hst] at hb; cases hb
        | cons b₀ bs =>
          have hbot_gt := forall_gt_of_not_mustPop_and_not_all_lt
            (hst ▸ hmp) (fun b hb => hne_x b (hst ▸ hb)) (hst ▸ hall)
          change IsRLMin x (runStack suf (x :: st') out')
          rw [hst]
          simpa [IsRLMin] using
            runStack_never_pops_x_max x (b₀ :: bs) (List.cons_ne_nil b₀ bs) hbot_gt suf [] out' hsuf

theorem countP_le_of_imp {α : Type} (p q : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = true → q x = true) :
    l.countP p ≤ l.countP q := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons]
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hx := h x List.mem_cons_self
    cases hpx : p x <;> cases hqx : q x <;> simp_all <;> omega

theorem countP_lt_of_imp {α : Type} (p q : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = true → q x = true)
    (hex : ∃ a ∈ l, p a = false ∧ q a = true) :
    l.countP p + 1 ≤ l.countP q := by
  induction l with
  | nil => rcases hex with ⟨_, hm, _⟩; cases hm
  | cons x xs ih =>
    rcases hex with ⟨a, ha, hpa, hqa⟩
    simp only [List.countP_cons]
    rcases List.mem_cons.mp ha with rfl | ha'
    · have hle := countP_le_of_imp p q xs (fun y hy => h y (List.mem_cons_of_mem a hy))
      simp [hpa, hqa]
      omega
    · have ih' := ih (fun y hy => h y (List.mem_cons_of_mem x hy)) ⟨a, ha', hpa, hqa⟩
      have hx := h x List.mem_cons_self
      cases hpx : p x <;> cases hqx : q x <;> simp_all <;> omega

theorem badCount_mono {π : List Nat} (hnd : π.Nodup) :
    badCount (s213_231 π) ≤ badCount π := by
  have hp : (s213_231 π).Perm π := s213_231_perm π
  have hnd2 : (s213_231 π).Nodup := hp.nodup_iff.mpr hnd
  rw [badCount, List.Perm.countP_eq _ hp, badCount]
  apply countP_le_of_imp
  intro _x _hx hbad
  simp only [Bool.not_eq_true'] at hbad ⊢
  cases hb : isRightExtremeBool _x π
  · rfl
  · exfalso
    have h1 := (isRightExtremeBool_iff hnd).mp hb
    have h2 := isRightExtreme_s213_231 hnd h1
    have h3 := (isRightExtremeBool_iff hnd2).mpr h2
    rw [h3] at hbad
    exact Bool.noConfusion hbad

theorem head_non_extreme_not_rightExtreme {n : Nat} {a : Nat} {rest : List Nat}
    (hπ : IsPerm n (a :: rest)) (ha1 : a ≠ 1) (han : a ≠ n) :
    isRightExtremeBool a (a :: rest) = false := by
  have hnd := isPerm_nodup hπ
  have ha_mem : a ∈ a :: rest := List.mem_cons_self
  have ha_bounds := (isPerm_mem hπ).mp ha_mem
  have h1_mem : 1 ∈ a :: rest := (isPerm_mem hπ).mpr ⟨Nat.le_refl 1, by omega⟩
  have hn_mem : n ∈ a :: rest := (isPerm_mem hπ).mpr ⟨by omega, Nat.le_refl n⟩
  have h1_rest : 1 ∈ rest := by
    rcases List.mem_cons.mp h1_mem with h | h
    · exact absurd h.symm ha1
    · exact h
  have hn_rest : n ∈ rest := by
    rcases List.mem_cons.mp hn_mem with h | h
    · exact absurd h.symm han
    · exact h
  cases hb : isRightExtremeBool a (a :: rest)
  · rfl
  · exfalso
    rcases (isRightExtremeBool_iff hnd).mp hb with ⟨pref, suf, heq, hsuf⟩ | ⟨pref, suf, heq, hsuf⟩
    · cases pref with
      | nil =>
        simp only [List.nil_append, List.singleton_append, List.cons.injEq] at heq
        have := hsuf 1 (heq.2 ▸ h1_rest)
        omega
      | cons p ps =>
        simp only [List.cons_append, List.cons.injEq] at heq
        rw [List.nodup_cons] at hnd
        apply hnd.1
        rw [heq.2]
        simp
    · cases pref with
      | nil =>
        simp only [List.nil_append, List.singleton_append, List.cons.injEq] at heq
        have := hsuf n (heq.2 ▸ hn_rest)
        omega
      | cons p ps =>
        simp only [List.cons_append, List.cons.injEq] at heq
        rw [List.nodup_cons] at hnd
        apply hnd.1
        rw [heq.2]
        simp

theorem exists_append_singleton_of_getLast {α : Type} :
    ∀ (l : List α) (x : α), l.getLast? = some x → ∃ pref, l = pref ++ [x]
  | [], _, h => by simp at h
  | [y], x, h => by simp at h; subst h; exact ⟨[], rfl⟩
  | y :: z :: zs, x, h => by
    rw [List.getLast?_cons_cons] at h
    obtain ⟨pref, hp⟩ := exists_append_singleton_of_getLast (z :: zs) x h
    exact ⟨y :: pref, by simp [hp]⟩

theorem isRightExtreme_of_getLast {x : Nat} {xs : List Nat}
    (hlast : xs.getLast? = some x) : IsRightExtreme x xs := by
  obtain ⟨pref, heq⟩ := exists_append_singleton_of_getLast xs x hlast
  exact Or.inl ⟨pref, [], by simpa using heq, fun _ hm => by cases hm⟩

theorem badCount_drop_of_non_extreme_head {n a : Nat} {rest : List Nat}
    (hπ : IsPerm n (a :: rest)) (ha1 : a ≠ 1) (han : a ≠ n) :
    badCount (s213_231 (a :: rest)) + 1 ≤ badCount (a :: rest) := by
  have hnd := isPerm_nodup hπ
  have hp := s213_231_perm (a :: rest)
  have hnd2 := hp.nodup_iff.mpr hnd
  rw [badCount, List.Perm.countP_eq _ hp, badCount]
  apply countP_lt_of_imp
  · intro _x _hx hbad
    simp only [Bool.not_eq_true'] at hbad ⊢
    cases hb : isRightExtremeBool _x (a :: rest)
    · rfl
    · exfalso
      have h1 := (isRightExtremeBool_iff hnd).mp hb
      have h2 := isRightExtreme_s213_231 hnd h1
      have h3 := (isRightExtremeBool_iff hnd2).mpr h2
      rw [h3] at hbad
      exact Bool.noConfusion hbad
  · refine ⟨a, List.mem_cons_self, ?_, ?_⟩
    · have hre := isRightExtreme_of_getLast (s213_231_last_eq_head a rest)
      have hbool := (isRightExtremeBool_iff hnd2).mpr hre
      simp [hbool]
    · have hfalse := head_non_extreme_not_rightExtreme hπ ha1 han
      simp [hfalse]

theorem last_two_rightExtreme {u v : Nat} {init : List Nat} (hnd : (init ++ [u, v]).Nodup) :
    isRightExtremeBool u (init ++ [u, v]) = true ∧ isRightExtremeBool v (init ++ [u, v]) = true := by
  have hnodup_uv : ([u, v] : List Nat).Nodup :=
    (List.Pairwise.sublist (List.sublist_append_right init [u, v]) hnd)
  rw [List.nodup_cons] at hnodup_uv
  have huv : u ≠ v := fun h => hnodup_uv.1 (h ▸ List.mem_cons_self)
  refine ⟨?_, ?_⟩
  · apply (isRightExtremeBool_iff hnd).mpr
    by_cases hlt : u < v
    · exact Or.inl ⟨init, [v], by simp [List.append_assoc], fun y hy => by simp at hy; subst hy; exact hlt⟩
    · exact Or.inr ⟨init, [v], by simp [List.append_assoc], fun y hy => by simp at hy; subst hy; omega⟩
  · apply (isRightExtremeBool_iff hnd).mpr
    exact Or.inl ⟨init ++ [u], [], by simp [List.append_assoc], fun _ hy => by cases hy⟩

theorem badCount_le_sub_two {n : Nat} {π : List Nat} (hn : n ≥ 2) (hπ : IsPerm n π) :
    badCount π ≤ n - 2 := by
  have hlen := isPerm_length hπ
  have hnd := isPerm_nodup hπ
  have hrev : π.reverse.length ≥ 2 := by simp [hlen]; exact hn
  cases hr0 : π.reverse with
  | nil => rw [hr0] at hrev; simp at hrev
  | cons v r1 =>
    cases hr1 : r1 with
    | nil => rw [hr0, hr1] at hrev; simp at hrev
    | cons u r2 =>
      have hsplit : π = r2.reverse ++ [u, v] := by
        have := congrArg List.reverse hr0
        rw [List.reverse_reverse, hr1, List.reverse_cons, List.reverse_cons] at this
        simpa [List.append_assoc] using this
      have hlen_init : r2.reverse.length = n - 2 := by
        have hlen_sp := congrArg List.length hsplit
        simp only [hlen, List.length_append, List.length_cons, List.length_nil] at hlen_sp
        omega
      rw [hsplit] at hnd ⊢
      have ⟨hu, hv⟩ := last_two_rightExtreme hnd
      simp only [badCount, List.countP_append, List.countP_cons, List.countP_nil, hu, hv,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      have hcnt : List.countP (fun x => !isRightExtremeBool x (r2.reverse ++ [u, v])) r2.reverse ≤ r2.reverse.length :=
        List.countP_le_length
      omega

/-! ### Part 5: Lemma 4 (At Most Two Consecutive Extreme Starts) & Lemma 5 (`badCount = 0`) -/

theorem mem_popLoop_snd (z : Nat) :
    ∀ stack outRev y, y ∈ (popLoop z stack outRev).2 → y ∈ stack ∨ y ∈ outRev
  | [], outRev, y, hy => Or.inr hy
  | s :: ss, outRev, y, hy => by
    simp only [popLoop] at hy
    split at hy
    · rcases mem_popLoop_snd z ss (s :: outRev) y hy with h | h
      · exact Or.inl (List.mem_cons_of_mem s h)
      · rcases List.mem_cons.mp h with rfl | h'
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h'
    · exact Or.inr hy

theorem mem_feedList_snd :
    ∀ xs stack outRev y, y ∈ (feedList xs stack outRev).2 → y ∈ xs ∨ y ∈ stack ∨ y ∈ outRev
  | [], stack, outRev, y, hy => Or.inr (Or.inr hy)
  | x :: xs, stack, outRev, y, hy => by
    simp only [feedList] at hy
    rcases mem_feedList_snd xs (x :: (popLoop x stack outRev).1) (popLoop x stack outRev).2 y hy with h | h | h
    · exact Or.inl (List.mem_cons_of_mem x h)
    · rcases List.mem_cons.mp h with rfl | hst
      · exact Or.inl List.mem_cons_self
      · -- wait: hst in popLoop.1, which is subset of stack
        have hperm := popLoop_inv x stack outRev
        have hmem : y ∈ (popLoop x stack outRev).2.reverse ++ (popLoop x stack outRev).1 :=
          List.mem_append_right _ hst
        rw [hperm] at hmem
        rcases List.mem_append.mp hmem with h1 | h2
        · exact Or.inr (Or.inr (List.mem_reverse.mp h1))
        · exact Or.inr (Or.inl h2)
    · rcases mem_popLoop_snd x stack outRev y h with h1 | h2
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h2)

theorem length_le_popLoop_snd (z : Nat) :
    ∀ stack outRev, outRev.length ≤ (popLoop z stack outRev).2.length
  | [], outRev => Nat.le_refl _
  | s :: ss, outRev => by
    simp only [popLoop]
    split
    · exact Nat.le_trans (by simp) (length_le_popLoop_snd z ss (s :: outRev))
    · exact Nat.le_refl _

theorem length_le_feedList_snd :
    ∀ xs stack outRev, outRev.length ≤ (feedList xs stack outRev).2.length
  | [], _stack, _outRev => Nat.le_refl _
  | x :: xs, stack, outRev =>
    Nat.le_trans (length_le_popLoop_snd x stack outRev)
      (length_le_feedList_snd xs (x :: (popLoop x stack outRev).1) (popLoop x stack outRev).2)

theorem popLoop_out_nil_of_eq {x : Nat} {s : Nat} {ss : List Nat}
    (h : (popLoop x (s :: ss) []).2 = []) :
    mustPop x (s :: ss) = false ∧ popLoop x (s :: ss) [] = (s :: ss, []) := by
  simp only [popLoop] at h ⊢
  cases hmp : mustPop x (s :: ss)
  · simp
  · exfalso
    rw [hmp] at h
    simp only [↓reduceIte] at h
    have := length_le_popLoop_snd x ss [s]
    rw [h] at this
    simp at this

theorem no_pops_of_feedList_out_nil :
    ∀ xs stack, (feedList xs stack []).2 = [] →
      ∀ pre z suf, xs = pre ++ [z] ++ suf → mustPop z (pre.reverse ++ stack) = false
  | [], stack, _, pre, z, suf, heq => by cases pre <;> simp at heq
  | x :: xs, stack, hnil, pre, z, suf, heq => by
    have hpop_len : (popLoop x stack []).2.length ≤ (feedList xs (x :: (popLoop x stack []).1) (popLoop x stack []).2).2.length :=
      length_le_feedList_snd xs _ _
    simp only [feedList] at hnil
    rw [hnil] at hpop_len
    have hpop_nil : (popLoop x stack []).2 = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hpop_len)
    have ⟨hmp_x, hpop_eq⟩ : mustPop x stack = false ∧ popLoop x stack [] = (stack, []) := by
      cases stack with
      | nil => exact ⟨rfl, rfl⟩
      | cons s ss => exact popLoop_out_nil_of_eq hpop_nil
    rw [hpop_eq] at hnil
    cases pre with
    | nil =>
      simp only [List.nil_append, List.singleton_append, List.cons.injEq] at heq
      rcases heq with ⟨rfl, _⟩
      simpa using hmp_x
    | cons p ps =>
      simp only [List.cons_append, List.cons.injEq] at heq
      rcases heq with ⟨rfl, htail⟩
      have ih := no_pops_of_feedList_out_nil xs (x :: stack) hnil ps z suf htail
      simpa [List.reverse_cons, List.append_assoc] using ih

theorem head?_append_of_ne_nil {α : Type} {a b : List α} (ha : a ≠ []) :
    (a ++ b).head? = a.head? := by
  cases a with
  | nil => exact absurd rfl ha
  | cons x xs => rfl

theorem outRev_nil_of_last_exits_first {pref : List Nat} {a : Nat}
    (ha : a ∉ pref) (hhead : (s213_231 (pref ++ [a])).head? = some a) :
    (feedList (pref ++ [a]) [] []).2 = [] := by
  rw [s213_231, runStack_eq_feedList] at hhead
  cases hout : (feedList (pref ++ [a]) [] []).2 with
  | nil => rfl
  | cons y ys =>
    exfalso
    have hrev_ne : (y :: ys).reverse ≠ [] := by
      intro hrev
      have := congrArg List.length hrev
      simp at this
    rw [hout, head?_append_of_ne_nil hrev_ne] at hhead
    cases hrev_eq : (y :: ys).reverse with
    | nil => exact hrev_ne hrev_eq
    | cons z zs =>
      rw [hrev_eq] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      have hz_rev : z ∈ y :: ys := List.mem_reverse.mp (hrev_eq ▸ List.mem_cons_self)
      rw [feedList_append] at hout
      simp only [feedList] at hout
      have hz_mem : z ∈ (popLoop a (feedList pref [] []).1 (feedList pref [] []).2).2 :=
        hout ▸ hz_rev
      rcases mem_popLoop_snd a _ _ z hz_mem with h1 | h2
      · have hf := feedList_perm pref [] []
        simp only [List.reverse_nil, List.nil_append] at hf
        exact ha (hhead ▸ hf.mem_iff.mp (List.mem_append_right _ h1))
      · rcases mem_feedList_snd pref [] [] z h2 with h1 | h2' | h3
        · exact ha (hhead ▸ h1)
        · cases h2'
        · cases h3

theorem exists_split_of_mem {α : Type} :
    ∀ (l : List α) (x : α), x ∈ l → ∃ a b, l = a ++ [x] ++ b
  | [], _, hx => by cases hx
  | y :: ys, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨[], ys, rfl⟩
    · obtain ⟨a, b, rfl⟩ := exists_split_of_mem ys x hx'
      exact ⟨y :: a, b, rfl⟩

theorem pairwise_of_forall_split (R : Nat → Nat → Prop) :
    ∀ l : List Nat,
      (∀ pre z suf, l = pre ++ [z] ++ suf → ∀ u ∈ pre, R u z) →
      l.Pairwise R
  | [], _ => List.Pairwise.nil
  | u :: rest, h => by
    rw [List.pairwise_cons]
    refine ⟨?_, pairwise_of_forall_split R rest (fun pre z suf heq w hw =>
      h (u :: pre) z suf (by simp [heq]) w (List.mem_cons_of_mem u hw))⟩
    intro v hv
    obtain ⟨pre', suf', rfl⟩ := exists_split_of_mem rest v hv
    exact h (u :: pre') v suf' (by simp [List.append_assoc]) u List.mem_cons_self

theorem pairwise_lt_of_no_pops_min_head {n : Nat} {rest : List Nat}
    (hperm : IsPerm n (1 :: rest))
    (hnopops : ∀ pre z suf, (1 :: rest) = pre ++ [z] ++ suf → mustPop z pre.reverse = false) :
    (1 :: rest).Pairwise (· < ·) := by
  have hnd := isPerm_nodup hperm
  apply pairwise_of_forall_split (· < ·) (1 :: rest)
  intro pre z suf heq u hu
  have h1_in_pre : 1 ∈ pre := by
    cases pre with
    | nil => cases hu
    | cons p ps =>
      simp only [List.cons_append, List.cons.injEq] at heq
      rw [heq.1]
      exact List.mem_cons_self
  have hpre_ne : pre.reverse ≠ [] := by
    intro hnil
    have h0 := congrArg List.length hnil
    simp only [List.length_reverse, List.length_nil] at h0
    cases pre with
    | nil => cases hu
    | cons _ _ => simp at h0
  have hnd_split := hnd
  rw [heq] at hnd_split
  have hne_z : ∀ y ∈ pre, y ≠ z := fun y hy =>
    not_mem_of_nodup_perm hnd_split (by simp [List.append_assoc]) y (List.mem_append_left suf hy)
  have hz_mem : z ∈ 1 :: rest := by rw [heq]; simp
  have hz_ge1 : 1 ≤ z := ((isPerm_mem hperm).mp hz_mem).1
  have hz_ne1 : z ≠ 1 := (hne_z 1 h1_in_pre).symm
  have hz_gt1 : 1 < z := by omega
  have hmp := hnopops pre z suf heq
  cases hrev : pre.reverse with
  | nil => exact absurd hrev hpre_ne
  | cons r₀ rs =>
    rw [hrev] at hmp
    simp only [mustPop, decide_eq_false_iff_not] at hmp
    have h1_rev : 1 ∈ r₀ :: rs := hrev ▸ List.mem_reverse.mpr h1_in_pre
    have hmn : listMin r₀ rs < z := by
      have := listMin_le r₀ 1 rs (List.mem_cons.mp h1_rev)
      omega
    have hmx_le : listMax r₀ rs ≤ z := by omega
    have hu_rev : u ∈ r₀ :: rs := hrev ▸ List.mem_reverse.mpr hu
    have hu_le := le_listMax r₀ u rs (List.mem_cons.mp hu_rev)
    have huz := hne_z u hu
    omega

theorem pairwise_gt_of_no_pops_max_head {n : Nat} {rest : List Nat}
    (hperm : IsPerm n (n :: rest))
    (hnopops : ∀ pre z suf, (n :: rest) = pre ++ [z] ++ suf → mustPop z pre.reverse = false) :
    (n :: rest).Pairwise (· > ·) := by
  have hnd := isPerm_nodup hperm
  apply pairwise_of_forall_split (· > ·) (n :: rest)
  intro pre z suf heq u hu
  have hn_in_pre : n ∈ pre := by
    cases pre with
    | nil => cases hu
    | cons p ps =>
      simp only [List.cons_append, List.cons.injEq] at heq
      rw [heq.1]
      exact List.mem_cons_self
  have hpre_ne : pre.reverse ≠ [] := by
    intro hnil
    have h0 := congrArg List.length hnil
    simp only [List.length_reverse, List.length_nil] at h0
    cases pre with
    | nil => cases hu
    | cons _ _ => simp at h0
  have hnd_split := hnd
  rw [heq] at hnd_split
  have hne_z : ∀ y ∈ pre, y ≠ z := fun y hy =>
    not_mem_of_nodup_perm hnd_split (by simp [List.append_assoc]) y (List.mem_append_left suf hy)
  have hz_mem : z ∈ n :: rest := by rw [heq]; simp
  have hz_len : z ≤ n := ((isPerm_mem hperm).mp hz_mem).2
  have hz_nen : z ≠ n := (hne_z n hn_in_pre).symm
  have hz_ltn : z < n := by omega
  have hmp := hnopops pre z suf heq
  cases hrev : pre.reverse with
  | nil => exact absurd hrev hpre_ne
  | cons r₀ rs =>
    rw [hrev] at hmp
    simp only [mustPop, decide_eq_false_iff_not] at hmp
    have hn_rev : n ∈ r₀ :: rs := hrev ▸ List.mem_reverse.mpr hn_in_pre
    have hmx : z < listMax r₀ rs := by
      have := le_listMax r₀ n rs (List.mem_cons.mp hn_rev)
      omega
    have hmn_ge : z ≤ listMin r₀ rs := by omega
    have hu_rev : u ∈ r₀ :: rs := hrev ▸ List.mem_reverse.mpr hu
    have hu_ge := listMin_le r₀ u rs (List.mem_cons.mp hu_rev)
    have huz := hne_z u hu
    omega

theorem head?_eq_some_of_ne_nil {α : Type} {l : List α} (h : l ≠ []) :
    ∃ a, l.head? = some a := by
  cases l with
  | nil => exact absurd rfl h
  | cons a _ => exact ⟨a, rfl⟩

/-- Lemma 4 (At Most Two Consecutive Extreme Starts):
    If `π`, `s213_231 π`, and `s213_231 (s213_231 π)` all start with `1` or `n` (`n ≥ 2`),
    then `s213_231 π ∈ {idPerm n, revPerm n}`. -/
theorem lemma4_consecutive_extreme_starts {n : Nat} (hn : n ≥ 2) {π : List Nat} (hπ : IsPerm n π)
    (h0 : ∃ a, π.head? = some a ∧ (a = 1 ∨ a = n))
    (h1 : ∃ b, (s213_231 π).head? = some b ∧ (b = 1 ∨ b = n))
    (h2 : ∃ c, (s213_231 (s213_231 π)).head? = some c ∧ (c = 1 ∨ c = n)) :
    s213_231 π = idPerm n ∨ s213_231 π = revPerm n := by
  rcases h0 with ⟨a, ha_head, ha_ext⟩
  rcases h1 with ⟨b, hb_head, hb_ext⟩
  rcases h2 with ⟨c, hc_head, hc_ext⟩
  cases hpi_eq : π with
  | nil =>
    have hl := isPerm_length hπ
    rw [hpi_eq] at hl
    simp at hl
    omega
  | cons a' π_rest =>
    rw [hpi_eq] at ha_head
    simp only [List.head?_cons, Option.some.injEq] at ha_head
    rw [ha_head]
    have hpi_a : π = a :: π_rest := by rw [hpi_eq, ha_head]
    rw [hpi_a] at hπ hb_head hc_head
    let τ := s213_231 (a :: π_rest)
    have hτ_perm : IsPerm n τ := s213_231_isPerm hπ
    have hτ_len := isPerm_length hτ_perm
    have hτ_nd := isPerm_nodup hτ_perm
    have hτ_last : τ.getLast? = some a := s213_231_last_eq_head a π_rest
    have hτ_head : τ.head? = some b := hb_head
    have hσ_head : (s213_231 τ).head? = some c := hc_head
    change τ = idPerm n ∨ τ = revPerm n
    cases hτ_eq : τ with
    | nil => rw [hτ_eq] at hτ_len; simp at hτ_len; omega
    | cons b' τ_rest =>
      rw [hτ_eq] at hτ_head
      simp only [List.head?_cons, Option.some.injEq] at hτ_head
      rw [hτ_head]
      have hτ_b : τ = b :: τ_rest := by rw [hτ_eq, hτ_head]
      rw [hτ_b] at hτ_perm hτ_nd hτ_len hτ_last hσ_head
      obtain ⟨dl, hsplit_end⟩ := exists_append_singleton_of_getLast (b :: τ_rest) a hτ_last
      have ha_not_dl : a ∉ dl := by
        intro hm
        have hnd_dl := hτ_nd
        rw [hsplit_end, List.nodup_append] at hnd_dl
        exact hnd_dl.2.2 a hm a List.mem_cons_self rfl
      have head_ne_last : ∀ {x y : Nat} {l : List Nat}, l.Nodup → l.length ≥ 2 →
          l.head? = some x → l.getLast? = some y → x ≠ y := by
        intro x y l hndL hlenL hh hl heq
        subst heq
        cases l with
        | nil => simp at hlenL
        | cons x₀ xs₀ =>
          cases xs₀ with
          | nil => simp at hlenL
          | cons x₁ xs₁ =>
            simp only [List.head?_cons, Option.some.injEq] at hh
            subst hh
            have hneL : x₀ :: x₁ :: xs₁ ≠ [] := List.cons_ne_nil x₀ (x₁ :: xs₁)
            have hgl : (x₀ :: x₁ :: xs₁).getLast hneL = x₀ := by
              rw [List.getLast?_eq_some_getLast hneL] at hl
              injection hl
            have hmemL : x₀ ∈ x₁ :: xs₁ := by
              rw [← hgl]
              change (x₁ :: xs₁).getLast (List.cons_ne_nil x₁ xs₁) ∈ x₁ :: xs₁
              exact List.getLast_mem (List.cons_ne_nil x₁ xs₁)
            rw [List.nodup_cons] at hndL
            exact hndL.1 hmemL
      have hba : b ≠ a := head_ne_last hτ_nd (by omega) rfl hτ_last
      have hσ_perm : IsPerm n (s213_231 (b :: τ_rest)) := s213_231_isPerm hτ_perm
      have hσ_nd := isPerm_nodup hσ_perm
      have hσ_len := isPerm_length hσ_perm
      have hσ_last : (s213_231 (b :: τ_rest)).getLast? = some b := s213_231_last_eq_head b τ_rest
      have hcb : c ≠ b := head_ne_last hσ_nd (by omega) hσ_head hσ_last
      have hca : c = a := by omega
      have hout_nil : (feedList (dl ++ [a]) [] []).2 = [] := by
        apply outRev_nil_of_last_exits_first ha_not_dl
        rw [← hsplit_end, ← hca]
        exact hσ_head
      rw [← hsplit_end] at hout_nil
      have hnopops := no_pops_of_feedList_out_nil (b :: τ_rest) [] hout_nil
      rcases hb_ext with hb1 | hbn
      · rw [hb1] at hτ_perm hnopops ⊢
        have hpw : (1 :: τ_rest).Pairwise (· < ·) :=
          pairwise_lt_of_no_pops_min_head hτ_perm (fun pre z suf heq => by
            simpa using hnopops pre z suf heq)
        exact Or.inl (eq_idPerm_of_pairwise hτ_perm hpw)
      · rw [hbn] at hτ_perm hnopops ⊢
        have hpw : (n :: τ_rest).Pairwise (· > ·) :=
          pairwise_gt_of_no_pops_max_head hτ_perm (fun pre z suf heq => by
            simpa using hnopops pre z suf heq)
        exact Or.inr (eq_revPerm_of_pairwise hτ_perm hpw)

/-! ### Part 6: Lemma 5 (`badCount = 0` One-Step Convergence) & Main Theorems -/

theorem forall_rightExtreme_of_badCount_zero :
    ∀ xs : List Nat, xs.Nodup → badCount xs = 0 → ∀ w ∈ xs, IsRightExtreme w xs := by
  intro xs hnd hzero w hw
  have h0 := List.countP_eq_zero.mp hzero w hw
  have hbool : isRightExtremeBool w xs = true := by
    cases hb : isRightExtremeBool w xs
    · simp [hb] at h0
    · rfl
  exact (isRightExtremeBool_iff hnd).mp hbool

theorem forall_rightExtreme_tail {a : Nat} {ρ : List Nat} (hnd : (a :: ρ).Nodup)
    (hall : ∀ w ∈ a :: ρ, IsRightExtreme w (a :: ρ)) :
    ∀ w ∈ ρ, IsRightExtreme w ρ := by
  intro w hw
  rw [List.nodup_cons] at hnd
  rcases hall w (List.mem_cons_of_mem a hw) with ⟨pref, suf, heq, hsuf⟩ | ⟨pref, suf, heq, hsuf⟩
  · cases pref with
    | nil =>
      simp at heq
      exact absurd heq.1.symm (fun he => hnd.1 (he ▸ hw))
    | cons p ps =>
      simp only [List.cons_append, List.cons.injEq] at heq
      exact Or.inl ⟨ps, suf, heq.2, hsuf⟩
  · cases pref with
    | nil =>
      simp at heq
      exact absurd heq.1.symm (fun he => hnd.1 (he ▸ hw))
    | cons p ps =>
      simp only [List.cons_append, List.cons.injEq] at heq
      exact Or.inr ⟨ps, suf, heq.2, hsuf⟩

theorem nodup_split_suf_eq {x : Nat} :
    ∀ {p₁ p₂ s₁ s₂ : List Nat}, (p₁ ++ [x] ++ s₁).Nodup →
      p₁ ++ [x] ++ s₁ = p₂ ++ [x] ++ s₂ → s₁ = s₂
  | [], [], s₁, s₂, _, heq => by simpa using heq
  | [], q :: qs, s₁, s₂, hnd, heq => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
    exfalso
    simp only [List.nil_append, List.cons_append] at hnd
    rw [List.nodup_cons] at hnd
    apply hnd.1
    rw [heq.2]
    simp
  | p :: ps, [], s₁, s₂, hnd, heq => by
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
    exfalso
    simp only [List.cons_append] at hnd
    rw [List.nodup_cons] at hnd
    apply hnd.1
    rw [heq.1]
    simp
  | p :: ps, q :: qs, s₁, s₂, hnd, heq => by
    simp only [List.cons_append, List.cons.injEq] at heq
    rw [List.cons_append, List.cons_append, List.nodup_cons] at hnd
    exact nodup_split_suf_eq hnd.2 heq.2

theorem split_rel_of_all_rightExtreme {rem : List Nat} (hnd : rem.Nodup)
    (hall : ∀ w ∈ rem, IsRightExtreme w rem) :
    ∀ p x suf, rem = p ++ [x] ++ suf → ∀ u ∈ p,
      (∀ y ∈ [x] ++ suf, u < y) ∨ (∀ y ∈ [x] ++ suf, y < u) := by
  intro p x suf heq u hu
  obtain ⟨p₁, p₂, rfl⟩ := exists_split_of_mem p u hu
  have hu_mem : u ∈ rem := by rw [heq]; simp
  have hre := hall u hu_mem
  have heq_u : rem = p₁ ++ [u] ++ (p₂ ++ [x] ++ suf) := by
    rw [heq]
    simp [List.append_assoc]
  rcases hre with ⟨pref', suf', heq', hsuf'⟩ | ⟨pref', suf', heq', hsuf'⟩
  · have hsuf_eq : suf' = p₂ ++ [x] ++ suf :=
      nodup_split_suf_eq (heq' ▸ hnd) (heq'.symm.trans heq_u)
    left
    intro y hy
    apply hsuf'
    rw [hsuf_eq, List.append_assoc]
    exact List.mem_append_right p₂ hy
  · have hsuf_eq : suf' = p₂ ++ [x] ++ suf :=
      nodup_split_suf_eq (heq' ▸ hnd) (heq'.symm.trans heq_u)
    right
    intro y hy
    apply hsuf'
    rw [hsuf_eq, List.append_assoc]
    exact List.mem_append_right p₂ hy

theorem popLoop_s21_step (n x : Nat) (xs : List Nat) (hx_lt : x < n)
    (hrem_lt : ∀ y ∈ xs, y < n) :
    ∀ top outRev : List Nat,
      (∀ t ∈ top, t < n) →
      (∀ y ∈ outRev, y < n) →
      (outRev.reverse ++ top ++ (x :: xs)).Nodup →
      top.Pairwise (· < ·) →
      outRev.reverse.Pairwise (· < ·) →
      (∀ y ∈ outRev.reverse, ∀ u ∈ top ++ (x :: xs), y < u) →
      (∀ t ∈ top, (∀ y ∈ x :: xs, t < y) ∨ (∀ y ∈ x :: xs, y < t)) →
      ∃ top' outRev',
        popLoop x (top ++ [n]) outRev = (top' ++ [n], outRev') ∧
        (∀ t ∈ top', t < n) ∧
        (∀ y ∈ outRev', y < n) ∧
        (outRev'.reverse ++ (x :: top') ++ xs).Nodup ∧
        (x :: top').Pairwise (· < ·) ∧
        outRev'.reverse.Pairwise (· < ·) ∧
        (∀ y ∈ outRev'.reverse, ∀ u ∈ (x :: top') ++ xs, y < u) ∧
        (∀ t ∈ top', (∀ y ∈ xs, t < y) ∨ (∀ y ∈ xs, y < t))
  | [], outRev, _, hout_lt, hnd, _, hout_pw, hout_lt_all, _ => by
    refine ⟨[], outRev, ?_, ?_, hout_lt, ?_, ?_, hout_pw, ?_, ?_⟩
    · simp [popLoop, mustPop_singleton]
    · intro _ hm; cases hm
    · simpa [List.append_assoc] using hnd
    · simp
    · intro y hy u hu; exact hout_lt_all y hy u (by simpa using hu)
    · intro _ hm; cases hm
  | t :: ts, outRev, htop_lt, hout_lt, hnd, htop_pw, hout_pw, hout_lt_all, htop_ext => by
    have ht_lt_n : t < n := htop_lt t List.mem_cons_self
    have hts_lt : ∀ s ∈ ts, s < n := fun s hs => htop_lt s (List.mem_cons_of_mem t hs)
    have ht_ne_x : t ≠ x := by
      have h1 : (outRev.reverse ++ t :: (ts ++ x :: xs)).Nodup := by simpa [List.append_assoc] using hnd
      exact not_mem_of_nodup_perm h1 (List.Perm.refl _) x
        (List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self)) |>.symm
    by_cases htx : t < x
    · have hmn : listMin t (ts ++ [n]) ≤ t := listMin_le t t (ts ++ [n]) (Or.inl rfl)
      have hmx : n ≤ listMax t (ts ++ [n]) := le_listMax t n (ts ++ [n]) (Or.inr (List.mem_append_right ts List.mem_cons_self))
      have hmp : mustPop x (t :: (ts ++ [n])) = true := by
        simp only [mustPop, decide_eq_true_eq]
        omega
      have hpop : popLoop x ((t :: ts) ++ [n]) outRev = popLoop x (ts ++ [n]) (t :: outRev) := by
        rw [List.cons_append, popLoop, hmp]
        rfl
      rw [hpop]
      rw [List.pairwise_cons] at htop_pw
      have ht_all_gt : ∀ y ∈ x :: xs, t < y := by
        rcases htop_ext t List.mem_cons_self with h | h
        · exact h
        · exfalso; have := h x List.mem_cons_self; omega
      have hnd' : ((t :: outRev).reverse ++ ts ++ x :: xs).Nodup := by
        simpa [List.reverse_cons, List.append_assoc] using hnd
      have hout_pw' : (t :: outRev).reverse.Pairwise (· < ·) := by
        rw [List.reverse_cons, List.pairwise_append]
        refine ⟨hout_pw, by simp, fun y hy z h => ?_⟩
        simp at h; subst h
        exact hout_lt_all y hy z (List.mem_append_left _ List.mem_cons_self)
      have hout_lt_all' : ∀ y ∈ (t :: outRev).reverse, ∀ u ∈ ts ++ x :: xs, y < u := by
        intro y hy u hu
        rw [List.reverse_cons, List.mem_append] at hy
        rcases hy with hy1 | hy2
        · exact hout_lt_all y hy1 u (List.mem_cons_of_mem t hu)
        · simp at hy2; subst hy2
          rcases List.mem_append.mp hu with hu1 | hu2
          · exact htop_pw.1 u hu1
          · exact ht_all_gt u hu2
      have hout_lt' : ∀ y ∈ t :: outRev, y < n := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact ht_lt_n
        · exact hout_lt y hy'
      exact popLoop_s21_step n x xs hx_lt hrem_lt ts (t :: outRev)
        hts_lt hout_lt' hnd' htop_pw.2 hout_pw' hout_lt_all'
        (fun s hs => htop_ext s (List.mem_cons_of_mem t hs))
    · have hxt : x < t := by omega
      rw [List.pairwise_cons] at htop_pw
      have hall_gt : ∀ b ∈ t :: (ts ++ [n]), x < b := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb1
        · exact hxt
        · rcases List.mem_append.mp hb1 with hb2 | hb3
          · exact Nat.lt_trans hxt (htop_pw.1 b hb2)
          · simp at hb3; subst hb3; exact hx_lt
      have hmp : mustPop x (t :: (ts ++ [n])) = false := mustPop_of_forall_gt x _ hall_gt
      have hpop : popLoop x ((t :: ts) ++ [n]) outRev = ((t :: ts) ++ [n], outRev) := by
        rw [List.cons_append, popLoop, hmp]
        rfl
      refine ⟨t :: ts, outRev, hpop, htop_lt, hout_lt, ?_, ?_, hout_pw, ?_, ?_⟩
      · have hp_mid : (outRev.reverse ++ x :: (t :: ts) ++ xs).Perm (outRev.reverse ++ (t :: ts) ++ (x :: xs)) := by
          simp only [List.append_assoc]
          exact List.Perm.append_left outRev.reverse (List.perm_middle (a := x) (l₁ := t :: ts) (l₂ := xs)).symm
        exact hp_mid.nodup_iff.mpr hnd
      · rw [List.pairwise_cons]
        refine ⟨fun b hb => ?_, List.pairwise_cons.mpr htop_pw⟩
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact hxt
        · exact Nat.lt_trans hxt (htop_pw.1 b hb')
      · intro y hy u hu
        apply hout_lt_all y hy u
        have hu' : u = x ∨ u ∈ t :: ts ∨ u ∈ xs := by
          rcases List.mem_append.mp hu with hu1 | hu2
          · rcases List.mem_cons.mp hu1 with rfl | hu1'
            · exact Or.inl rfl
            · exact Or.inr (Or.inl hu1')
          · exact Or.inr (Or.inr hu2)
        rcases hu' with rfl | hmem | hxs'
        · exact List.mem_append_right _ List.mem_cons_self
        · exact List.mem_append_left _ hmem
        · exact List.mem_append_right _ (List.mem_cons_of_mem x hxs')
      · intro s hs
        rcases htop_ext s hs with h | h
        · exact Or.inl (fun y hy => h y (List.mem_cons_of_mem x hy))
        · exact Or.inr (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem runStack_s21_idPerm (n : Nat) :
    ∀ rem top outRev : List Nat,
      (∀ x ∈ rem, x < n) →
      (∀ t ∈ top, t < n) →
      (∀ y ∈ outRev, y < n) →
      (outRev.reverse ++ top ++ rem).Nodup →
      top.Pairwise (· < ·) →
      outRev.reverse.Pairwise (· < ·) →
      (∀ y ∈ outRev.reverse, ∀ u ∈ top ++ rem, y < u) →
      (∀ t ∈ top, (∀ y ∈ rem, t < y) ∨ (∀ y ∈ rem, y < t)) →
      (∀ w ∈ rem, IsRightExtreme w rem) →
      (runStack rem (top ++ [n]) outRev).Pairwise (· < ·)
  | [], top, outRev, _, htop_lt, hout_lt, _, htop_pw, hout_pw, hout_lt_all, _, _ => by
    simp only [runStack]
    rw [List.pairwise_append]
    refine ⟨hout_pw, ?_, ?_⟩
    · rw [List.pairwise_append]
      exact ⟨htop_pw, by simp, fun t ht b hb => by simp at hb; subst hb; exact htop_lt t ht⟩
    · intro y hy u hu
      rcases List.mem_append.mp hu with hu1 | hu2
      · exact hout_lt_all y hy u (by simpa using hu1)
      · simp at hu2; subst hu2; exact hout_lt y (List.mem_reverse.mp hy)
  | x :: xs, top, outRev, hrem_lt, htop_lt, hout_lt, hnd, htop_pw, hout_pw, hout_lt_all, htop_ext, hrem_ext => by
    have hx_lt : x < n := hrem_lt x List.mem_cons_self
    have hxs_lt : ∀ y ∈ xs, y < n := fun y hy => hrem_lt y (List.mem_cons_of_mem x hy)
    obtain ⟨top', outRev', hpop, htop'_lt, hout'_lt, hnd', htop'_pw, hout'_pw, hout'_all, htop'_ext⟩ :=
      popLoop_s21_step n x xs hx_lt hxs_lt top outRev htop_lt hout_lt hnd htop_pw hout_pw hout_lt_all htop_ext
    simp only [runStack]
    rw [hpop]
    have hx_top'_ext : ∀ t ∈ x :: top', (∀ y ∈ xs, t < y) ∨ (∀ y ∈ xs, y < t) := by
      intro t ht
      rcases List.mem_cons.mp ht with htx | ht'
      · subst htx
        rcases hrem_ext t List.mem_cons_self with ⟨pref, suf, heq, hsuf⟩ | ⟨pref, suf, heq, hsuf⟩
        · have hsuf_eq : suf = xs := nodup_split_suf_eq (p₂ := []) (by
            have hnd_rem : (t :: xs).Nodup :=
              (List.Pairwise.sublist (List.sublist_append_right _ _) hnd)
            exact heq ▸ hnd_rem) heq.symm
          exact Or.inl (hsuf_eq ▸ hsuf)
        · have hsuf_eq : suf = xs := nodup_split_suf_eq (p₂ := []) (by
            have hnd_rem : (t :: xs).Nodup :=
              (List.Pairwise.sublist (List.sublist_append_right _ _) hnd)
            exact heq ▸ hnd_rem) heq.symm
          exact Or.inr (hsuf_eq ▸ hsuf)
      · exact htop'_ext t ht'
    have hnd_rem : (x :: xs).Nodup := List.Pairwise.sublist (List.sublist_append_right _ _) hnd
    have hxs_ext := forall_rightExtreme_tail hnd_rem hrem_ext
    have htop'_all_lt : ∀ t ∈ x :: top', t < n := by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact hx_lt
      · exact htop'_lt t ht'
    exact runStack_s21_idPerm n xs (x :: top') outRev' hxs_lt htop'_all_lt hout'_lt
      hnd' htop'_pw hout'_pw hout'_all hx_top'_ext hxs_ext

theorem popLoop_s12_step (x : Nat) (xs : List Nat) (hx_gt : 1 < x)
    (hrem_gt : ∀ y ∈ xs, 1 < y) :
    ∀ top outRev : List Nat,
      (∀ t ∈ top, 1 < t) →
      (∀ y ∈ outRev, 1 < y) →
      (outRev.reverse ++ top ++ (x :: xs)).Nodup →
      top.Pairwise (· > ·) →
      outRev.reverse.Pairwise (· > ·) →
      (∀ y ∈ outRev.reverse, ∀ u ∈ top ++ (x :: xs), u < y) →
      (∀ t ∈ top, (∀ y ∈ x :: xs, t < y) ∨ (∀ y ∈ x :: xs, y < t)) →
      ∃ top' outRev',
        popLoop x (top ++ [1]) outRev = (top' ++ [1], outRev') ∧
        (∀ t ∈ top', 1 < t) ∧
        (∀ y ∈ outRev', 1 < y) ∧
        (outRev'.reverse ++ (x :: top') ++ xs).Nodup ∧
        (x :: top').Pairwise (· > ·) ∧
        outRev'.reverse.Pairwise (· > ·) ∧
        (∀ y ∈ outRev'.reverse, ∀ u ∈ (x :: top') ++ xs, u < y) ∧
        (∀ t ∈ top', (∀ y ∈ xs, t < y) ∨ (∀ y ∈ xs, y < t))
  | [], outRev, _, hout_gt, hnd, _, hout_pw, hout_gt_all, _ => by
    refine ⟨[], outRev, ?_, ?_, hout_gt, ?_, ?_, hout_pw, ?_, ?_⟩
    · simp [popLoop, mustPop_singleton]
    · intro _ hm; cases hm
    · simpa [List.append_assoc] using hnd
    · simp
    · intro y hy u hu; exact hout_gt_all y hy u (by simpa using hu)
    · intro _ hm; cases hm
  | t :: ts, outRev, htop_gt, hout_gt, hnd, htop_pw, hout_pw, hout_gt_all, htop_ext => by
    have ht_gt_1 : 1 < t := htop_gt t List.mem_cons_self
    have hts_gt : ∀ s ∈ ts, 1 < s := fun s hs => htop_gt s (List.mem_cons_of_mem t hs)
    have ht_ne_x : t ≠ x := by
      have h1 : (outRev.reverse ++ t :: (ts ++ x :: xs)).Nodup := by simpa [List.append_assoc] using hnd
      exact not_mem_of_nodup_perm h1 (List.Perm.refl _) x
        (List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self)) |>.symm
    by_cases hxt : x < t
    · have hmn : listMin t (ts ++ [1]) ≤ 1 := listMin_le t 1 (ts ++ [1]) (Or.inr (List.mem_append_right ts List.mem_cons_self))
      have hmx : t ≤ listMax t (ts ++ [1]) := le_listMax t t (ts ++ [1]) (Or.inl rfl)
      have hmp : mustPop x (t :: (ts ++ [1])) = true := by
        simp only [mustPop, decide_eq_true_eq]
        omega
      have hpop : popLoop x ((t :: ts) ++ [1]) outRev = popLoop x (ts ++ [1]) (t :: outRev) := by
        rw [List.cons_append, popLoop, hmp]
        rfl
      rw [hpop]
      rw [List.pairwise_cons] at htop_pw
      have ht_all_lt : ∀ y ∈ x :: xs, y < t := by
        rcases htop_ext t List.mem_cons_self with h | h
        · exfalso; have := h x List.mem_cons_self; omega
        · exact h
      have hnd' : ((t :: outRev).reverse ++ ts ++ x :: xs).Nodup := by
        simpa [List.reverse_cons, List.append_assoc] using hnd
      have hout_pw' : (t :: outRev).reverse.Pairwise (· > ·) := by
        rw [List.reverse_cons, List.pairwise_append]
        refine ⟨hout_pw, by simp, fun y hy z h => ?_⟩
        simp at h; subst h
        exact hout_gt_all y hy z (List.mem_append_left _ List.mem_cons_self)
      have hout_gt_all' : ∀ y ∈ (t :: outRev).reverse, ∀ u ∈ ts ++ x :: xs, u < y := by
        intro y hy u hu
        rw [List.reverse_cons, List.mem_append] at hy
        rcases hy with hy1 | hy2
        · exact hout_gt_all y hy1 u (List.mem_cons_of_mem t hu)
        · simp at hy2; subst hy2
          rcases List.mem_append.mp hu with hu1 | hu2
          · exact htop_pw.1 u hu1
          · exact ht_all_lt u hu2
      have hout_gt' : ∀ y ∈ t :: outRev, 1 < y := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact ht_gt_1
        · exact hout_gt y hy'
      exact popLoop_s12_step x xs hx_gt hrem_gt ts (t :: outRev)
        hts_gt hout_gt' hnd' htop_pw.2 hout_pw' hout_gt_all'
        (fun s hs => htop_ext s (List.mem_cons_of_mem t hs))
    · have htx : t < x := by omega
      rw [List.pairwise_cons] at htop_pw
      have hall_lt : ∀ b ∈ t :: (ts ++ [1]), b < x := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb1
        · exact htx
        · rcases List.mem_append.mp hb1 with hb2 | hb3
          · exact Nat.lt_trans (htop_pw.1 b hb2) htx
          · simp at hb3; subst hb3; exact hx_gt
      have hmp : mustPop x (t :: (ts ++ [1])) = false := mustPop_of_forall_lt x _ hall_lt
      have hpop : popLoop x ((t :: ts) ++ [1]) outRev = ((t :: ts) ++ [1], outRev) := by
        rw [List.cons_append, popLoop, hmp]
        rfl
      refine ⟨t :: ts, outRev, hpop, htop_gt, hout_gt, ?_, ?_, hout_pw, ?_, ?_⟩
      · have hp_mid : (outRev.reverse ++ x :: (t :: ts) ++ xs).Perm (outRev.reverse ++ (t :: ts) ++ (x :: xs)) := by
          simp only [List.append_assoc]
          exact List.Perm.append_left outRev.reverse (List.perm_middle (a := x) (l₁ := t :: ts) (l₂ := xs)).symm
        exact hp_mid.nodup_iff.mpr hnd
      · rw [List.pairwise_cons]
        refine ⟨fun b hb => ?_, List.pairwise_cons.mpr htop_pw⟩
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact htx
        · exact Nat.lt_trans (htop_pw.1 b hb') htx
      · intro y hy u hu
        apply hout_gt_all y hy u
        have hu' : u = x ∨ u ∈ t :: ts ∨ u ∈ xs := by
          rcases List.mem_append.mp hu with hu1 | hu2
          · rcases List.mem_cons.mp hu1 with rfl | hu1'
            · exact Or.inl rfl
            · exact Or.inr (Or.inl hu1')
          · exact Or.inr (Or.inr hu2)
        rcases hu' with rfl | hmem | hxs'
        · exact List.mem_append_right _ List.mem_cons_self
        · exact List.mem_append_left _ hmem
        · exact List.mem_append_right _ (List.mem_cons_of_mem x hxs')
      · intro s hs
        rcases htop_ext s hs with h | h
        · exact Or.inl (fun y hy => h y (List.mem_cons_of_mem x hy))
        · exact Or.inr (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem runStack_s12_revPerm :
    ∀ rem top outRev : List Nat,
      (∀ x ∈ rem, 1 < x) →
      (∀ t ∈ top, 1 < t) →
      (∀ y ∈ outRev, 1 < y) →
      (outRev.reverse ++ top ++ rem).Nodup →
      top.Pairwise (· > ·) →
      outRev.reverse.Pairwise (· > ·) →
      (∀ y ∈ outRev.reverse, ∀ u ∈ top ++ rem, u < y) →
      (∀ t ∈ top, (∀ y ∈ rem, t < y) ∨ (∀ y ∈ rem, y < t)) →
      (∀ w ∈ rem, IsRightExtreme w rem) →
      (runStack rem (top ++ [1]) outRev).Pairwise (· > ·)
  | [], top, outRev, _, htop_gt, hout_gt, _, htop_pw, hout_pw, hout_gt_all, _, _ => by
    simp only [runStack]
    rw [List.pairwise_append]
    refine ⟨hout_pw, ?_, ?_⟩
    · rw [List.pairwise_append]
      exact ⟨htop_pw, by simp, fun t ht b hb => by simp at hb; subst hb; exact htop_gt t ht⟩
    · intro y hy u hu
      rcases List.mem_append.mp hu with hu1 | hu2
      · exact hout_gt_all y hy u (by simpa using hu1)
      · simp at hu2; subst hu2; exact hout_gt y (List.mem_reverse.mp hy)
  | x :: xs, top, outRev, hrem_gt, htop_gt, hout_gt, hnd, htop_pw, hout_pw, hout_gt_all, htop_ext, hrem_ext => by
    have hx_gt : 1 < x := hrem_gt x List.mem_cons_self
    have hxs_gt : ∀ y ∈ xs, 1 < y := fun y hy => hrem_gt y (List.mem_cons_of_mem x hy)
    obtain ⟨top', outRev', hpop, htop'_gt, hout'_gt, hnd', htop'_pw, hout'_pw, hout'_all, htop'_ext⟩ :=
      popLoop_s12_step x xs hx_gt hxs_gt top outRev htop_gt hout_gt hnd htop_pw hout_pw hout_gt_all htop_ext
    simp only [runStack]
    rw [hpop]
    have hx_top'_ext : ∀ t ∈ x :: top', (∀ y ∈ xs, t < y) ∨ (∀ y ∈ xs, y < t) := by
      intro t ht
      rcases List.mem_cons.mp ht with htx | ht'
      · subst htx
        rcases hrem_ext t List.mem_cons_self with ⟨pref, suf, heq, hsuf⟩ | ⟨pref, suf, heq, hsuf⟩
        · have hsuf_eq : suf = xs := nodup_split_suf_eq (p₂ := []) (by
            have hnd_rem : (t :: xs).Nodup :=
              (List.Pairwise.sublist (List.sublist_append_right _ _) hnd)
            exact heq ▸ hnd_rem) heq.symm
          exact Or.inl (hsuf_eq ▸ hsuf)
        · have hsuf_eq : suf = xs := nodup_split_suf_eq (p₂ := []) (by
            have hnd_rem : (t :: xs).Nodup :=
              (List.Pairwise.sublist (List.sublist_append_right _ _) hnd)
            exact heq ▸ hnd_rem) heq.symm
          exact Or.inr (hsuf_eq ▸ hsuf)
      · exact htop'_ext t ht'
    have hnd_rem : (x :: xs).Nodup := List.Pairwise.sublist (List.sublist_append_right _ _) hnd
    have hxs_ext := forall_rightExtreme_tail hnd_rem hrem_ext
    have htop'_all_gt : ∀ t ∈ x :: top', 1 < t := by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact hx_gt
      · exact htop'_gt t ht'
    exact runStack_s12_revPerm xs (x :: top') outRev' hxs_gt htop'_all_gt hout'_gt
      hnd' htop'_pw hout'_pw hout'_all hx_top'_ext hxs_ext

/-- Lemma 5 (One-Step Convergence from `badCount π = 0`):
    For every `n ≥ 2` and `π` with `badCount π = 0`, `s213_231 π ∈ {idPerm n, revPerm n}`. -/
theorem lemma5_no_bad_one_step {n : Nat} (hn : n ≥ 2) {π : List Nat}
    (hπ : IsPerm n π) (hzero : badCount π = 0) :
    s213_231 π = idPerm n ∨ s213_231 π = revPerm n := by
  have hnd := isPerm_nodup hπ
  have hlen := isPerm_length hπ
  have hall := forall_rightExtreme_of_badCount_zero π hnd hzero
  cases hpi : π with
  | nil => rw [hpi] at hlen; simp at hlen; omega
  | cons a ρ =>
    have hnd_a : (a :: ρ).Nodup := hpi ▸ hnd
    have hall_a : ∀ w ∈ a :: ρ, IsRightExtreme w (a :: ρ) := hpi ▸ hall
    have ha_ext : a = 1 ∨ a = n := by
      by_cases ha1 : a = 1
      · exact Or.inl ha1
      · by_cases han : a = n
        · exact Or.inr han
        · exfalso
          have hfalse := head_non_extreme_not_rightExtreme (hpi ▸ hπ) ha1 han
          have htrue := (isRightExtremeBool_iff hnd_a).mpr (hall_a a List.mem_cons_self)
          rw [hfalse] at htrue
          exact Bool.noConfusion htrue
    have hρ_nd : ρ.Nodup := (List.nodup_cons.mp hnd_a).2
    have hρ_ext := forall_rightExtreme_tail hnd_a hall_a
    rcases ha_ext with ha1 | han
    · rw [ha1] at hpi hnd_a ⊢
      have hρ_gt : ∀ x ∈ ρ, 1 < x := by
        intro x hx
        have hmem := (isPerm_mem (hpi ▸ hπ)).mp (List.mem_cons_of_mem 1 hx)
        have hne : x ≠ 1 := fun h => (List.nodup_cons.mp hnd_a).1 (h ▸ hx)
        omega
      have hpw : (s213_231 (1 :: ρ)).Pairwise (· > ·) := by
        simp only [s213_231, runStack, popLoop]
        exact runStack_s12_revPerm ρ [] [] hρ_gt
          (fun _ hm => by cases hm) (fun _ hm => by cases hm) hρ_nd
          List.Pairwise.nil List.Pairwise.nil
          (fun _ hm => by cases hm) (fun _ hm => by cases hm) hρ_ext
      exact Or.inr (eq_revPerm_of_pairwise (s213_231_isPerm (hpi ▸ hπ)) hpw)
    · rw [han] at hpi hnd_a ⊢
      have hρ_lt : ∀ x ∈ ρ, x < n := by
        intro x hx
        have hmem := (isPerm_mem (hpi ▸ hπ)).mp (List.mem_cons_of_mem n hx)
        have hne : x ≠ n := fun h => (List.nodup_cons.mp hnd_a).1 (h ▸ hx)
        omega
      have hpw : (s213_231 (n :: ρ)).Pairwise (· < ·) := by
        simp only [s213_231, runStack, popLoop]
        exact runStack_s21_idPerm n ρ [] [] hρ_lt
          (fun _ hm => by cases hm) (fun _ hm => by cases hm) hρ_nd
          List.Pairwise.nil List.Pairwise.nil
          (fun _ hm => by cases hm) (fun _ hm => by cases hm) hρ_ext
      exact Or.inl (eq_idPerm_of_pairwise (s213_231_isPerm (hpi ▸ hπ)) hpw)

/-! ### Part 7: Main Convergence & Periodic-Point Classification Theorems (All `n ≥ 1`) -/

theorem iterSort_add (a b : Nat) (xs : List Nat) :
    iterSort (a + b) xs = iterSort b (iterSort a xs) := by
  induction a generalizing xs with
  | zero => simp [iterSort]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [iterSort]
    exact ih (s213_231 xs)

theorem iterSort_mul (p : Nat) (π : List Nat) (hper : iterSort p π = π) :
    ∀ m, iterSort (m * p) π = π
  | 0 => by simp [iterSort]
  | m + 1 => by
    rw [Nat.succ_mul, iterSort_add, iterSort_mul p π hper m, hper]

theorem convergence_from_badCount {n : Nat} (hn : n ≥ 2) :
    ∀ (m : Nat) (π : List Nat), IsPerm n π → badCount π ≤ m →
      iterSort (3 * m + 1) π = idPerm n ∨ iterSort (3 * m + 1) π = revPerm n
  | 0, π, hπ, hm => by
    have hzero : badCount π = 0 := by omega
    simpa [iterSort] using lemma5_no_bad_one_step hn hπ hzero
  | m + 1, π, hπ, hm => by
    have hnd0 := isPerm_nodup hπ
    have hlen0 := isPerm_length hπ
    have hπ1 : IsPerm n (s213_231 π) := s213_231_isPerm hπ
    have hπ2 : IsPerm n (s213_231 (s213_231 π)) := s213_231_isPerm hπ1
    have hnd1 := isPerm_nodup hπ1
    have hnd2 := isPerm_nodup hπ2
    have hlen1 := isPerm_length hπ1
    have hlen2 := isPerm_length hπ2
    obtain ⟨a, ha_h⟩ := head?_eq_some_of_ne_nil (show π ≠ [] by intro h; rw [h] at hlen0; simp at hlen0; omega)
    obtain ⟨b, hb_h⟩ := head?_eq_some_of_ne_nil (show s213_231 π ≠ [] by intro h; rw [h] at hlen1; simp at hlen1; omega)
    obtain ⟨c, hc_h⟩ := head?_eq_some_of_ne_nil (show s213_231 (s213_231 π) ≠ [] by intro h; rw [h] at hlen2; simp at hlen2; omega)
    by_cases ha_ext : a = 1 ∨ a = n
    · by_cases hb_ext : b = 1 ∨ b = n
      · by_cases hc_ext : c = 1 ∨ c = n
        · have hstep1 := lemma4_consecutive_extreme_starts hn hπ ⟨a, ha_h, ha_ext⟩ ⟨b, hb_h, hb_ext⟩ ⟨c, hc_h, hc_ext⟩
          have heq : 3 * (m + 1) + 1 = 1 + (3 * m + 3) := by omega
          rw [heq, iterSort_add]
          exact iterSort_id_or_rev (3 * m + 3) n (by simpa [iterSort] using hstep1)
        · have hc1 : c ≠ 1 := fun h => hc_ext (Or.inl h)
          have hcn : c ≠ n := fun h => hc_ext (Or.inr h)
          cases hc_eq : s213_231 (s213_231 π) with
          | nil => rw [hc_eq] at hc_h; simp at hc_h
          | cons c' rest2 =>
            rw [hc_eq] at hc_h; simp at hc_h; subst hc_h
            have hdrop := badCount_drop_of_non_extreme_head (hc_eq ▸ hπ2) hc1 hcn
            have hmono1 := badCount_mono hnd1
            have hmono0 := badCount_mono hnd0
            have hbad3 : badCount (iterSort 3 π) ≤ m := by
              simp only [iterSort]
              rw [← hc_eq] at hdrop
              omega
            have heq : 3 * (m + 1) + 1 = 3 + (3 * m + 1) := by omega
            rw [heq, iterSort_add]
            exact convergence_from_badCount hn m (iterSort 3 π) (iterSort_isPerm 3 hπ) hbad3
      · have hb1 : b ≠ 1 := fun h => hb_ext (Or.inl h)
        have hbn : b ≠ n := fun h => hb_ext (Or.inr h)
        cases hb_eq : s213_231 π with
        | nil => rw [hb_eq] at hb_h; simp at hb_h
        | cons b' rest1 =>
          rw [hb_eq] at hb_h; simp at hb_h; subst hb_h
          have hdrop := badCount_drop_of_non_extreme_head (hb_eq ▸ hπ1) hb1 hbn
          have hmono2 := badCount_mono hnd2
          have hmono0 := badCount_mono hnd0
          have hbad3 : badCount (iterSort 3 π) ≤ m := by
            simp only [iterSort]
            rw [← hb_eq] at hdrop
            omega
          have heq : 3 * (m + 1) + 1 = 3 + (3 * m + 1) := by omega
          rw [heq, iterSort_add]
          exact convergence_from_badCount hn m (iterSort 3 π) (iterSort_isPerm 3 hπ) hbad3
    · have ha1 : a ≠ 1 := fun h => ha_ext (Or.inl h)
      have han : a ≠ n := fun h => ha_ext (Or.inr h)
      cases ha_eq : π with
      | nil => rw [ha_eq] at ha_h; simp at ha_h
      | cons a' rest0 =>
        rw [ha_eq] at ha_h; simp at ha_h
        have hpi_a : π = a :: rest0 := by rw [ha_eq, ha_h]
        have hdrop := badCount_drop_of_non_extreme_head (hpi_a ▸ hπ) ha1 han
        rw [← hpi_a] at hdrop
        have hmono2 := badCount_mono hnd2
        have hmono1 := badCount_mono hnd1
        have hbad3 : badCount (iterSort 3 π) ≤ m := by
          simp only [iterSort]
          omega
        have heq : 3 * (m + 1) + 1 = 3 + (3 * m + 1) := by omega
        rw [← ha_eq, heq, iterSort_add]
        exact convergence_from_badCount hn m (iterSort 3 π) (iterSort_isPerm 3 hπ) hbad3

/--
  Main Convergence Theorem (all `n ≥ 3`):
  Starting from any permutation `π ∈ S_n`, at most `3 * n - 7` passes of the literal
  `{213, 231}`-avoiding stack-sorting map reach `{idPerm n, revPerm n}`.
-/
theorem berlow_convergence_3n_minus_7 (n : Nat) (hn : n ≥ 3) (π : List Nat) (hπ : IsPerm n π) :
    iterSortLit (3 * n - 7) π = idPerm n ∨ iterSortLit (3 * n - 7) π = revPerm n := by
  rw [iterSortLit_eq_iterSort]
  have hle := badCount_le_sub_two (by omega) hπ
  have hlen := isPerm_length hπ
  by_cases hfull : badCount π = n - 2
  · have hnd := isPerm_nodup hπ
    cases hpi : π with
    | nil => rw [hpi] at hlen; simp at hlen; omega
    | cons a rest =>
      have ha_bad : a ≠ 1 ∧ a ≠ n := by
        by_cases ha1 : a = 1
        · exfalso
          have ha_true : isRightExtremeBool a (a :: rest) = true := by
            subst ha1
            apply (isRightExtremeBool_iff (hpi ▸ hnd)).mpr
            exact Or.inl ⟨[], rest, rfl, fun y hy => by
              have := ((isPerm_mem (hpi ▸ hπ)).mp (List.mem_cons_of_mem 1 hy)).1
              have hne : y ≠ 1 := fun h => (List.nodup_cons.mp (hpi ▸ hnd)).1 (h ▸ hy)
              omega⟩
          have hrev_len : rest.reverse.length ≥ 2 := by
            have := congrArg List.length hpi
            rw [hlen] at this
            simp at this ⊢; omega
          cases hr0 : rest.reverse with
          | nil => rw [hr0] at hrev_len; simp at hrev_len
          | cons v r1 =>
            cases hr1 : r1 with
            | nil => rw [hr0, hr1] at hrev_len; simp at hrev_len
            | cons u r2 =>
              have hrest_eq : rest = r2.reverse ++ [u, v] := by
                have := congrArg List.reverse hr0
                rw [List.reverse_reverse, hr1, List.reverse_cons, List.reverse_cons] at this
                simpa [List.append_assoc] using this
              have hπ_split : a :: rest = (a :: r2.reverse) ++ [u, v] := by
                rw [hrest_eq]; simp
              have hnd_sp : ((a :: r2.reverse) ++ [u, v]).Nodup := hπ_split ▸ hpi ▸ hnd
              have ⟨hu, hv⟩ := last_two_rightExtreme hnd_sp
              have ha_sp : isRightExtremeBool a ((a :: r2.reverse) ++ [u, v]) = true :=
                hπ_split ▸ ha_true
              have hr2_len : r2.reverse.length = n - 3 := by
                have hls := congrArg List.length hπ_split
                rw [← hpi, hlen] at hls
                simp at hls ⊢
                omega
              have hbc_lt : badCount (a :: rest) ≤ n - 3 := by
                rw [hπ_split]
                simp only [badCount, List.countP_append, List.countP_cons, List.countP_nil,
                  ha_sp, hu, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
                have hcl : List.countP (fun x => !isRightExtremeBool x ((a :: r2.reverse) ++ [u, v])) r2.reverse ≤ r2.reverse.length :=
                  List.countP_le_length
                omega
              rw [← hpi, hfull] at hbc_lt
              omega
        · by_cases han : a = n
          · exfalso
            have ha_true : isRightExtremeBool a (a :: rest) = true := by
              rw [han] at hpi ⊢
              apply (isRightExtremeBool_iff (hpi ▸ hnd)).mpr
              exact Or.inr ⟨[], rest, rfl, fun y hy => by
                have := ((isPerm_mem (hpi ▸ hπ)).mp (List.mem_cons_of_mem n hy)).2
                have hne : y ≠ n := fun h => (List.nodup_cons.mp (hpi ▸ hnd)).1 (h ▸ hy)
                omega⟩
            have hrev_len : rest.reverse.length ≥ 2 := by
              have := congrArg List.length hpi
              rw [hlen] at this
              simp at this ⊢; omega
            cases hr0 : rest.reverse with
            | nil => rw [hr0] at hrev_len; simp at hrev_len
            | cons v r1 =>
              cases hr1 : r1 with
              | nil => rw [hr0, hr1] at hrev_len; simp at hrev_len
              | cons u r2 =>
                have hrest_eq : rest = r2.reverse ++ [u, v] := by
                  have := congrArg List.reverse hr0
                  rw [List.reverse_reverse, hr1, List.reverse_cons, List.reverse_cons] at this
                  simpa [List.append_assoc] using this
                have hπ_split : a :: rest = (a :: r2.reverse) ++ [u, v] := by
                  rw [hrest_eq]; simp
                have hnd_sp : ((a :: r2.reverse) ++ [u, v]).Nodup := hπ_split ▸ hpi ▸ hnd
                have ⟨hu, hv⟩ := last_two_rightExtreme hnd_sp
                have ha_sp : isRightExtremeBool a ((a :: r2.reverse) ++ [u, v]) = true :=
                  hπ_split ▸ ha_true
                have hr2_len : r2.reverse.length = n - 3 := by
                  have hls := congrArg List.length hπ_split
                  rw [← hpi, hlen] at hls
                  simp at hls ⊢
                  omega
                have hbc_lt : badCount (a :: rest) ≤ n - 3 := by
                  rw [hπ_split]
                  simp only [badCount, List.countP_append, List.countP_cons, List.countP_nil,
                    ha_sp, hu, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
                  have hcl : List.countP (fun x => !isRightExtremeBool x ((a :: r2.reverse) ++ [u, v])) r2.reverse ≤ r2.reverse.length :=
                    List.countP_le_length
                  omega
                rw [← hpi, hfull] at hbc_lt
                omega
          · exact ⟨ha1, han⟩
      have hdrop := badCount_drop_of_non_extreme_head (hpi ▸ hπ) ha_bad.1 ha_bad.2
      rw [← hpi] at hdrop
      have hbad1 : badCount (iterSort 1 π) ≤ n - 3 := by
        simp only [iterSort]
        omega
      have hsteps : 3 * n - 7 = 1 + (3 * (n - 3) + 1) := by omega
      rw [← hpi, hsteps, iterSort_add]
      exact convergence_from_badCount (by omega) (n - 3) (iterSort 1 π) (iterSort_isPerm 1 hπ) hbad1
  · have hbad_le : badCount π ≤ n - 3 := by omega
    have heq : 3 * n - 7 = (3 * (n - 3) + 1) + 1 := by omega
    rw [heq, iterSort_add]
    exact iterSort_id_or_rev 1 n (convergence_from_badCount (by omega) (n - 3) π hπ hbad_le)

/--
  Complete Resolution of Berlow's Conjecture 5.1 / Zhang's Conjecture 4.2 for `T = {213, 231}`
  (all `n ≥ 1` and all periods `p ≥ 1`, stated directly in terms of `iterSortLit`):
  The only periodic points of `s_{213, 231}` on `S_n` are `idPerm n` and `revPerm n`.
-/
theorem berlow_conjecture_5_1_213_231 (n : Nat) (hn : n ≥ 1) (π : List Nat) (hπ : IsPerm n π)
    (p : Nat) (hp : p ≥ 1) (hper : iterSortLit p π = π) :
    π = idPerm n ∨ π = revPerm n := by
  rw [iterSortLit_eq_iterSort] at hper
  by_cases hn1 : n = 1
  · subst hn1
    have hp1 : π.Perm [1] := hπ
    cases hpi : π with
    | nil => have := hp1.length_eq; rw [hpi] at this; simp at this
    | cons a as =>
      cases as with
      | nil =>
        have ha : a ∈ [1] := hp1.mem_iff.mp (by rw [hpi]; exact List.mem_cons_self)
        simp at ha; subst ha
        exact Or.inl rfl
      | cons b bs => have := hp1.length_eq; rw [hpi] at this; simp at this
  · by_cases hn2 : n = 2
    · subst hn2
      have hp2 : π.Perm [1, 2] := hπ
      have hlen := hp2.length_eq
      cases hpi : π with
      | nil => rw [hpi] at hlen; simp at hlen
      | cons a as =>
        cases as with
        | nil => rw [hpi] at hlen; simp at hlen
        | cons b bs =>
          cases bs with
          | cons c cs => rw [hpi] at hlen; simp at hlen
          | nil =>
            rw [hpi] at hp2
            have h1 : 1 ∈ [a, b] := hp2.mem_iff.mpr (by simp)
            have h2 : 2 ∈ [a, b] := hp2.mem_iff.mpr (by simp)
            have hnd : ([a, b] : List Nat).Nodup := hp2.nodup_iff.mpr (by decide)
            simp at h1 h2 hnd
            rcases h1 with h1a | h1b <;> rcases h2 with h2a | h2b
            · omega
            · rw [← h1a, ← h2b]; exact Or.inl rfl
            · rw [← h1b, ← h2a]; exact Or.inr rfl
            · omega
    · have hn3 : n ≥ 3 := by omega
      have hm1 : (3 * n) * 1 ≤ (3 * n) * p := Nat.mul_le_mul_left (3 * n) hp
      have hge : (3 * n) * p ≥ 3 * n - 7 := by omega
      have hmul : iterSort ((3 * n) * p) π = π := iterSort_mul p π hper (3 * n)
      have hconv := berlow_convergence_3n_minus_7 n hn3 π hπ
      rw [iterSortLit_eq_iterSort] at hconv
      have hdiff : (3 * n) * p = (3 * n - 7) + ((3 * n) * p - (3 * n - 7)) := by omega
      have hres := iterSort_id_or_rev ((3 * n) * p - (3 * n - 7)) n hconv
      rw [← iterSort_add, ← hdiff, hmul] at hres
      exact hres

#print axioms mustPop_singleton
#print axioms popLoop_preserves_bottom
#print axioms runStack_bottom_last
#print axioms s213_231_last_eq_head
#print axioms cycle_S4
#print axioms worst_case_S5
#print axioms s213_231_literal_eq
#print axioms berlow_convergence_3n_minus_7
#print axioms berlow_conjecture_5_1_213_231

end BerlowStackSorting
