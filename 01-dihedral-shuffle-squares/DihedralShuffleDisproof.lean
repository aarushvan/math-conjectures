/-
  Self-contained Lean 4 formalization disproving Conjecture 2 of
  Grytczuk, Pawlik, and Pleszczynski, "Variations on shuffle squares" (arXiv:2308.13882v2):
  "Every even ternary word is a dihedral shuffle square."

  Counterexample family for all n >= 4 (even length 2*n >= 8):
    W_n = 0^(2n-5) 1 1 0 2 2
  Minimal instance at n = 4 (length 8): W_4 = 00011022.

  Zero external dependencies (no Mathlib, fully kernel-verified).
-/

namespace DihedralShuffleDisproof

def getZero (u : List (Fin 3)) (i : Nat) : Fin 3 :=
  match u, i with
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => getZero xs i

theorem getZero_append (l₁ l₂ : List (Fin 3)) (i : Nat) :
    getZero (l₁ ++ l₂) i = if i < l₁.length then getZero l₁ i else getZero l₂ (i - l₁.length) := by
  induction l₁ generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp [getZero]
    | succ k =>
      simp only [List.cons_append, List.length_cons, getZero]
      rw [ih k]
      by_cases hk : k < xs.length
      · have hk1 : k + 1 < xs.length + 1 := by omega
        simp [hk, hk1]
      · have hk1 : ¬ (k + 1 < xs.length + 1) := by omega
        have hsub : k + 1 - (xs.length + 1) = k - xs.length := by omega
        simp [hk, hk1, hsub]

theorem getZero_replicate_zero (k i : Nat) :
    getZero (List.replicate k (0 : Fin 3)) i = 0 := by
  induction k generalizing i with
  | zero => simp [getZero]
  | succ k ih =>
    rw [List.replicate_succ]
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem map_getZero_range (u : List (Fin 3)) :
    (List.range u.length).map (getZero u) = u := by
  induction u with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    have hcomp : (getZero (x :: xs) ∘ Nat.succ) = getZero xs := rfl
    rw [hcomp, ih]
    rfl

theorem getZero_map_range (n : Nat) (f : Nat → Fin 3) (i : Nat) (hi : i < n) :
    getZero ((List.range n).map f) i = f i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, getZero_append]
    rw [List.length_map, List.length_range]
    split
    · next hlt => exact ih i hlt
    · next hge =>
      have heq : i = n := by omega
      subst heq
      simp [getZero]

/-- Splitting a word into two disjoint subwords via a boolean mask. -/
def splitTrue : List Bool → List α → List α
  | true :: bs, x :: xs => x :: splitTrue bs xs
  | false :: bs, _ :: xs => splitTrue bs xs
  | _, _ => []

def splitFalse : List Bool → List α → List α
  | false :: bs, x :: xs => x :: splitFalse bs xs
  | true :: bs, _ :: xs => splitFalse bs xs
  | _, _ => []

theorem splitTrue_append {α : Type} (m₁ m₂ : List Bool) (w₁ w₂ : List α)
    (h : m₁.length = w₁.length) :
    splitTrue (m₁ ++ m₂) (w₁ ++ w₂) = splitTrue m₁ w₁ ++ splitTrue m₂ w₂ := by
  induction m₁ generalizing w₁ with
  | nil =>
    cases w₁ with
    | nil => rfl
    | cons _ _ => simp at h
  | cons b bs ih =>
    cases w₁ with
    | nil => simp at h
    | cons x xs =>
      simp only [List.length_cons] at h
      cases b <;> simp [splitTrue, ih xs (by omega)]

theorem splitFalse_append {α : Type} (m₁ m₂ : List Bool) (w₁ w₂ : List α)
    (h : m₁.length = w₁.length) :
    splitFalse (m₁ ++ m₂) (w₁ ++ w₂) = splitFalse m₁ w₁ ++ splitFalse m₂ w₂ := by
  induction m₁ generalizing w₁ with
  | nil =>
    cases w₁ with
    | nil => rfl
    | cons _ _ => simp at h
  | cons b bs ih =>
    cases w₁ with
    | nil => simp at h
    | cons x xs =>
      simp only [List.length_cons] at h
      cases b <;> simp [splitFalse, ih xs (by omega)]

theorem splitTrue_replicate_zero (m : List Bool) (k : Nat) (h : m.length = k) :
    splitTrue m (List.replicate k (0 : Fin 3)) = List.replicate (m.count true) 0 := by
  induction m generalizing k with
  | nil =>
    cases k with
    | zero => rfl
    | succ _ => simp at h
  | cons b bs ih =>
    cases k with
    | zero => simp at h
    | succ k =>
      simp only [List.length_cons] at h
      cases b <;> simp [splitTrue, List.replicate_succ, ih k (by omega)]

theorem splitFalse_replicate_zero (m : List Bool) (k : Nat) (h : m.length = k) :
    splitFalse m (List.replicate k (0 : Fin 3)) = List.replicate (m.count false) 0 := by
  induction m generalizing k with
  | nil =>
    cases k with
    | zero => rfl
    | succ _ => simp at h
  | cons b bs ih =>
    cases k with
    | zero => simp at h
    | succ k =>
      simp only [List.length_cons] at h
      cases b <;> simp [splitFalse, List.replicate_succ, ih k (by omega)]

theorem split_count_sum {α : Type} [BEq α] (m : List Bool) (w : List α) (c : α)
    (h : m.length = w.length) :
    (splitTrue m w).count c + (splitFalse m w).count c = w.count c := by
  induction m generalizing w with
  | nil => cases w <;> simp_all [splitTrue, splitFalse]
  | cons b bs ih =>
    cases w with
    | nil => simp at h
    | cons x xs =>
      simp only [List.length_cons] at h
      have ih' := ih xs (by omega)
      cases b <;> simp [splitTrue, splitFalse, List.count_cons] <;> omega

/-- Dihedral group D_n acting on positions {0, ..., n-1}. -/
inductive DihedralPerm (n : Nat) where
  | rot (k : Nat)
  | refl (k : Nat)

def DihedralPerm.applyIdx (n : Nat) : DihedralPerm n → Nat → Nat
  | .rot k, i => (i + k) % n
  | .refl k, i => (k + n - (i % n)) % n

def DihedralPerm.apply {n : Nat} (γ : DihedralPerm n) (u : List (Fin 3)) : List (Fin 3) :=
  (List.range u.length).map (fun i => getZero u (DihedralPerm.applyIdx n γ i))

theorem DihedralPerm.apply_length {n : Nat} (γ : DihedralPerm n) (u : List (Fin 3)) :
    (γ.apply u).length = u.length := by
  simp [DihedralPerm.apply, List.length_map, List.length_range]

/--
  Definition of a dihedral shuffle square matching arXiv:2308.13882v2 Section 2.1 & 2.3:
  W of length 2n splits into two disjoint subwords U, V of length n such that
  V = gamma(U) or U = gamma(V) for some gamma in D_n.
-/
def IsDihedralShuffleSquare (n : Nat) (W : List (Fin 3)) : Prop :=
  ∃ mask : List Bool,
    mask.length = W.length ∧
    (splitTrue mask W).length = n ∧
    (splitFalse mask W).length = n ∧
    ∃ γ : DihedralPerm n,
      splitFalse mask W = γ.apply (splitTrue mask W) ∨
      splitTrue mask W = γ.apply (splitFalse mask W)

/-- Counterexample family W_n = 0^(2n-5) 1 1 0 2 2. -/
def W_n (n : Nat) : List (Fin 3) :=
  List.replicate (2 * n - 5) 0 ++ [1, 1, 0, 2, 2]

theorem W_n_length (n : Nat) (hn : n ≥ 4) : (W_n n).length = 2 * n := by
  simp [W_n, List.length_append, List.length_replicate]
  omega

theorem W_n_even (n : Nat) (hn : n ≥ 4) :
    (W_n n).count 0 = 2 * n - 4 ∧ (W_n n).count 1 = 2 ∧ (W_n n).count 2 = 2 := by
  simp [W_n, List.count_append, List.count_replicate]
  omega

/-- General bijection lemma on List.range n. -/
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

theorem range_perm_of_bij (n : Nat) (f g : Nat → Nat)
    (hf : ∀ i, i < n → f i < n)
    (hg : ∀ j, j < n → g j < n)
    (hfg : ∀ i, i < n → g (f i) = i)
    (hgf : ∀ j, j < n → f (g j) = j) :
    ((List.range n).map f).Perm (List.range n) := by
  have hdn : ((List.range n).map f).Nodup := by
    apply nodup_map_of_inj_on (List.range n) f List.nodup_range
    intro x hx y hy hxy
    rw [List.mem_range] at hx hy
    have h1 := hfg x hx
    have h2 := hfg y hy
    rw [hxy] at h1
    omega
  rw [List.perm_ext_iff_of_nodup hdn List.nodup_range]
  intro a
  constructor
  · intro ha
    rcases List.mem_map.mp ha with ⟨i, hi, rfl⟩
    rw [List.mem_range] at hi ⊢
    exact hf i hi
  · intro ha
    rw [List.mem_range] at ha
    apply List.mem_map.mpr
    exact ⟨g a, List.mem_range.mpr (hg a ha), hgf a ha⟩

theorem rot_bij (n k : Nat) (hn : n > 0) :
    ((List.range n).map (fun i => (i + k) % n)).Perm (List.range n) := by
  let f := fun i => (i + k) % n
  let g := fun j => (j + (n - k % n)) % n
  apply range_perm_of_bij n f g
  · intro i _; exact Nat.mod_lt _ hn
  · intro j _; exact Nat.mod_lt _ hn
  · intro i hi
    dsimp [f, g]
    have hk : k % n < n := Nat.mod_lt k hn
    have hdiv := Nat.div_add_mod k n
    rw [Nat.mod_add_mod]
    have hsum : i + k + (n - k % n) = n * (k / n + 1) + i := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [hsum, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hi]
  · intro j hj
    dsimp [f, g]
    have hk : k % n < n := Nat.mod_lt k hn
    have hdiv := Nat.div_add_mod k n
    rw [Nat.mod_add_mod]
    have hsum : j + (n - k % n) + k = n * (k / n + 1) + j := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [hsum, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hj]

theorem refl_involution (n k i : Nat) (hn : n > 0) (hi : i < n) :
    (k + n - (((k + n - i) % n) % n)) % n = i := by
  have hk : k + n - i = n * ((k + n - i) / n) + (k + n - i) % n :=
    (Nat.div_add_mod (k + n - i) n).symm
  have hr : (k + n - i) % n < n := Nat.mod_lt _ hn
  rw [Nat.mod_eq_of_lt hr]
  have hsum : k + n - (k + n - i) % n = n * ((k + n - i) / n) + i := by omega
  rw [hsum, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hi]

theorem refl_bij (n k : Nat) (hn : n > 0) :
    ((List.range n).map (fun i => (k + n - (i % n)) % n)).Perm (List.range n) := by
  let f := fun i => (k + n - (i % n)) % n
  apply range_perm_of_bij n f f
  · intro i _; exact Nat.mod_lt _ hn
  · intro j _; exact Nat.mod_lt _ hn
  · intro i hi
    dsimp [f]
    rw [Nat.mod_eq_of_lt hi]
    exact refl_involution n k i hn hi
  · intro j hj
    dsimp [f]
    rw [Nat.mod_eq_of_lt hj]
    exact refl_involution n k j hn hj

theorem applyIdx_perm {n : Nat} (γ : DihedralPerm n) (hn : n > 0) :
    ((List.range n).map (DihedralPerm.applyIdx n γ)).Perm (List.range n) := by
  cases γ with
  | rot k => exact rot_bij n k hn
  | refl k => exact refl_bij n k hn

theorem DihedralPerm.apply_perm {n : Nat} (γ : DihedralPerm n) (u : List (Fin 3))
    (hn : n > 0) (hu : u.length = n) :
    (γ.apply u).Perm u := by
  unfold DihedralPerm.apply
  rw [hu]
  have hp : ((List.range n).map (DihedralPerm.applyIdx n γ)).Perm (List.range n) := applyIdx_perm γ hn
  have hmap := hp.map (getZero u)
  rw [List.map_map] at hmap
  have h1 : (getZero u ∘ DihedralPerm.applyIdx n γ) = fun i => getZero u (DihedralPerm.applyIdx n γ i) := rfl
  rw [h1] at hmap
  have hu2 : (List.range n).map (getZero u) = u := by
    rw [← hu]
    exact map_getZero_range u
  rw [hu2] at hmap
  exact hmap

theorem DihedralPerm.count_apply {n : Nat} (γ : DihedralPerm n) (u : List (Fin 3))
    (hn : n > 0) (hu : u.length = n) (c : Fin 3) :
    (γ.apply u).count c = u.count c :=
  (DihedralPerm.apply_perm γ u hn hu).count_eq c

/-- Cyclic adjacent zero pairs: number of i in {0, ..., |u|-1} with u[i] = 0 and u[(i+1) % |u|] = 0. -/
def cyclicAdjZeros (u : List (Fin 3)) : Nat :=
  (List.range u.length).countP
    (fun i => decide (getZero u i = 0 ∧ getZero u ((i + 1) % u.length) = 0))

theorem rot_succ_mod (n k i : Nat) :
    ((i + 1) % n + k) % n = ((i + k) % n + 1) % n := by
  rw [Nat.mod_add_mod, Nat.add_right_comm, ← Nat.mod_add_mod]

theorem refl_succ_mod (n k i : Nat) (hi : i < n) :
    (((k + n - ((i + 1) % n)) % n) + 1) % n = (k + n - (i % n)) % n := by
  rw [Nat.mod_eq_of_lt hi, Nat.mod_add_mod]
  by_cases hlt : i + 1 < n
  · rw [Nat.mod_eq_of_lt hlt]
    have heq : k + n - (i + 1) + 1 = k + n - i := by omega
    rw [heq]
  · have heq : i + 1 = n := by omega
    rw [heq, Nat.mod_self, Nat.sub_zero]
    have h1 : k + n + 1 = (k + n - i) + n := by omega
    rw [h1, Nat.add_mod_right]

theorem refl_shift_bij (n k : Nat) (hn : n > 0) :
    ((List.range n).map (fun i => (k + n - ((i + 1) % n)) % n)).Perm (List.range n) := by
  let g := fun i => (k + n - ((i + 1) % n)) % n
  have hg_lt : ∀ i, i < n → g i < n := fun i _ => Nat.mod_lt _ hn
  have h_eq_shifted : ∀ i, i < n → g i = (k + n - 1 - i) % n := by
    intro i hi
    dsimp [g]
    by_cases hlt : i + 1 < n
    · rw [Nat.mod_eq_of_lt hlt]
      have : k + n - (i + 1) = k + n - 1 - i := by omega
      rw [this]
    · have hi1 : i + 1 = n := by omega
      rw [hi1, Nat.mod_self, Nat.sub_zero]
      have h1 : k + n - 1 - i = k := by omega
      rw [h1, Nat.add_mod_right]
  have hinv : ∀ i, i < n → g (g i) = i := by
    intro i hi
    have hgi_lt : g i < n := hg_lt i hi
    rw [h_eq_shifted (g i) hgi_lt, h_eq_shifted i hi]
    have ha : k + n - 1 - i = n * ((k + n - 1 - i) / n) + (k + n - 1 - i) % n :=
      (Nat.div_add_mod (k + n - 1 - i) n).symm
    have hsum : k + n - 1 - (k + n - 1 - i) % n = n * ((k + n - 1 - i) / n) + i := by omega
    rw [hsum, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hi]
  exact range_perm_of_bij n g g hg_lt hg_lt hinv hinv

theorem cyclicAdjZeros_apply {n : Nat} (hn : n > 0) (u : List (Fin 3)) (hu : u.length = n)
    (γ : DihedralPerm n) :
    cyclicAdjZeros (γ.apply u) = cyclicAdjZeros u := by
  unfold cyclicAdjZeros
  rw [γ.apply_length, hu]
  let pU : Nat → Bool := fun j => decide (getZero u j = 0 ∧ getZero u ((j + 1) % n) = 0)
  let pV : Nat → Bool := fun i =>
    decide (getZero (γ.apply u) i = 0 ∧ getZero (γ.apply u) ((i + 1) % n) = 0)
  have hget : ∀ i, i < n → getZero (γ.apply u) i = getZero u (DihedralPerm.applyIdx n γ i) := by
    intro i hi
    unfold DihedralPerm.apply
    rw [hu]
    exact getZero_map_range n (fun j => getZero u (DihedralPerm.applyIdx n γ j)) i hi
  cases γ with
  | rot k =>
    let f := fun i => (i + k) % n
    have hp_eq : (List.range n).countP pV = ((List.range n).map f).countP pU := by
      rw [List.countP_map]
      apply List.countP_congr
      intro i hi
      rw [List.mem_range] at hi
      dsimp [pV, pU, f, Function.comp]
      simp only [decide_eq_true_eq]
      rw [hget i hi, hget ((i + 1) % n) (Nat.mod_lt _ hn)]
      simp only [DihedralPerm.applyIdx]
      rw [rot_succ_mod n k i]
    rw [hp_eq]
    exact (rot_bij n k hn).countP_eq pU
  | refl k =>
    let σ := fun i => (k + n - ((i + 1) % n)) % n
    have hp_eq : (List.range n).countP pV = ((List.range n).map σ).countP pU := by
      rw [List.countP_map]
      apply List.countP_congr
      intro i hi
      rw [List.mem_range] at hi
      dsimp [pV, pU, σ, Function.comp]
      simp only [decide_eq_true_eq]
      rw [hget i hi, hget ((i + 1) % n) (Nat.mod_lt _ hn)]
      simp only [DihedralPerm.applyIdx]
      have hmod : (i + 1) % n % n = (i + 1) % n := Nat.mod_eq_of_lt (Nat.mod_lt _ hn)
      rw [hmod, refl_succ_mod n k i hi, and_comm]
    rw [hp_eq]
    exact (refl_shift_bij n k hn).countP_eq pU

/-- Exact cyclicAdjZeros counts for the two forced subwords of W_n. -/
theorem cyclicAdjZeros_templateA (m : Nat) (hm : m ≥ 1) :
    cyclicAdjZeros (List.replicate m (0 : Fin 3) ++ [1, 2]) = m - 1 := by
  let u := List.replicate m (0 : Fin 3) ++ [1, 2]
  have hlen : u.length = m + 2 := by simp [u, List.length_append, List.length_replicate]
  unfold cyclicAdjZeros
  rw [hlen]
  let p : Nat → Bool := fun i => decide (getZero u i = 0 ∧ getZero u ((i + 1) % (m + 2)) = 0)
  have hp_val : ∀ i, i < m + 2 → p i = decide (i < m - 1) := by
    intro i hi
    dsimp [p, u]
    rw [getZero_append, getZero_append, List.length_replicate]
    by_cases h1 : i < m - 1
    · have hi1 : i < m := by omega
      have hs1 : (i + 1) % (m + 2) = i + 1 := Nat.mod_eq_of_lt (by omega)
      have hs2 : i + 1 < m := by omega
      simp [h1, hi1, hs1, hs2, getZero_replicate_zero]
    · have hi1_not : ¬ (i < m - 1) := h1
      by_cases hi_eq : i = m - 1
      · subst hi_eq
        have hs1 : (m - 1) < m := by omega
        have hadd : m - 1 + 1 = m := by omega
        have hs2 : (m - 1 + 1) % (m + 2) = m := by rw [hadd, Nat.mod_eq_of_lt (by omega)]
        simp [hi1_not, hs1, hs2, getZero_replicate_zero, getZero]
      · by_cases hi_m : i = m
        · subst hi_m
          simp [hi1_not, getZero]
        · have hi_m1 : i = m + 1 := by omega
          subst hi_m1
          have hmod : (m + 1 + 1) % (m + 2) = 0 := by
            have : m + 1 + 1 = m + 2 := by omega
            rw [this, Nat.mod_self]
          simp [hi1_not, hmod, getZero_replicate_zero, getZero]
  have hcount : ∀ r, r ≤ m + 2 →
      (List.range r).countP p = (List.range r).countP (fun i => decide (i < m - 1)) := by
    intro r hr
    apply List.countP_congr
    intro i hi
    rw [List.mem_range] at hi
    simp [hp_val i (by omega)]
  change (List.range (m + 2)).countP p = m - 1
  rw [hcount (m + 2) (Nat.le_refl _)]
  have hlt_count : ∀ r, (List.range r).countP (fun i => decide (i < m - 1)) = min r (m - 1) := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [List.range_succ, List.countP_append, ih, List.countP_cons, List.countP_nil]
      by_cases hr : r < m - 1 <;> simp [hr] <;> omega
  rw [hlt_count (m + 2)]
  omega

theorem cyclicAdjZeros_templateB (m : Nat) (hm : m ≥ 1) :
    cyclicAdjZeros (List.replicate m (0 : Fin 3) ++ [1, 0, 2]) = m - 1 := by
  let u := List.replicate m (0 : Fin 3) ++ [1, 0, 2]
  have hlen : u.length = m + 3 := by simp [u, List.length_append, List.length_replicate]
  unfold cyclicAdjZeros
  rw [hlen]
  let p : Nat → Bool := fun i => decide (getZero u i = 0 ∧ getZero u ((i + 1) % (m + 3)) = 0)
  have hp_val : ∀ i, i < m + 3 → p i = decide (i < m - 1) := by
    intro i hi
    dsimp [p, u]
    rw [getZero_append, getZero_append, List.length_replicate]
    by_cases h1 : i < m - 1
    · have hi1 : i < m := by omega
      have hs1 : (i + 1) % (m + 3) = i + 1 := Nat.mod_eq_of_lt (by omega)
      have hs2 : i + 1 < m := by omega
      simp [h1, hi1, hs1, hs2, getZero_replicate_zero]
    · have hi1_not : ¬ (i < m - 1) := h1
      by_cases hi_eq : i = m - 1
      · subst hi_eq
        have hs1 : (m - 1) < m := by omega
        have hadd : m - 1 + 1 = m := by omega
        have hs2 : (m - 1 + 1) % (m + 3) = m := by rw [hadd, Nat.mod_eq_of_lt (by omega)]
        simp [hi1_not, hs1, hs2, getZero_replicate_zero, getZero]
      · by_cases hi_m : i = m
        · subst hi_m
          simp [hi1_not, getZero]
        · by_cases hi_m1 : i = m + 1
          · subst hi_m1
            have hs2 : (m + 1 + 1) % (m + 3) = m + 2 := Nat.mod_eq_of_lt (by omega)
            have hnot1 : ¬ (m + 1 < m) := by omega
            have hnot2 : ¬ (m + 2 < m) := by omega
            have hsub1 : m + 1 - m = 1 := by omega
            have hsub2 : m + 2 - m = 2 := by omega
            simp [hi1_not, hs2, hnot1, hnot2, hsub1, hsub2, getZero]
          · have hi_m2 : i = m + 2 := by omega
            subst hi_m2
            have hmod : (m + 2 + 1) % (m + 3) = 0 := by
              have : m + 2 + 1 = m + 3 := by omega
              rw [this, Nat.mod_self]
            simp [hi1_not, hmod, getZero_replicate_zero, getZero]
  have hcount : ∀ r, r ≤ m + 3 →
      (List.range r).countP p = (List.range r).countP (fun i => decide (i < m - 1)) := by
    intro r hr
    apply List.countP_congr
    intro i hi
    rw [List.mem_range] at hi
    simp [hp_val i (by omega)]
  change (List.range (m + 3)).countP p = m - 1
  rw [hcount (m + 3) (Nat.le_refl _)]
  have hlt_count : ∀ r, (List.range r).countP (fun i => decide (i < m - 1)) = min r (m - 1) := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [List.range_succ, List.countP_append, ih, List.countP_cons, List.countP_nil]
      by_cases hr : r < m - 1 <;> simp [hr] <;> omega
  rw [hlt_count (m + 3)]
  omega

theorem list_length_eq_five {α : Type} {l : List α} (h : l.length = 5) :
    ∃ a b c d e, l = [a, b, c, d, e] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | _⟩⟩⟩⟩⟩ <;>
    simp at h
  exact ⟨a, b, c, d, e, rfl⟩

/-- Split Classification Lemma for W_n = 0^(2n-5) 1 1 0 2 2. -/
theorem mask_split_W_n (n : Nat) (hn : n ≥ 4) (mask : List Bool)
    (hm_len : mask.length = (W_n n).length)
    (hu_len : (splitTrue mask (W_n n)).length = n)
    (hv_len : (splitFalse mask (W_n n)).length = n)
    (hu1 : (splitTrue mask (W_n n)).count 1 = 1)
    (hu2 : (splitTrue mask (W_n n)).count 2 = 1) :
    (splitTrue mask (W_n n) = List.replicate (n - 3) 0 ++ [1, 0, 2] ∧
     splitFalse mask (W_n n) = List.replicate (n - 2) 0 ++ [1, 2]) ∨
    (splitTrue mask (W_n n) = List.replicate (n - 2) 0 ++ [1, 2] ∧
     splitFalse mask (W_n n) = List.replicate (n - 3) 0 ++ [1, 0, 2]) := by
  have hwlen : (W_n n).length = 2 * n := W_n_length n hn
  rw [hwlen] at hm_len
  let r := 2 * n - 5
  let m1 := mask.take r
  let m2 := mask.drop r
  have hm1_len : m1.length = r := by simp [m1, hm_len, r]
  have hm2_len : m2.length = 5 := by simp [m2, hm_len, r]; omega
  have hm_eq : mask = m1 ++ m2 := (List.take_append_drop r mask).symm
  rcases list_length_eq_five hm2_len with ⟨b1, b2, b3, b4, b5, hb⟩
  have hm_eq2 : mask = m1 ++ [b1, b2, b3, b4, b5] := by rw [hm_eq, hb]
  rw [hm_eq2] at hu_len hv_len hu1 hu2
  unfold W_n at hu_len hv_len hu1 hu2 ⊢
  rw [hm_eq2]
  have hrep_len : m1.length = (List.replicate (2 * n - 5) (0 : Fin 3)).length := by
    rw [List.length_replicate]; exact hm1_len
  rw [splitTrue_append m1 [b1, b2, b3, b4, b5] _ _ hrep_len] at hu_len hu1 hu2 ⊢
  rw [splitFalse_append m1 [b1, b2, b3, b4, b5] _ _ hrep_len] at hv_len ⊢
  rw [splitTrue_replicate_zero m1 (2 * n - 5) hm1_len] at hu_len hu1 hu2 ⊢
  rw [splitFalse_replicate_zero m1 (2 * n - 5) hm1_len] at hv_len ⊢
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    simp [splitTrue, splitFalse, List.count_append, List.count_replicate,
          List.length_append, List.length_replicate] at hu_len hv_len hu1 hu2 ⊢
  all_goals omega

/-- Main Theorem: For every n >= 4, W_n is NOT a dihedral shuffle square. -/
theorem dihedral_conjecture_false (n : Nat) (hn : n ≥ 4) :
    ¬ IsDihedralShuffleSquare n (W_n n) := by
  rintro ⟨mask, hm_len, hu_len, hv_len, γ, hsim⟩
  have hn_pos : n > 0 := by omega
  have hw_even := W_n_even n hn
  have hsum1 := split_count_sum mask (W_n n) 1 hm_len
  have hsum2 := split_count_sum mask (W_n n) 2 hm_len
  have hcnt1_eq : (splitTrue mask (W_n n)).count 1 = (splitFalse mask (W_n n)).count 1 := by
    rcases hsim with h1 | h2
    · rw [h1, γ.count_apply _ hn_pos hu_len 1]
    · rw [h2, γ.count_apply _ hn_pos hv_len 1]
  have hcnt2_eq : (splitTrue mask (W_n n)).count 2 = (splitFalse mask (W_n n)).count 2 := by
    rcases hsim with h1 | h2
    · rw [h1, γ.count_apply _ hn_pos hu_len 2]
    · rw [h2, γ.count_apply _ hn_pos hv_len 2]
  have hu1 : (splitTrue mask (W_n n)).count 1 = 1 := by omega
  have hu2 : (splitTrue mask (W_n n)).count 2 = 1 := by omega
  have hclass := mask_split_W_n n hn mask hm_len hu_len hv_len hu1 hu2
  have hadj_eq : cyclicAdjZeros (splitTrue mask (W_n n)) = cyclicAdjZeros (splitFalse mask (W_n n)) := by
    rcases hsim with h1 | h2
    · rw [h1, cyclicAdjZeros_apply hn_pos _ hu_len γ]
    · rw [h2, cyclicAdjZeros_apply hn_pos _ hv_len γ]
  rcases hclass with ⟨hU, hV⟩ | ⟨hU, hV⟩
  · rw [hU, hV, cyclicAdjZeros_templateB (n - 3) (by omega),
        cyclicAdjZeros_templateA (n - 2) (by omega)] at hadj_eq
    omega
  · rw [hU, hV, cyclicAdjZeros_templateA (n - 2) (by omega),
        cyclicAdjZeros_templateB (n - 3) (by omega)] at hadj_eq
    omega

/-- Minimal counterexample at n = 4 (length 8): W_4 = 00011022. -/
theorem minimal_counterexample_00011022 :
    ¬ IsDihedralShuffleSquare 4 [0, 0, 0, 1, 1, 0, 2, 2] :=
  dihedral_conjecture_false 4 (Nat.le_refl 4)

end DihedralShuffleDisproof

#print axioms DihedralShuffleDisproof.dihedral_conjecture_false
#print axioms DihedralShuffleDisproof.minimal_counterexample_00011022
