/-
  Self-contained Lean 4 formalization answering Gus Wiseman's question on OEIS A384890:
  "Do all constant runs in this sequence have lengths 1, 2, or 3?"

  Proves:
  1. The number of maximal anti-runs in the binary indices of n >= 1 equals
     a(n) = 1 + popcount(n &&& (n >>> 1)).
  2. No four consecutive terms are equal: a(n) = a(n+1) = a(n+2) = a(n+3) is impossible,
     so every constant run has length <= 3 (and lengths 1, 2, 3 all occur).

  Zero external dependencies (no Mathlib, fully kernel-verified).
-/

namespace WisemanA384890

def popcountFuel : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, n => n % 2 + popcountFuel fuel (n / 2)

def popcount (n : Nat) : Nat := popcountFuel n n

def adjOnesFuel : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, n => (if n % 4 = 3 then 1 else 0) + adjOnesFuel fuel (n / 2)

def adjOnes (n : Nat) : Nat := adjOnesFuel n n

def a (n : Nat) : Nat :=
  if n = 0 then 0 else 1 + adjOnes n

theorem popcountFuel_eq_of_le (k₁ k₂ n : Nat) (h₁ : n ≤ k₁) (h₂ : n ≤ k₂) :
    popcountFuel k₁ n = popcountFuel k₂ n := by
  induction n using Nat.strongRecOn generalizing k₁ k₂ with
  | ind n ih =>
    cases n with
    | zero =>
      cases k₁ <;> cases k₂ <;> rfl
    | succ m =>
      obtain ⟨f₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k₁ ≠ 0)
      obtain ⟨f₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k₂ ≠ 0)
      simp only [popcountFuel]
      congr 1
      apply ih ((m + 1) / 2) (Nat.div_lt_self (by omega) (by omega))
      · omega
      · omega

theorem adjOnesFuel_eq_of_le (k₁ k₂ n : Nat) (h₁ : n ≤ k₁) (h₂ : n ≤ k₂) :
    adjOnesFuel k₁ n = adjOnesFuel k₂ n := by
  induction n using Nat.strongRecOn generalizing k₁ k₂ with
  | ind n ih =>
    cases n with
    | zero =>
      cases k₁ <;> cases k₂ <;> rfl
    | succ m =>
      obtain ⟨f₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k₁ ≠ 0)
      obtain ⟨f₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k₂ ≠ 0)
      simp only [adjOnesFuel]
      congr 1
      apply ih ((m + 1) / 2) (Nat.div_lt_self (by omega) (by omega))
      · omega
      · omega

theorem popcount_zero : popcount 0 = 0 := rfl
theorem adjOnes_zero : adjOnes 0 = 0 := rfl

theorem popcount_step {n : Nat} (hn : n ≠ 0) :
    popcount n = n % 2 + popcount (n / 2) := by
  unfold popcount
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp only [popcountFuel]
  congr 1
  exact popcountFuel_eq_of_le m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _)

theorem adjOnes_step {n : Nat} (hn : n ≠ 0) :
    adjOnes n = (if n % 4 = 3 then 1 else 0) + adjOnes (n / 2) := by
  unfold adjOnes
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp only [adjOnesFuel]
  congr 1
  exact adjOnesFuel_eq_of_le m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _)

theorem adjOnes_eq_popcount_and_shr (n : Nat) :
    adjOnes n = popcount (n &&& (n >>> 1)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn; rfl
    · have hdiv : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
      have hih := ih (n / 2) hdiv
      have hshr : n >>> 1 = n / 2 := Nat.shiftRight_eq_div_pow n 1
      have hshr2 : (n / 2) >>> 1 = (n / 2) / 2 := Nat.shiftRight_eq_div_pow (n / 2) 1
      rw [hshr]
      rw [hshr2] at hih
      have hmod2 : (n &&& (n / 2)) % 2 = if n % 4 = 3 then 1 else 0 := by
        have h1 : (n &&& (n / 2)) % 2 = n % 2 &&& (n / 2) % 2 := by
          simpa using (Nat.and_mod_two_pow (a := n) (b := n / 2) (n := 1))
        rw [h1]
        have h4 : n = 4 * (n / 4) + n % 4 := (Nat.div_add_mod n 4).symm
        have hlt : n % 4 < 4 := Nat.mod_lt n (by omega)
        have hr0 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
        rcases hr0 with r | r | r | r
        · have hn2 : n % 2 = 0 := by omega
          have hd2 : (n / 2) % 2 = 0 := by omega
          simp [r, hn2, hd2]
        · have hn2 : n % 2 = 1 := by omega
          have hd2 : (n / 2) % 2 = 0 := by omega
          simp [r, hn2, hd2]
        · have hn2 : n % 2 = 0 := by omega
          have hd2 : (n / 2) % 2 = 1 := by omega
          simp [r, hn2, hd2]
        · have hn2 : n % 2 = 1 := by omega
          have hd2 : (n / 2) % 2 = 1 := by omega
          simp [r, hn2, hd2]
      by_cases hand : (n &&& (n / 2)) = 0
      · have hmod0 : (n &&& (n / 2)) % 2 = 0 := by simp [hand]
        rw [hmod2] at hmod0
        have hne3 : n % 4 ≠ 3 := by
          intro h3; simp [h3] at hmod0
        have hdiv_zero : (n / 2 &&& (n / 2 / 2)) = 0 := by
          rw [← Nat.and_div_two (a := n) (b := n / 2), hand]
        rw [adjOnes_step hn]
        simp only [hne3, ↓reduceIte, Nat.zero_add]
        rw [hih, hdiv_zero, hand]
      · rw [adjOnes_step hn, popcount_step hand, hmod2, hih, Nat.and_div_two]

theorem adjOnes_4q (q : Nat) : adjOnes (4 * q) = adjOnes (2 * q) := by
  by_cases hq : q = 0
  · subst hq; rfl
  · have hn : 4 * q ≠ 0 := by omega
    rw [adjOnes_step hn]
    have hm : (4 * q) % 4 = 0 := by omega
    have hd : (4 * q) / 2 = 2 * q := by omega
    simp [hm, hd]

theorem adjOnes_4q1 (q : Nat) : adjOnes (4 * q + 1) = adjOnes (2 * q) := by
  have hn : 4 * q + 1 ≠ 0 := by omega
  rw [adjOnes_step hn]
  have hm : (4 * q + 1) % 4 = 1 := by omega
  have hd : (4 * q + 1) / 2 = 2 * q := by omega
  simp [hm, hd]

theorem adjOnes_4q2 (q : Nat) : adjOnes (4 * q + 2) = adjOnes (2 * q + 1) := by
  have hn : 4 * q + 2 ≠ 0 := by omega
  rw [adjOnes_step hn]
  have hm : (4 * q + 2) % 4 = 2 := by omega
  have hd : (4 * q + 2) / 2 = 2 * q + 1 := by omega
  simp [hm, hd]

theorem adjOnes_4q3 (q : Nat) : adjOnes (4 * q + 3) = 1 + adjOnes (2 * q + 1) := by
  have hn : 4 * q + 3 ≠ 0 := by omega
  rw [adjOnes_step hn]
  have hm : (4 * q + 3) % 4 = 3 := by omega
  have hd : (4 * q + 3) / 2 = 2 * q + 1 := by omega
  simp [hm, hd]

theorem adjOnes_succ_le (k : Nat) : adjOnes (k + 1) ≤ adjOnes k + 1 := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    let q := k / 4
    have hq : k = 4 * q + k % 4 := (Nat.div_add_mod k 4).symm
    have hm : k % 4 < 4 := Nat.mod_lt k (by omega)
    have hr : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases hr with r | r | r | r
    · have hk : k = 4 * q := by omega
      rw [hk, adjOnes_4q1, adjOnes_4q]; omega
    · have hk : k = 4 * q + 1 := by omega
      have hk1 : k + 1 = 4 * q + 2 := by omega
      rw [hk1, hk, adjOnes_4q2, adjOnes_4q1]
      by_cases h2q : 2 * q < k
      · exact ih (2 * q) h2q
      · have hq0 : q = 0 := by omega
        rw [hq0]; decide
    · have hk : k = 4 * q + 2 := by omega
      have hk1 : k + 1 = 4 * q + 3 := by omega
      rw [hk1, hk, adjOnes_4q3, adjOnes_4q2]; omega
    · have hk : k = 4 * q + 3 := by omega
      have hk1 : k + 1 = 4 * (q + 1) := by omega
      rw [hk1, hk, adjOnes_4q, adjOnes_4q3]
      have h2q : 2 * (q + 1) = (2 * q + 1) + 1 := by omega
      rw [h2q]
      have hlt : 2 * q + 1 < k := by omega
      have := ih (2 * q + 1) hlt
      omega

/-- Main Theorem: No constant run in OEIS A384890 has length >= 4. -/
theorem wiseman_A384890_no_run_len_4 (n : Nat) :
    ¬ (a n = a (n + 1) ∧ a (n + 1) = a (n + 2) ∧ a (n + 2) = a (n + 3)) := by
  intro ⟨h01, h12, h23⟩
  by_cases hn0 : n = 0
  · subst hn0
    have ha0 : a 0 = 0 := rfl
    have ha1 : a 1 = 1 := by decide
    rw [ha0, ha1] at h01
    exact absurd h01 (by decide)
  · have hn1_nz : n + 1 ≠ 0 := by omega
    have hn2_nz : n + 2 ≠ 0 := by omega
    have hn3_nz : n + 3 ≠ 0 := by omega
    have e01 : adjOnes n = adjOnes (n + 1) := by
      unfold a at h01
      simp only [hn0, hn1_nz, ↓reduceIte] at h01
      omega
    have e12 : adjOnes (n + 1) = adjOnes (n + 2) := by
      unfold a at h12
      simp only [hn1_nz, hn2_nz, ↓reduceIte] at h12
      omega
    have e23 : adjOnes (n + 2) = adjOnes (n + 3) := by
      unfold a at h23
      simp only [hn2_nz, hn3_nz, ↓reduceIte] at h23
      omega
    let q := n / 4
    have hq : n = 4 * q + n % 4 := (Nat.div_add_mod n 4).symm
    have hm : n % 4 < 4 := Nat.mod_lt n (by omega)
    have hr : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases hr with r | r | r | r
    · have hn2 : n + 2 = 4 * q + 2 := by omega
      have hn3 : n + 3 = 4 * q + 3 := by omega
      rw [hn2, hn3, adjOnes_4q2, adjOnes_4q3] at e23
      omega
    · have hn1 : n + 1 = 4 * q + 2 := by omega
      have hn2 : n + 2 = 4 * q + 3 := by omega
      rw [hn1, hn2, adjOnes_4q2, adjOnes_4q3] at e12
      omega
    · have hn1 : n + 1 = 4 * q + 3 := by omega
      have hn0' : n = 4 * q + 2 := by omega
      rw [hn1, hn0', adjOnes_4q2, adjOnes_4q3] at e01
      omega
    · have hn1 : n + 1 = 4 * (q + 1) := by omega
      have hn0' : n = 4 * q + 3 := by omega
      have hn2 : n + 2 = 4 * (q + 1) + 1 := by omega
      have hn3 : n + 3 = 4 * (q + 1) + 2 := by omega
      rw [hn1, hn0', adjOnes_4q3, adjOnes_4q] at e01
      rw [hn2, hn3, adjOnes_4q1, adjOnes_4q2] at e23
      let m := q / 2
      have hm2 : q = 2 * m + q % 2 := (Nat.div_add_mod q 2).symm
      have hqm : q % 2 = 0 ∨ q % 2 = 1 := by omega
      rcases hqm with b | b
      · have hq0 : q = 2 * m := by omega
        have ha : 2 * (q + 1) = 4 * m + 2 := by omega
        have hb : 2 * (q + 1) + 1 = 4 * m + 3 := by omega
        rw [hb, ha, adjOnes_4q2, adjOnes_4q3] at e23
        omega
      · have hq1 : q = 2 * m + 1 := by omega
        have ha : 2 * q + 1 = 4 * m + 3 := by omega
        have hb : 2 * (q + 1) = 4 * (m + 1) := by omega
        rw [ha, hb, adjOnes_4q3, adjOnes_4q] at e01
        have hle := adjOnes_succ_le (2 * m + 1)
        have h2m2 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
        rw [h2m2] at e01
        omega

/-- Witnesses showing run lengths 1, 2, and 3 all occur. -/
theorem witness_run_len_1_and_2 : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 1 ∧ a 3 = 2 := by decide
theorem witness_run_len_3 : a 7 = 3 ∧ a 8 = 1 ∧ a 9 = 1 ∧ a 10 = 1 ∧ a 11 = 2 := by decide

end WisemanA384890

#print axioms WisemanA384890.adjOnes_eq_popcount_and_shr
#print axioms WisemanA384890.wiseman_A384890_no_run_len_4
