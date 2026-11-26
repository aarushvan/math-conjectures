/-
  Complete Lean 4 formalization of Gus Wiseman's 2025 conjectures on
  OEIS A382427 and OEIS A381717:
  A partition of positive integers can be partitioned into constant blocks
  with pairwise distinct block-sums if and only if it admits a permutation
  whose maximal constant runs have pairwise distinct run-sums.

  Zero external dependencies (no Mathlib, fully kernel-verified).
-/

namespace WisemanA382427

structure Block where
  val   : Nat
  count : Nat
  h_val : val > 0
  h_cnt : count > 0
  deriving DecidableEq

def Block.sum (b : Block) : Nat := b.val * b.count

def Block.expand (b : Block) : List Nat := List.replicate b.count b.val

def DistinctSums (bs : List Block) : Prop :=
  (bs.map Block.sum).Nodup

def NoAdjSameVal : List Block → Prop
  | [] => True
  | [_] => True
  | b₁ :: b₂ :: rest => b₁.val ≠ b₂.val ∧ NoAdjSameVal (b₂ :: rest)

def mergeBlocks (b₁ b₂ : Block) (_h : b₁.val = b₂.val) : Block :=
  { val := b₁.val
    count := b₁.count + b₂.count
    h_val := b₁.h_val
    h_cnt := Nat.add_pos_left b₁.h_cnt b₂.count }

theorem Block.sum_pos (b : Block) : b.sum > 0 :=
  Nat.mul_pos b.h_val b.h_cnt

theorem mergeBlocks_sum (b₁ b₂ : Block) (h : b₁.val = b₂.val) :
    (mergeBlocks b₁ b₂ h).sum = b₁.sum + b₂.sum := by
  simp only [mergeBlocks, Block.sum]
  rw [Nat.mul_add, h]

theorem replicate_add_eq {α : Type} (m n : Nat) (a : α) :
    List.replicate (m + n) a = List.replicate m a ++ List.replicate n a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, ih, List.cons_append]

theorem mergeBlocks_expand (b₁ b₂ : Block) (h : b₁.val = b₂.val) :
    (mergeBlocks b₁ b₂ h).expand = b₁.expand ++ b₂.expand := by
  simp only [mergeBlocks, Block.expand]
  rw [h, replicate_add_eq]

theorem perm_flatMap {α β : Type} {f : α → List β} {l₁ l₂ : List α} (hp : l₁.Perm l₂) :
    (l₁.flatMap f).Perm (l₂.flatMap f) := by
  induction hp with
  | nil => exact List.Perm.nil
  | cons x _ ih =>
    simp only [List.flatMap_cons]
    exact ih.append_left (f x)
  | swap x y l =>
    simp only [List.flatMap_cons]
    have hassoc1 : f y ++ (f x ++ l.flatMap f) = (f y ++ f x) ++ l.flatMap f := by simp [List.append_assoc]
    have hassoc2 : f x ++ (f y ++ l.flatMap f) = (f x ++ f y) ++ l.flatMap f := by simp [List.append_assoc]
    rw [hassoc1, hassoc2]
    exact List.Perm.append_right (l.flatMap f) List.perm_append_comm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

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

theorem filter_perm_partition {α : Type} (p : α → Bool) (l : List α) :
    l.Perm (l.filter p ++ l.filter (fun x => !(p x))) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hpx : p x
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      exact (List.Perm.cons x ih).trans List.perm_middle.symm
    · simp only [↓reduceIte, Bool.not_true, List.cons_append]
      exact List.Perm.cons x ih

/-- Maximal constant runs of a list of natural numbers, represented as (val, count). -/
def maxRunsAux (curVal curCnt : Nat) : List Nat → List (Nat × Nat)
  | [] => [(curVal, curCnt)]
  | x :: xs =>
    if x == curVal then maxRunsAux curVal (curCnt + 1) xs
    else (curVal, curCnt) :: maxRunsAux x 1 xs

def maxRuns : List Nat → List (Nat × Nat)
  | [] => []
  | x :: xs => maxRunsAux x 1 xs

theorem maxRunsAux_replicate_append (v : Nat) (c : Nat) (curVal curCnt : Nat)
    (hc : c > 0) (hne : v ≠ curVal) (rest : List Nat) :
    maxRunsAux curVal curCnt (List.replicate c v ++ rest) =
      (curVal, curCnt) :: maxRunsAux v c rest := by
  cases c with
  | zero => omega
  | succ c =>
    clear hc
    rw [List.replicate_succ, List.cons_append]
    simp only [maxRunsAux, beq_iff_eq, hne, ↓reduceIte]
    congr 1
    clear curVal curCnt hne
    suffices hgen : ∀ k, maxRunsAux v k (List.replicate c v ++ rest) = maxRunsAux v (k + c) rest by
      have h1 := hgen 1
      have hadd : 1 + c = c + 1 := by omega
      rw [hadd] at h1
      exact h1
    intro k
    induction c generalizing k with
    | zero => simp
    | succ c ih =>
      rw [List.replicate_succ, List.cons_append]
      simp only [maxRunsAux, beq_self_eq_true, ↓reduceIte]
      rw [ih (k + 1)]
      congr 1; omega

theorem maxRunsAux_expand (b : Block) (bs : List Block) (hno : NoAdjSameVal (b :: bs)) :
    maxRunsAux b.val b.count (bs.flatMap Block.expand) =
      (b.val, b.count) :: bs.map (fun x => (x.val, x.count)) := by
  induction bs generalizing b with
  | nil => rfl
  | cons b₂ bs ih =>
    rcases hno with ⟨hne, hrest⟩
    rw [List.flatMap_cons, Block.expand]
    rw [maxRunsAux_replicate_append b₂.val b₂.count b.val b.count b₂.h_cnt hne.symm]
    rw [ih b₂ hrest]
    rfl

theorem maxRuns_expand (bs : List Block) (hno : NoAdjSameVal bs) :
    maxRuns (bs.flatMap Block.expand) = bs.map (fun b => (b.val, b.count)) := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    rw [List.flatMap_cons]
    have hc : b.count > 0 := b.h_cnt
    obtain ⟨c, hceq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hc)
    clear hc
    simp only [Block.expand]
    rw [hceq, List.replicate_succ, List.cons_append]
    simp only [maxRuns]
    have hgen : ∀ k,
        maxRunsAux b.val k (List.replicate c b.val ++ bs.flatMap Block.expand) =
        maxRunsAux b.val (k + c) (bs.flatMap Block.expand) := by
      intro k
      clear hceq
      induction c generalizing k with
      | zero => simp
      | succ c ihc =>
        rw [List.replicate_succ, List.cons_append]
        simp only [maxRunsAux, beq_self_eq_true, ↓reduceIte]
        rw [ihc (k + 1)]
        congr 1; omega
    have hc1 : b.count = 1 + c := by omega
    rw [hgen 1, ← hc1]
    exact maxRunsAux_expand b bs hno

/-- Converting any list of positive numbers back into constant blocks matching its maximal runs. -/
def toBlocksAux (curVal curCnt : Nat) (hv : curVal > 0) (hc : curCnt > 0)
    (xs : List Nat) (hxs : ∀ x ∈ xs, x > 0) : List Block :=
  match xs with
  | [] => [⟨curVal, curCnt, hv, hc⟩]
  | x :: rest =>
    if _hx : x = curVal then
      toBlocksAux curVal (curCnt + 1) hv (Nat.add_pos_left hc 1) rest
        (fun y hy => hxs y (List.mem_cons_of_mem x hy))
    else
      ⟨curVal, curCnt, hv, hc⟩ ::
        toBlocksAux x 1 (hxs x List.mem_cons_self) (Nat.zero_lt_succ 0) rest
          (fun y hy => hxs y (List.mem_cons_of_mem x hy))

theorem toBlocksAux_expand (curVal curCnt : Nat) (hv : curVal > 0) (hc : curCnt > 0)
    (xs : List Nat) (hxs : ∀ x ∈ xs, x > 0) :
    (toBlocksAux curVal curCnt hv hc xs hxs).flatMap Block.expand =
      List.replicate curCnt curVal ++ xs := by
  induction xs generalizing curVal curCnt hv hc with
  | nil => simp [toBlocksAux, Block.expand]
  | cons x rest ih =>
    dsimp only [toBlocksAux]
    split
    · next hx =>
      rw [ih curVal (curCnt + 1) hv (Nat.add_pos_left hc 1) _]
      rw [List.replicate_succ', List.append_assoc]
      simp [hx]
    · next _ =>
      rw [List.flatMap_cons, ih x 1 _ _]
      simp [Block.expand, List.replicate_succ]

theorem toBlocksAux_sums (curVal curCnt : Nat) (hv : curVal > 0) (hc : curCnt > 0)
    (xs : List Nat) (hxs : ∀ x ∈ xs, x > 0) :
    (toBlocksAux curVal curCnt hv hc xs hxs).map Block.sum =
      (maxRunsAux curVal curCnt xs).map (fun r => r.1 * r.2) := by
  induction xs generalizing curVal curCnt hv hc with
  | nil => simp [toBlocksAux, maxRunsAux, Block.sum]
  | cons x rest ih =>
    dsimp only [toBlocksAux, maxRunsAux]
    split
    · next hx =>
      simp only [hx, beq_self_eq_true, ↓reduceIte]
      exact ih curVal (curCnt + 1) hv (Nat.add_pos_left hc 1) _
    · next hne =>
      have hbeq : (x == curVal) = false := beq_false_of_ne hne
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.map_cons, Block.sum]
      congr 1
      exact ih x 1 _ _ _

/-- Pigeonhole Principle for Nodup lists: if ys.length < xs.length and xs.Nodup, some x in xs is not in ys. -/
theorem exists_not_mem_of_nodup_lt {α : Type} [DecidableEq α] (xs ys : List α)
    (hnd : xs.Nodup) (hlt : ys.length < xs.length) :
    ∃ x ∈ xs, x ∉ ys := by
  induction xs generalizing ys with
  | nil => simp only [List.length_nil] at hlt; omega
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    by_cases hmem : x ∈ ys
    · have hys_pos : ys.length ≥ 1 := List.length_pos_of_mem hmem
      have hlt2 : (ys.erase x).length < xs.length := by
        rw [List.length_erase_of_mem hmem]
        simp only [List.length_cons] at hlt
        omega
      rcases ih (ys.erase x) hnd.2 hlt2 with ⟨z, hz_mem, hz_not⟩
      refine ⟨z, List.mem_cons_of_mem x hz_mem, ?_⟩
      intro hz_ys
      have hne : z ≠ x := by
        rintro rfl
        exact hnd.1 hz_mem
      exact hz_not ((List.mem_erase_of_ne hne).mpr hz_ys)
    · exact ⟨x, List.mem_cons_self, hmem⟩

/-- Maximum-sum block in a nonempty list. -/
def maxSumBlock : (l : List Block) → l ≠ [] → Block
  | [b], _ => b
  | b₁ :: b₂ :: rest, _ =>
    let tailMax := maxSumBlock (b₂ :: rest) (List.cons_ne_nil b₂ rest)
    if b₁.sum ≥ tailMax.sum then b₁ else tailMax

theorem maxSumBlock_mem (l : List Block) (hl : l ≠ []) : maxSumBlock l hl ∈ l := by
  match l with
  | [] => exact absurd rfl hl
  | [b] => simp [maxSumBlock]
  | b₁ :: b₂ :: rest =>
    dsimp only [maxSumBlock]
    split
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem b₁ (maxSumBlock_mem (b₂ :: rest) _)

theorem maxSumBlock_ge (l : List Block) (hl : l ≠ []) :
    ∀ b ∈ l, b.sum ≤ (maxSumBlock l hl).sum := by
  match l with
  | [] => exact absurd rfl hl
  | [b₀] =>
    intro b hb
    simp at hb; subst hb; simp [maxSumBlock]
  | b₁ :: b₂ :: rest =>
    intro b hb
    dsimp only [maxSumBlock]
    have ih := maxSumBlock_ge (b₂ :: rest) (List.cons_ne_nil b₂ rest)
    split
    · next hge =>
      rcases List.mem_cons.mp hb with rfl | hmem
      · exact Nat.le_refl _
      · exact Nat.le_trans (ih b hmem) hge
    · next hlt =>
      rcases List.mem_cons.mp hb with rfl | hmem
      · omega
      · exact ih b hmem

theorem distinctSums_erase {bs : List Block} (hnd : DistinctSums bs) (b : Block) :
    DistinctSums (bs.erase b) := by
  by_cases hmem : b ∈ bs
  · have hp : bs.Perm (b :: bs.erase b) := List.perm_cons_erase hmem
    have hmap := (hp.map Block.sum).nodup_iff.mp hnd
    exact (List.nodup_cons.mp hmap).2
  · rw [List.erase_of_not_mem hmem]
    exact hnd

theorem mem_erase_of_mem_ne {α : Type} [DecidableEq α] {a b : α} {l : List α}
    (ha : a ∈ l) (hne : a ≠ b) : a ∈ l.erase b :=
  (List.mem_erase_of_ne hne).mpr ha

theorem sum_mem_erase_lt {bs : List Block} (hnd : DistinctSums bs) {bMax b : Block}
    (hbMax : bMax ∈ bs) (hle : b.sum ≤ bMax.sum) (hb : b ∈ bs.erase bMax) :
    b.sum < bMax.sum := by
  by_cases heq : b.sum = bMax.sum
  · have hp := (List.perm_cons_erase hbMax).map Block.sum
    have hnd2 := hp.nodup_iff.mp hnd
    have hnot : bMax.sum ∉ (bs.erase bMax).map Block.sum := (List.nodup_cons.mp hnd2).1
    have hmem : b.sum ∈ (bs.erase bMax).map Block.sum := List.mem_map.mpr ⟨b, hb, rfl⟩
    rw [heq] at hmem
    exact absurd hmem hnot
  · omega

theorem length_eq_countP_add_not (v : Nat) (bs : List Block) :
    bs.countP (fun b => b.val == v) + bs.countP (fun b => !(b.val == v)) = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.countP_cons, List.length_cons]
    cases (b.val == v) <;> simp <;> omega

/-- Strong-induction Pigeonhole Merge reduction. -/
theorem pigeonhole_reduce (n : Nat) :
    ∀ bs : List Block, bs.length = n → DistinctSums bs →
      ∃ bs' : List Block,
        (bs'.flatMap Block.expand).Perm (bs.flatMap Block.expand) ∧
        DistinctSums bs' ∧
        (∀ v, 2 * (bs'.countP (fun b => b.val == v)) ≤ bs'.length + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro bs hlen hds
    by_cases hgood : ∀ v, 2 * (bs.countP (fun b => b.val == v)) ≤ bs.length + 1
    · exact ⟨bs, List.Perm.refl _, hds, hgood⟩
    · have hex : ∃ v, ¬ (2 * (bs.countP (fun b => b.val == v)) ≤ bs.length + 1) := by
        apply Classical.byContradiction
        intro hno
        apply hgood
        intro v
        apply Classical.byContradiction
        intro hnv
        exact hno ⟨v, hnv⟩
      rcases hex with ⟨v, hv_bad⟩
      let same := bs.filter (fun b => b.val == v)
      let diff := bs.filter (fun b => !(b.val == v))
      have hsame_len : same.length = bs.countP (fun b => b.val == v) := by
        simp [same, List.countP_eq_length_filter]
      have hdiff_len : diff.length = bs.countP (fun b => !(b.val == v)) := by
        simp [diff, List.countP_eq_length_filter]
      have hsplit_len := length_eq_countP_add_not v bs
      have h_ineq : same.length ≥ diff.length + 2 := by omega
      have hsame_ne : same ≠ [] := by
        intro hnil; rw [hnil] at h_ineq; simp at h_ineq
      let bMax := maxSumBlock same hsame_ne
      have hbMax_same : bMax ∈ same := maxSumBlock_mem same hsame_ne
      have hbMax_bs : bMax ∈ bs := (List.mem_filter.mp hbMax_same).1
      have hbMax_val : bMax.val = v := beq_iff_eq.mp (List.mem_filter.mp hbMax_same).2
      let restSame := same.erase bMax
      have hrest_len : restSame.length = same.length - 1 := List.length_erase_of_mem hbMax_same
      have hcand_gt : diff.length < restSame.length := by omega
      have hsame_perm_bs : bs.Perm (same ++ diff) := filter_perm_partition (fun b => b.val == v) bs
      have hsame_diff_ds : DistinctSums (same ++ diff) :=
        (hsame_perm_bs.map Block.sum).nodup_iff.mp hds
      have hsame_ds : DistinctSums same := by
        rw [DistinctSums, List.map_append] at hsame_diff_ds
        exact (List.nodup_append.mp hsame_diff_ds).1
      have hrest_ds : DistinctSums restSame := distinctSums_erase hsame_ds bMax
      have hcand_nodup : (restSame.map (fun b => bMax.sum + b.sum)).Nodup := by
        have hm1 : restSame.map (fun b => bMax.sum + b.sum) =
            (restSame.map Block.sum).map (fun s => bMax.sum + s) := by
          rw [List.map_map]; rfl
        rw [hm1]
        apply nodup_map_of_inj_on _ _ hrest_ds
        intro x _ y _ hxy; omega
      have hlt_cand : (diff.map Block.sum).length <
          (restSame.map (fun b => bMax.sum + b.sum)).length := by
        simpa [List.length_map] using hcand_gt
      rcases exists_not_mem_of_nodup_lt _ (diff.map Block.sum) hcand_nodup hlt_cand with
        ⟨s, hs_cand, hs_not_diff⟩
      rcases List.mem_map.mp hs_cand with ⟨b₂, hb₂_rest, rfl⟩
      have hb₂_same : b₂ ∈ same := List.mem_of_mem_erase hb₂_rest
      have hb₂_bs : b₂ ∈ bs := (List.mem_filter.mp hb₂_same).1
      have hb₂_val : b₂.val = v := beq_iff_eq.mp (List.mem_filter.mp hb₂_same).2
      have hne_b₂_bMax : b₂ ≠ bMax := by
        intro heq
        subst heq
        have hbMax_sum_lt := sum_mem_erase_lt hsame_ds hbMax_same (Nat.le_refl _) hb₂_rest
        omega
      have hb₂_in_erase : b₂ ∈ bs.erase bMax := mem_erase_of_mem_ne hb₂_bs hne_b₂_bMax
      let merged := mergeBlocks bMax b₂ (by rw [hbMax_val, hb₂_val])
      let bsNext := merged :: (bs.erase bMax).erase b₂
      have hperm_bs : bs.Perm (bMax :: b₂ :: (bs.erase bMax).erase b₂) :=
        (List.perm_cons_erase hbMax_bs).trans
          (List.Perm.cons bMax (List.perm_cons_erase hb₂_in_erase))
      have hlen_next : bsNext.length = n - 1 := by
        have hl := hperm_bs.length_eq
        simp only [bsNext, List.length_cons] at hl ⊢
        omega
      have hlt_n : bsNext.length < n := by omega
      have hds_erase2 : DistinctSums ((bs.erase bMax).erase b₂) :=
        distinctSums_erase (distinctSums_erase hds bMax) b₂
      have hmerged_not_in : merged.sum ∉ ((bs.erase bMax).erase b₂).map Block.sum := by
        intro hmem
        rcases List.mem_map.mp hmem with ⟨x, hx_mem, hx_sum⟩
        have hx_erase1 : x ∈ bs.erase bMax := List.mem_of_mem_erase hx_mem
        have hx_bs : x ∈ bs := List.mem_of_mem_erase hx_erase1
        rw [mergeBlocks_sum] at hx_sum
        by_cases hxv : x.val = v
        · have hx_same : x ∈ same := List.mem_filter.mpr ⟨hx_bs, beq_iff_eq.mpr hxv⟩
          have hx_ge : x.sum ≤ bMax.sum := maxSumBlock_ge same hsame_ne x hx_same
          have hpos2 : b₂.sum > 0 := Block.sum_pos b₂
          omega
        · have hx_diff : x ∈ diff :=
            List.mem_filter.mpr ⟨hx_bs, by simp [beq_false_of_ne hxv]⟩
          have hx_in_diff_map : bMax.sum + b₂.sum ∈ diff.map Block.sum :=
            List.mem_map.mpr ⟨x, hx_diff, hx_sum⟩
          exact hs_not_diff hx_in_diff_map
      have hds_next : DistinctSums bsNext := by
        rw [DistinctSums, List.map_cons, List.nodup_cons]
        exact ⟨hmerged_not_in, hds_erase2⟩
      rcases ih bsNext.length hlt_n bsNext rfl hds_next with ⟨bs', hp_exp, hds', hgood'⟩
      refine ⟨bs', hp_exp.trans ?_, hds', hgood'⟩
      have hperm_exp1 : (bsNext.flatMap Block.expand).Perm
          ((bMax :: b₂ :: (bs.erase bMax).erase b₂).flatMap Block.expand) := by
        simp only [bsNext, List.flatMap_cons]
        rw [mergeBlocks_expand, List.append_assoc]
      exact hperm_exp1.trans (perm_flatMap hperm_bs.symm)

def pickMaxScore (score : Block → Nat) : (l : List Block) → l ≠ [] → Block
  | [b], _ => b
  | b₁ :: b₂ :: rest, _ =>
    let m := pickMaxScore score (b₂ :: rest) (List.cons_ne_nil b₂ rest)
    if score b₁ ≥ score m then b₁ else m

theorem pickMaxScore_mem (score : Block → Nat) (l : List Block) (hl : l ≠ []) :
    pickMaxScore score l hl ∈ l := by
  match l with
  | [] => exact absurd rfl hl
  | [b] => simp [pickMaxScore]
  | b₁ :: b₂ :: rest =>
    dsimp only [pickMaxScore]
    split
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem b₁ (pickMaxScore_mem score (b₂ :: rest) _)

theorem pickMaxScore_ge (score : Block → Nat) (l : List Block) (hl : l ≠ []) :
    ∀ x ∈ l, score x ≤ score (pickMaxScore score l hl) := by
  match l with
  | [] => exact absurd rfl hl
  | [b] =>
    intro x hx; simp at hx; subst hx; simp [pickMaxScore]
  | b₁ :: b₂ :: rest =>
    intro x hx
    dsimp only [pickMaxScore]
    have ih := pickMaxScore_ge score (b₂ :: rest) (List.cons_ne_nil b₂ rest)
    split
    · next hge =>
      rcases List.mem_cons.mp hx with rfl | hxm
      · exact Nat.le_refl _
      · exact Nat.le_trans (ih x hxm) hge
    · next hlt =>
      rcases List.mem_cons.mp hx with rfl | hxm
      · omega
      · exact ih x hxm

/-- Pick an element of bs maximizing countVal b.val bs among those with some b.val != prev. -/
theorem exists_max_valid_block (bs : List Block) (prev : Option Nat)
    (hne : ∃ b ∈ bs, (some b.val ≠ prev)) :
    ∃ b ∈ bs, some b.val ≠ prev ∧
      ∀ x ∈ bs, some x.val ≠ prev →
        bs.countP (fun z => z.val == x.val) ≤ bs.countP (fun z => z.val == b.val) := by
  let cands := bs.filter (fun b => decide (some b.val ≠ prev))
  have hc_ne : cands ≠ [] := by
    rcases hne with ⟨b, hb, hbp⟩
    intro heq
    have hmem : b ∈ cands := List.mem_filter.mpr ⟨hb, decide_eq_true hbp⟩
    rw [heq] at hmem
    simp at hmem
  let score : Block → Nat := fun b => bs.countP (fun z => z.val == b.val)
  let bStar := pickMaxScore score cands hc_ne
  have hb_cands : bStar ∈ cands := pickMaxScore_mem score cands hc_ne
  have hb_mem_pair := List.mem_filter.mp hb_cands
  refine ⟨bStar, hb_mem_pair.1, of_decide_eq_true hb_mem_pair.2, ?_⟩
  intro x hx hxp
  exact pickMaxScore_ge score cands hc_ne x (List.mem_filter.mpr ⟨hx, decide_eq_true hxp⟩)

theorem countP_ge_one_of_mem {α : Type} (p : α → Bool) {b : α} {l : List α}
    (hb : b ∈ l) (hp : p b = true) : l.countP p ≥ 1 := by
  induction l with
  | nil => simp at hb
  | cons x xs ih =>
    simp only [List.countP_cons]
    rcases List.mem_cons.mp hb with rfl | hmem
    · simp [hp]
    · have := ih hmem; omega

theorem countP_disjoint_le {α : Type} (p q : α → Bool) (l : List α)
    (hdisj : ∀ x ∈ l, ¬ (p x = true ∧ q x = true)) :
    l.countP p + l.countP q ≤ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons, List.length_cons]
    have hxs := ih (fun y hy => hdisj y (List.mem_cons_of_mem x hy))
    have hx := hdisj x List.mem_cons_self
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

theorem countP_erase_eq {α : Type} [DecidableEq α] (p : α → Bool) (b : α) (bs : List α)
    (hb : b ∈ bs) :
    (bs.erase b).countP p = bs.countP p - if p b then 1 else 0 := by
  have hp := (List.perm_cons_erase hb).countP_eq p
  rw [List.countP_cons] at hp
  cases hpb : p b
  · simp [hpb] at hp ⊢; omega
  · have hpos := countP_ge_one_of_mem p hb hpb
    simp [hpb] at hp ⊢; omega

/-- Forbidden-head alternating interleaving theorem. -/
theorem interleave_blocks (n : Nat) :
    ∀ (bs : List Block) (prev : Option Nat),
      bs.length = n →
      (∀ v, 2 * bs.countP (fun b => b.val == v) ≤ bs.length + 1) →
      (∀ p, prev = some p → 2 * bs.countP (fun b => b.val == p) ≤ bs.length) →
      ∃ bs' : List Block,
        bs'.Perm bs ∧ NoAdjSameVal bs' ∧ (∀ p, prev = some p → bs'.head?.map Block.val ≠ some p) := by
  induction n with
  | zero =>
    intro bs _ hlen _ _
    cases bs with
    | nil => exact ⟨[], List.Perm.nil, trivial, fun p _ => by simp⟩
    | cons _ _ => simp at hlen
  | succ n ih =>
    intro bs prev hlen hcap hprev
    have hex_cand : ∃ b ∈ bs, some b.val ≠ prev := by
      cases prev with
      | none =>
        cases bs with
        | nil => simp at hlen
        | cons b _ => exact ⟨b, List.mem_cons_self, by simp⟩
      | some p =>
        have hp_le : 2 * bs.countP (fun b => b.val == p) ≤ bs.length := hprev p rfl
        have hnot_len : bs.countP (fun b => !(b.val == p)) ≥ 1 := by
          have := length_eq_countP_add_not p bs
          omega
        apply Classical.byContradiction
        intro hnone
        have hzero : bs.countP (fun b => !(b.val == p)) = 0 := by
          rw [List.countP_eq_zero]
          intro b hb
          by_cases hbp : b.val = p
          · simp [hbp]
          · exfalso; apply hnone; exact ⟨b, hb, by simp [hbp]⟩
        omega
    rcases exists_max_valid_block bs prev hex_cand with ⟨b, hb_mem, hb_ne_prev, hb_max⟩
    let bsRem := bs.erase b
    have hrem_len : bsRem.length = n := by
      rw [List.length_erase_of_mem hb_mem, hlen]; omega
    have hrem_cap : ∀ v, 2 * bsRem.countP (fun x => x.val == v) ≤ bsRem.length + 1 := by
      intro v
      rw [hrem_len]
      have hce := countP_erase_eq (fun x => x.val == v) b bs hb_mem
      by_cases hvb : b.val = v
      · have hpos : bs.countP (fun x => x.val == v) ≥ 1 :=
          countP_ge_one_of_mem _ hb_mem (beq_iff_eq.mpr hvb)
        have h1 : bsRem.countP (fun x => x.val == v) = bs.countP (fun x => x.val == v) - 1 := by
          simpa [hvb] using hce
        have hcapv := hcap v
        omega
      · have h0 : bsRem.countP (fun x => x.val == v) = bs.countP (fun x => x.val == v) := by
          have hbeq : (b.val == v) = false := beq_false_of_ne hvb
          simpa [hbeq] using hce
        rw [h0]
        by_cases hvp : some v = prev
        · rw [← hvp] at hprev
          have := hprev v rfl
          omega
        · have hex_v : ∃ x ∈ bs, x.val = v ∨ bs.countP (fun z => z.val == v) = 0 := by
            by_cases hc0 : bs.countP (fun z => z.val == v) = 0
            · exact ⟨b, hb_mem, Or.inr hc0⟩
            · have : ∃ x ∈ bs, (x.val == v) = true := by
                apply Classical.byContradiction
                intro hno
                have hcz : bs.countP (fun z => z.val == v) = 0 := by
                  rw [List.countP_eq_zero]
                  intro x hx
                  cases hxv : (x.val == v)
                  · decide
                  · exfalso; exact hno ⟨x, hx, hxv⟩
                omega
              rcases this with ⟨x, hx, hxv⟩
              exact ⟨x, hx, Or.inl (beq_iff_eq.mp hxv)⟩
          rcases hex_v with ⟨x, hx_mem, hxv | hc0⟩
          · have hle_b := hb_max x hx_mem (by rw [hxv]; exact hvp)
            rw [hxv] at hle_b
            have hdisj : bs.countP (fun z => z.val == v) + bs.countP (fun z => z.val == b.val) ≤ bs.length := by
              apply countP_disjoint_le
              intro z _ ⟨hzv, hzb⟩
              have h1 : z.val = v := beq_iff_eq.mp hzv
              have h2 : z.val = b.val := beq_iff_eq.mp hzb
              exact hvb (h2.symm.trans h1)
            omega
          · omega
    have hrem_prev : ∀ p, some b.val = some p → 2 * bsRem.countP (fun x => x.val == p) ≤ bsRem.length := by
      intro p hp
      injection hp with hbp
      subst hbp
      have hce := countP_erase_eq (fun x => x.val == b.val) b bs hb_mem
      have h1 : bsRem.countP (fun x => x.val == b.val) = bs.countP (fun x => x.val == b.val) - 1 := by
        simpa using hce
      have hcapb := hcap b.val
      rw [hrem_len]
      omega
    rcases ih bsRem (some b.val) hrem_len hrem_cap hrem_prev with ⟨bsRest, hpRest, hnoRest, hheadRest⟩
    refine ⟨b :: bsRest, (List.Perm.cons b hpRest).trans (List.perm_cons_erase hb_mem).symm, ?_, ?_⟩
    · cases bsRest with
      | nil => exact trivial
      | cons b₂ _ =>
        have hne : b.val ≠ b₂.val := by
          intro heq
          apply hheadRest b.val rfl
          simp [heq]
        exact ⟨hne, hnoRest⟩
    · intro p hp
      subst hp
      simpa using hb_ne_prev

/--
  Main Theorem (Wiseman A382427):
  A multiset of positive integers `parts` can be partitioned into constant blocks
  with pairwise distinct sums iff `parts` admits a permutation whose maximal
  constant runs have pairwise distinct sums.
-/
theorem wiseman_A382427_iff (parts : List Nat) (hpos : ∀ x ∈ parts, x > 0) :
    (∃ bs : List Block, (bs.flatMap Block.expand).Perm parts ∧ DistinctSums bs) ↔
    (∃ w : List Nat, w.Perm parts ∧ ((maxRuns w).map (fun r => r.1 * r.2)).Nodup) := by
  constructor
  · rintro ⟨bs, hp_parts, hds⟩
    rcases pigeonhole_reduce bs.length bs rfl hds with ⟨bs1, hp_exp1, hds1, hcap1⟩
    rcases interleave_blocks bs1.length bs1 none rfl hcap1 (fun _ h => by simp at h) with
      ⟨bs2, hp2, hno2, _⟩
    let w := bs2.flatMap Block.expand
    refine ⟨w, (perm_flatMap hp2).trans (hp_exp1.trans hp_parts), ?_⟩
    rw [maxRuns_expand bs2 hno2, List.map_map]
    exact (hp2.map Block.sum).nodup_iff.mpr hds1
  · rintro ⟨w, hp_parts, hnodup⟩
    have hwpos : ∀ x ∈ w, x > 0 := fun x hx => hpos x (hp_parts.mem_iff.mp hx)
    cases w with
    | nil =>
      refine ⟨[], hp_parts, by simp [DistinctSums]⟩
    | cons x xs =>
      have hxpos : x > 0 := hwpos x List.mem_cons_self
      have hxspos : ∀ y ∈ xs, y > 0 := fun y hy => hwpos y (List.mem_cons_of_mem x hy)
      let bs := toBlocksAux x 1 hxpos (Nat.zero_lt_succ 0) xs hxspos
      refine ⟨bs, ?_, ?_⟩
      · rw [toBlocksAux_expand]
        simpa [List.replicate_one] using hp_parts
      · unfold DistinctSums
        rw [toBlocksAux_sums]
        exact hnodup

/-- Complement Equivalence (Wiseman A381717). -/
theorem wiseman_A381717_iff (parts : List Nat) (hpos : ∀ x ∈ parts, x > 0) :
    (¬ ∃ bs : List Block, (bs.flatMap Block.expand).Perm parts ∧ DistinctSums bs) ↔
    (¬ ∃ w : List Nat, w.Perm parts ∧ ((maxRuns w).map (fun r => r.1 * r.2)).Nodup) :=
  not_congr (wiseman_A382427_iff parts hpos)

end WisemanA382427

#print axioms WisemanA382427.wiseman_A382427_iff
#print axioms WisemanA382427.wiseman_A381717_iff
