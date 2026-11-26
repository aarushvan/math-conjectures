/-
  Formal End-to-End Proof of Conjecture 1 of Grytczuk, Pawlik & Pleszczynski
  (arXiv:2308.13882v2, Section 2.2: "There exists a shuffle anti-square of length 2n
  for every n >= 12").

  Zero external dependencies (Lean 4.36.0 core Init only). Zero sorrys, zero custom axioms.

  Explicit witness family for all n >= 12 (setting t := n - 12 >= 0):
    W(t) = 0^(5+t) ++ 1 ++ 0^2 ++ 1^4 ++ 0^(4+t) ++ 1^3 ++ 0 ++ 1^4.
  Proof structure:
    1. Every cyclic rotation of W(t) matches one of 12 exhaustive cyclic cut templates
       (4 zero-run cuts and 8 one-run cuts).
    2. Any hypothetical shuffle-square split (u, u) induces nonnegative flows (ks, xs, ys)
       satisfying 4 zero-run length equations and 7 gap-balance equations at ranks r = 0..6.
    3. All 568 run-level flow configurations (ks summing to 6) are refuted uniformly for
       all t >= 0 by exact integer Farkas dual certificates checked in the Lean kernel.
-/

namespace ShuffleAntiSquares

/-- Explicit infinite family indexed by t = n - 12 >= 0. -/
def W (t : Nat) : List Bool :=
  List.replicate (5 + t) false ++
  List.replicate 1 true ++
  List.replicate 2 false ++
  List.replicate 4 true ++
  List.replicate (4 + t) false ++
  List.replicate 3 true ++
  List.replicate 1 false ++
  List.replicate 4 true

/-- Cyclic rotation by s positions. -/
def rotate (w : List Bool) (s : Nat) : List Bool :=
  w.drop s ++ w.take s

/-- Inductive definition of splitting w into two disjoint subsequences u and v. -/
inductive IsShuffleSplit : List Bool → List Bool → List Bool → Prop
  | nil : IsShuffleSplit [] [] []
  | left {b : Bool} {w u v : List Bool} :
      IsShuffleSplit w u v → IsShuffleSplit (b :: w) (b :: u) v
  | right {b : Bool} {w u v : List Bool} :
      IsShuffleSplit w u v → IsShuffleSplit (b :: w) u (b :: v)

def IsShuffleSquare (w : List Bool) : Prop :=
  ∃ u, IsShuffleSplit w u u

def IsShuffleAntiSquare (w : List Bool) : Prop :=
  ∀ s, s < w.length → ¬ IsShuffleSquare (rotate w s)

/-! ### Part 1: Length, Symbol Counts, and Replicate/Rotate Lemmas -/

def countTrue : List Bool → Nat
  | [] => 0
  | true :: xs => countTrue xs + 1
  | false :: xs => countTrue xs

theorem countTrue_append (a b : List Bool) :
    countTrue (a ++ b) = countTrue a + countTrue b := by
  induction a with
  | nil => simp [countTrue]
  | cons x xs ih =>
    cases x <;> simp [countTrue, ih] <;> omega

theorem countTrue_rep_false (k : Nat) : countTrue (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, countTrue, ih]

theorem countTrue_rep_true (k : Nat) : countTrue (List.replicate k true) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, countTrue, ih]

theorem countTrue_eq_count (w : List Bool) :
    countTrue w = w.count true := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp [countTrue, ih]

theorem countFalse_add_countTrue (w : List Bool) :
    w.count false + w.count true = w.length := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp <;> omega

theorem length_W (t : Nat) : (W t).length = 2 * (12 + t) := by
  simp only [W, List.length_append, List.length_replicate]
  omega

theorem countTrue_W (t : Nat) : countTrue (W t) = 12 := by
  simp only [W, countTrue_append, countTrue_rep_false, countTrue_rep_true]

theorem count_true_W (t : Nat) : (W t).count true = 12 := by
  rw [← countTrue_eq_count]
  exact countTrue_W t

theorem count_false_W (t : Nat) : (W t).count false = 2 * (12 + t) - 12 := by
  have h1 := countFalse_add_countTrue (W t)
  rw [count_true_W, length_W] at h1
  omega

theorem rotate_split_block (l1 l2 : List Bool) (L : Nat) (b : Bool) (s : Nat)
    (hlo : l1.length ≤ s) (hhi : s ≤ l1.length + L) :
    rotate (l1 ++ List.replicate L b ++ l2) s =
      List.replicate (l1.length + L - s) b ++ l2 ++ l1 ++ List.replicate (s - l1.length) b := by
  simp only [rotate]
  have hd : (l1 ++ List.replicate L b ++ l2).drop s =
      List.replicate (l1.length + L - s) b ++ l2 := by
    rw [List.append_assoc, List.drop_append]
    rw [List.drop_eq_nil_of_le hlo, List.nil_append, List.drop_append]
    have h1 : s - l1.length - (List.replicate L b).length = 0 := by
      rw [List.length_replicate]; omega
    rw [h1, List.drop_zero, List.drop_replicate]
    have h2 : L - (s - l1.length) = l1.length + L - s := by omega
    rw [h2]
  have ht : (l1 ++ List.replicate L b ++ l2).take s =
      l1 ++ List.replicate (s - l1.length) b := by
    rw [List.append_assoc, List.take_append]
    rw [List.take_of_length_le hlo, List.take_append]
    have h1 : s - l1.length - (List.replicate L b).length = 0 := by
      rw [List.length_replicate]; omega
    rw [h1, List.take_zero, List.append_nil, List.take_replicate]
    have h2 : min (s - l1.length) L = s - l1.length := by omega
    rw [h2]
  rw [hd, ht]
  simp only [List.append_assoc]

/-! ### Part 2: Zero-Gap Invariant and Block-Split Flow Extraction -/

def zeroGapFrom (seen r : Nat) : List Bool → Nat
  | [] => 0
  | true :: xs => zeroGapFrom (seen + 1) r xs
  | false :: xs => (if seen == r then 1 else 0) + zeroGapFrom seen r xs

theorem zeroGapFrom_append (seen r : Nat) (a b : List Bool) :
    zeroGapFrom seen r (a ++ b) =
      zeroGapFrom seen r a + zeroGapFrom (seen + countTrue a) r b := by
  induction a generalizing seen with
  | nil => simp [zeroGapFrom, countTrue]
  | cons x xs ih =>
    cases x
    · simp only [List.cons_append, zeroGapFrom, countTrue]
      rw [ih seen, Nat.add_assoc]
    · simp only [List.cons_append, zeroGapFrom, countTrue]
      rw [ih (seen + 1), Nat.add_assoc, Nat.add_comm 1 (countTrue xs)]

theorem IsShuffleSplit_countTrue {w u v : List Bool} (h : IsShuffleSplit w u v) :
    countTrue u + countTrue v = countTrue w := by
  induction h with
  | nil => rfl
  | @left b _ _ _ _ ih => cases b <;> simp [countTrue] <;> omega
  | @right b _ _ _ _ ih => cases b <;> simp [countTrue] <;> omega

theorem IsShuffleSplit_append (a b u v : List Bool)
    (h : IsShuffleSplit (a ++ b) u v) :
    ∃ u1 u2 v1 v2, u = u1 ++ u2 ∧ v = v1 ++ v2 ∧
      IsShuffleSplit a u1 v1 ∧ IsShuffleSplit b u2 v2 := by
  induction a generalizing u v with
  | nil =>
    exact ⟨[], u, [], v, rfl, rfl, IsShuffleSplit.nil, h⟩
  | cons x xs ih =>
    simp only [List.cons_append] at h
    cases h with
    | left hrest =>
      obtain ⟨u1, u2, v1, v2, hu, hv, ha, hb⟩ := ih _ _ hrest
      exact ⟨x :: u1, u2, v1, v2, by rw [hu]; rfl, hv, IsShuffleSplit.left ha, hb⟩
    | right hrest =>
      obtain ⟨u1, u2, v1, v2, hu, hv, ha, hb⟩ := ih _ _ hrest
      exact ⟨u1, u2, x :: v1, v2, hu, by rw [hv]; rfl, IsShuffleSplit.right ha, hb⟩

theorem IsShuffleSplit_all_false (k : Nat) (u v : List Bool)
    (h : IsShuffleSplit (List.replicate k false) u v) :
    countTrue u = 0 ∧ countTrue v = 0 ∧ u.length + v.length = k := by
  induction k generalizing u v with
  | zero =>
    cases h
    exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
    rw [List.replicate_succ] at h
    cases h with
    | left hrest =>
      obtain ⟨hu, hv, hl⟩ := ih _ _ hrest
      exact ⟨by simp [countTrue, hu], hv, by simp; omega⟩
    | right hrest =>
      obtain ⟨hu, hv, hl⟩ := ih _ _ hrest
      exact ⟨hu, by simp [countTrue, hv], by simp; omega⟩

theorem zeroGapFrom_countTrue_zero (seen r : Nat) (u : List Bool)
    (hz : countTrue u = 0) :
    zeroGapFrom seen r u = if seen == r then u.length else 0 := by
  induction u with
  | nil => simp [zeroGapFrom]
  | cons x xs ih =>
    cases x
    · simp only [countTrue] at hz
      have hxs := ih hz
      simp only [zeroGapFrom, hxs, List.length_cons]
      by_cases hr : seen == r <;> simp [hr] <;> omega
    · simp [countTrue] at hz

theorem IsShuffleSplit_all_true (k : Nat) :
    ∀ u v seen r, IsShuffleSplit (List.replicate k true) u v →
      zeroGapFrom seen r u = 0 ∧ zeroGapFrom seen r v = 0 ∧ countTrue u + countTrue v = k := by
  induction k with
  | zero =>
    intro u v seen r h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
    intro u v seen r h
    rw [List.replicate_succ] at h
    cases h with
    | left hrest =>
      obtain ⟨hu, _, hc⟩ := ih _ _ (seen + 1) r hrest
      obtain ⟨_, hv, _⟩ := ih _ _ seen r hrest
      exact ⟨by simp only [zeroGapFrom]; exact hu, hv, by simp [countTrue]; omega⟩
    | right hrest =>
      obtain ⟨hu, _, hc⟩ := ih _ _ seen r hrest
      obtain ⟨_, hv, _⟩ := ih _ _ (seen + 1) r hrest
      exact ⟨hu, by simp only [zeroGapFrom]; exact hv, by simp [countTrue]; omega⟩

/-! ### Part 3: Block Rendering & Flow Reduction -/

def render : List (Bool × Nat) → List Bool
  | [] => []
  | (b, k) :: bs => List.replicate k b ++ render bs

inductive MatchesSplit : List (Bool × Nat) → List Nat → List Nat → List Nat → Prop
  | nil : MatchesSplit [] [] [] []
  | onetrue {o k : Nat} {bs ks xs ys} :
      k ≤ o → MatchesSplit bs ks xs ys → MatchesSplit ((true, o) :: bs) (k :: ks) xs ys
  | zero {z x y : Nat} {bs ks xs ys} :
      x + y = z → MatchesSplit bs ks xs ys → MatchesSplit ((false, z) :: bs) ks (x :: xs) (y :: ys)

def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

def gapU (su r : Nat) : List (Bool × Nat) → List Nat → List Nat → Nat
  | [], _, _ => 0
  | (true, _) :: bs, k :: ks, xs => gapU (su + k) r bs ks xs
  | (false, _) :: bs, ks, x :: xs => (if su == r then x else 0) + gapU su r bs ks xs
  | _, _, _ => 0

def gapV (sv r : Nat) : List (Bool × Nat) → List Nat → List Nat → Nat
  | [], _, _ => 0
  | (true, o) :: bs, k :: ks, ys => gapV (sv + (o - k)) r bs ks ys
  | (false, _) :: bs, ks, y :: ys => (if sv == r then y else 0) + gapV sv r bs ks ys
  | _, _, _ => 0

theorem countTrue_render (bs : List (Bool × Nat)) :
    countTrue (render bs) = sumList (bs.filterMap fun p => if p.1 then some p.2 else none) := by
  induction bs with
  | nil => rfl
  | cons p tl ih =>
    rcases p with ⟨b, k⟩
    cases b <;> simp [render, countTrue_append, countTrue_rep_false, countTrue_rep_true, sumList, ih]

theorem split_render (bs : List (Bool × Nat)) (u v : List Bool)
    (h : IsShuffleSplit (render bs) u v) :
    ∀ su sv : Nat, ∃ ks xs ys : List Nat,
      MatchesSplit bs ks xs ys ∧
      sumList ks = countTrue u ∧
      (∀ r, zeroGapFrom su r u = gapU su r bs ks xs) ∧
      (∀ r, zeroGapFrom sv r v = gapV sv r bs ks ys) := by
  induction bs generalizing u v with
  | nil =>
    intro su sv
    cases h
    exact ⟨[], [], [], MatchesSplit.nil, rfl, fun _ => rfl, fun _ => rfl⟩
  | cons hd tl ih =>
    intro su sv
    rcases hd with ⟨b, k⟩
    simp only [render] at h
    obtain ⟨u1, u2, v1, v2, rfl, rfl, h1, h2⟩ := IsShuffleSplit_append _ _ u v h
    cases b
    · obtain ⟨cu1, cv1, hlen1⟩ := IsShuffleSplit_all_false k u1 v1 h1
      obtain ⟨ks, xs, ys, hm, hsum, hgu, hgv⟩ := ih u2 v2 h2 su sv
      refine ⟨ks, u1.length :: xs, v1.length :: ys, MatchesSplit.zero hlen1 hm, ?_, ?_, ?_⟩
      · simp [countTrue_append, cu1, hsum]
      · intro r
        rw [zeroGapFrom_append, cu1, Nat.add_zero, zeroGapFrom_countTrue_zero su r u1 cu1]
        simp only [gapU, hgu r]
      · intro r
        rw [zeroGapFrom_append, cv1, Nat.add_zero, zeroGapFrom_countTrue_zero sv r v1 cv1]
        simp only [gapV, hgv r]
    · obtain ⟨_, _, hct1⟩ := IsShuffleSplit_all_true k u1 v1 0 0 h1
      have hko : countTrue u1 ≤ k := by omega
      have hcv1 : countTrue v1 = k - countTrue u1 := by omega
      obtain ⟨ks, xs, ys, hm, hsum, hgu, hgv⟩ :=
        ih u2 v2 h2 (su + countTrue u1) (sv + (k - countTrue u1))
      refine ⟨countTrue u1 :: ks, xs, ys, MatchesSplit.onetrue hko hm, ?_, ?_, ?_⟩
      · simp [countTrue_append, sumList, hsum]
      · intro r
        have hzu1 : zeroGapFrom su r u1 = 0 := (IsShuffleSplit_all_true k u1 v1 su r h1).1
        rw [zeroGapFrom_append, hzu1, Nat.zero_add]
        simp only [gapU, hgu r]
      · intro r
        have hzv1 : zeroGapFrom sv r v1 = 0 := (IsShuffleSplit_all_true k u1 v1 sv r h1).2.1
        rw [zeroGapFrom_append, hzv1, Nat.zero_add, hcv1]
        simp only [gapV, hgv r]

/-! ### Part 4: 12 Cut Templates and 568 Kernel-Checked Farkas Duals -/

def duals_0 : List Nat := [1622, 4538, 60379, 63997, 59677, 60619, 60646, 67180, 99958, 63508, 70096, 63562, 63535, 72310, 111622, 72283, 60376, 63994, 59674, 60862, 60889, 67423, 100201, 63751, 70339, 63805, 63778, 72313, 111625, 72286, 39854, 157952]
def duals_1 : List Nat := [40016, 39548, 119720, 43904, 122636, 40016, 40034, 120206, 40034, 118766, 53138, 131870, 40280, 119003, 44636, 123368, 53384, 132116, 40271, 119012, 43904, 122636, 43922, 122654, 43904, 122654, 122636, 52490, 131222, 52490, 131240, 131222]
def duals_2 : List Nat := [2108, 60619, 64969, 63511, 63565, 72310, 111622, 2114, 60622, 64969, 63991, 64045, 72793, 112105, 98983, 99010, 60616, 64963, 64963, 65017, 73765, 113077, 98503, 98530, 118268, 63508, 63562, 72313, 111625, 98503, 100714, 122474]
def duals_3 : List Nat := [4538, 218, 5024, 704, 40016, 59671, 72757, 98983, 61129, 74197, 100441, 120206, 5288, 72994, 99238, 119003, 5279, 75181, 101425, 119012, 4538, 76627, 102871, 63559, 76627, 102889, 76681, 13124, 13178, 131222, 52544, 170588]
def duals_4 : List Nat := [52650, 52656, 20127, 79176, 52656, 21339, 80388, 119718, 52656, 19887, 78936, 118266, 52980, 20208, 79257, 52980, 20211, 79260, 118590, 55164, 22395, 81444, 120774, 52974, 33327, 92376, 118590, 53952, 21177, 80226, 119556, 56136, 23367, 82416, 121746, 53952, 21183, 80232, 119562, 21180, 80229, 119562, 56868, 24099, 83148, 122478, 56862, 37215, 96264, 122478, 24096, 83145, 122478, 122472]
def duals_5 : List Nat := [17658, 13284, 13338, 17664, 13290, 13344, 40068, 158112, 17664, 13290, 13344, 39588, 157632, 118266, 17658, 17658, 17712, 43956, 162000, 118266, 17746, 13372, 13426, 39667, 157711, 17746, 14824, 14878, 41122, 159166, 119800, 17740, 17740, 17794, 44038, 162082, 118348, 13369, 13423, 39670, 157714, 118348, 18960, 14580, 14634, 40878, 158922, 119556, 18960, 14586, 14640, 40884, 158928, 119562, 14580, 14634, 40884, 158928, 119562, 40878, 158922, 158922]
def duals_6 : List Nat := [5994, 4536, 17664, 6762, 26445, 6000, 4542, 17664, 6765, 26448, 39534, 157632, 6000, 5268, 18390, 7491, 27174, 40260, 158358, 118266, 4536, 17658, 11133, 30816, 39534, 157632, 118266, 6324, 4866, 17988, 7083, 26766, 39852, 157950, 6324, 5592, 18714, 7815, 27498, 40584, 158682, 118590, 4866, 17988, 7089, 26772, 39858, 157956, 118590, 7086, 26769, 39858, 171072, 131706]
def duals_7 : List Nat := [40014, 702, 2000, 120044, 40844, 119558, 45200, 123932, 41727, 120459, 48288, 127020, 52650, 131382, 52650, 131400, 542, 2000, 120044, 41086, 119800, 45442, 124174, 41809, 120541, 48370, 127102, 52732, 131464, 52732, 131482, 39368, 39422, 157520, 40842, 119556, 45198, 123930, 43023, 121755, 49584, 128316, 52490, 131222, 52490, 131240, 39368, 39422, 158976, 119556]
def duals_8 : List Nat := [13284, 13772, 704, 542, 20207, 2000, 21656, 120044, 14760, 21330, 119718, 14760, 21348, 119736, 17676, 24264, 122652, 17658, 37368, 122652, 13284, 32994, 13338, 33003, 52704, 540, 20205, 1998, 21654, 120042, 15084, 21654, 120042, 15084, 21672, 120060, 18000, 24588, 122976, 17982, 37692, 122976, 13124, 32834, 13178, 32843, 52544, 39422, 157466, 157950]
def duals_9 : List Nat := [40986, 39546, 118278, 46101, 124833, 41472, 40032, 118764, 46584, 125316, 40014, 40068, 39870, 4920, 122964, 46422, 125154, 39852, 39906, 40351, 4920, 122964, 46428, 125160, 39858, 39912, 118590, 40830, 5892, 123936, 47400, 126132, 40830, 40884, 118840, 5886, 123930, 51768, 130500, 40830, 40884, 123948, 4428, 122472, 50310, 129042, 43758, 122490, 122472, 50313, 129045, 56880, 135612, 135594]
def duals_10 : List Nat := [13770, 13302, 19890, 4596, 24252, 122640, 13284, 32994, 13338, 13770, 13788, 20376, 5076, 24732, 123120, 13770, 33480, 13824, 40068, 158112, 13610, 14830, 1762, 4675, 24331, 122719, 13369, 33079, 13423, 39667, 157711, 14827, 1759, 5404, 25060, 123448, 14098, 33808, 14152, 39670, 157714, 119558, 14580, 1512, 5886, 25542, 123930, 14580, 34290, 14634, 21186, 119574, 119556, 5886, 25542, 123930, 14586, 34296, 14640, 25560, 123948, 123930]
def duals_11 : List Nat := [4536, 4554, 13302, 6000, 1680, 40992, 2385, 15480, 41724, 61434, 13284, 13338, 131382, 4711, 13459, 6000, 1680, 40992, 2391, 15486, 41730, 61440, 13290, 13344, 131388, 39534, 157632, 4866, 13614, 6324, 2004, 41316, 2715, 15810, 42054, 61764, 13614, 13668, 131712, 39622, 138037, 6318, 1998, 41310, 4167, 17262, 43506, 63216, 13614, 13668, 131712, 41328, 120060, 120042]

def templateZSpecs : Nat → List (Nat × Nat)
  | 0 => [(5, 1), (2, 0), (4, 1), (1, 0)]
  | 1 => [(2, 0), (4, 1), (1, 0), (5, 1)]
  | 2 => [(4, 1), (1, 0), (5, 1), (2, 0)]
  | 3 => [(1, 0), (5, 1), (2, 0), (4, 1)]
  | 4 | 5 | 6 => [(4, 1), (1, 0), (5, 1), (2, 0)]
  | 7 | 8 => [(1, 0), (5, 1), (2, 0), (4, 1)]
  | 9 | 10 | 11 => [(5, 1), (2, 0), (4, 1), (1, 0)]
  | _ => []

def templateOLens : Nat → List Nat
  | 0 => [1, 4, 3, 4]
  | 1 => [4, 3, 4, 1]
  | 2 => [3, 4, 1, 4]
  | 3 => [4, 1, 4, 3]
  | 4 => [3, 3, 4, 1, 1]
  | 5 => [2, 3, 4, 1, 2]
  | 6 => [1, 3, 4, 1, 3]
  | 7 => [2, 4, 1, 4, 1]
  | 8 => [1, 4, 1, 4, 2]
  | 9 => [3, 1, 4, 3, 1]
  | 10 => [2, 1, 4, 3, 2]
  | 11 => [1, 1, 4, 3, 3]
  | _ => []

def templateDuals : Nat → List Nat
  | 0 => duals_0 | 1 => duals_1 | 2 => duals_2 | 3 => duals_3
  | 4 => duals_4 | 5 => duals_5 | 6 => duals_6 | 7 => duals_7
  | 8 => duals_8 | 9 => duals_9 | 10 => duals_10 | 11 => duals_11
  | _ => []

def zLenNat (spec : Nat × Nat) (t : Nat) : Nat :=
  spec.1 + spec.2 * t

def templateBlocks (tidx z2 z1 t : Nat) : List (Bool × Nat) :=
  let zs := templateZSpecs tidx
  let ol := templateOLens tidx
  if tidx < 4 then
    [ (false, z2), (true, ol.getD 0 0),
      (false, zLenNat (zs.getD 1 (0, 0)) t), (true, ol.getD 1 0),
      (false, zLenNat (zs.getD 2 (0, 0)) t), (true, ol.getD 2 0),
      (false, zLenNat (zs.getD 3 (0, 0)) t), (true, ol.getD 3 0),
      (false, z1) ]
  else
    [ (true, ol.getD 0 0), (false, zLenNat (zs.getD 0 (0, 0)) t),
      (true, ol.getD 1 0), (false, zLenNat (zs.getD 1 (0, 0)) t),
      (true, ol.getD 2 0), (false, zLenNat (zs.getD 2 (0, 0)) t),
      (true, ol.getD 3 0), (false, zLenNat (zs.getD 3 (0, 0)) t),
      (true, ol.getD 4 0) ]

def unpackD (code i : Nat) : Int :=
  Int.ofNat ((code / (3 ^ i)) % 3) - 1

def prefSum : List Nat → Nat → Nat
  | [], _ => 0
  | _, 0 => 0
  | x :: xs, i + 1 => x + prefSum xs i

def lenRowOf (tidx j : Nat) : Nat :=
  if tidx < 4 && j == 4 then 0 else j

def oBeforeOf (tidx j : Nat) : Nat :=
  if tidx < 4 then j else j + 1

def checkDualFast (tidx : Nat) (ks : List Nat) (code : Nat) : Bool :=
  let zs := templateZSpecs tidx
  let ol := templateOLens tidx
  let nz := if tidx < 4 then 5 else 4
  let alpha_t : Int :=
    -(unpackD code 0 * Int.ofNat (zs.getD 0 (0,0)).2 +
      unpackD code 1 * Int.ofNat (zs.getD 1 (0,0)).2 +
      unpackD code 2 * Int.ofNat (zs.getD 2 (0,0)).2 +
      unpackD code 3 * Int.ofNat (zs.getD 3 (0,0)).2)
  let rhs_dot : Int :=
    unpackD code 0 * Int.ofNat (zs.getD 0 (0,0)).1 +
    unpackD code 1 * Int.ofNat (zs.getD 1 (0,0)).1 +
    unpackD code 2 * Int.ofNat (zs.getD 2 (0,0)).1 +
    unpackD code 3 * Int.ofNat (zs.getD 3 (0,0)).1
  let okX := (List.range nz).all fun j =>
    let ob := oBeforeOf tidx j
    let ur := prefSum ks ob
    decide (unpackD code (lenRowOf tidx j) + unpackD code (4 + ur) ≥ 0)
  let okY := (List.range nz).all fun j =>
    let ob := oBeforeOf tidx j
    let vr := prefSum ol ob - prefSum ks ob
    decide (unpackD code (lenRowOf tidx j) - unpackD code (4 + vr) ≥ 0)
  decide (alpha_t ≥ 0) && decide (rhs_dot < 0) && okX && okY

def enumSplitsAux : List Nat → Nat → List (List Nat)
  | [], 0 => [[]]
  | [], _ + 1 => []
  | o :: os, rem =>
    (List.range (min o rem + 1)).flatMap fun k =>
      (enumSplitsAux os (rem - k)).map (k :: ·)

def checkZipFast (tidx : Nat) : List (List Nat) → List Nat → Bool
  | [], [] => true
  | ks :: kss, code :: codes => checkDualFast tidx ks code && checkZipFast tidx kss codes
  | _, _ => false

def checkT (tidx : Nat) : Bool :=
  checkZipFast tidx (enumSplitsAux (templateOLens tidx) 6) (templateDuals tidx)

theorem t0_ok : checkT 0 = true := by decide
theorem t1_ok : checkT 1 = true := by decide
theorem t2_ok : checkT 2 = true := by decide
theorem t3_ok : checkT 3 = true := by decide
theorem t4_ok : checkT 4 = true := by decide
theorem t5_ok : checkT 5 = true := by decide
theorem t6_ok : checkT 6 = true := by decide
theorem t7_ok : checkT 7 = true := by decide
theorem t8_ok : checkT 8 = true := by decide
theorem t9_ok : checkT 9 = true := by decide
theorem t10_ok : checkT 10 = true := by decide
theorem t11_ok : checkT 11 = true := by decide

/-! ### Part 5: Farkas Soundness, Cut Classification, and Main Theorem -/

def boundedList : List Nat → List Nat → Prop
  | [], [] => True
  | k :: ks, o :: os => k ≤ o ∧ boundedList ks os
  | _, _ => False

theorem mem_enumSplitsAux (os ks : List Nat) (rem : Nat)
    (hb : boundedList ks os) (hs : sumList ks = rem) :
    ks ∈ enumSplitsAux os rem := by
  induction os generalizing ks rem with
  | nil =>
    cases ks with
    | nil =>
      have : rem = 0 := by simpa [sumList] using hs.symm
      subst this; simp [enumSplitsAux]
    | cons _ _ => exact False.elim hb
  | cons o os ih =>
    cases ks with
    | nil => exact False.elim hb
    | cons k ks =>
      obtain ⟨hko, htl⟩ := hb
      simp only [sumList] at hs
      simp only [enumSplitsAux, List.mem_flatMap, List.mem_map, List.mem_range]
      exact ⟨k, by omega, ks, ih ks (rem - k) htl (by omega), rfl⟩

theorem exists_dual_of_checkZipFast (tidx : Nat) :
    ∀ (kss : List (List Nat)) (duals : List Nat),
      checkZipFast tidx kss duals = true →
      ∀ ks ∈ kss, ∃ code : Nat, checkDualFast tidx ks code = true := by
  intro kss duals hchk ks hmem
  induction kss generalizing duals with
  | nil => cases hmem
  | cons k0 kss ih =>
    cases duals with
    | nil => simp [checkZipFast] at hchk
    | cons c0 cs =>
      simp only [checkZipFast, Bool.and_eq_true] at hchk
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact ⟨c0, hchk.1⟩
      · exact ih cs hchk.2 htail

theorem exists_dual_template (tidx : Nat) (ht : tidx < 12) (ks : List Nat)
    (hb : boundedList ks (templateOLens tidx)) (hs : sumList ks = 6) :
    ∃ code : Nat, checkDualFast tidx ks code = true := by
  have hmem := mem_enumSplitsAux (templateOLens tidx) ks 6 hb hs
  have hchk : checkT tidx = true := by
    rcases (by omega : tidx = 0 ∨ tidx = 1 ∨ tidx = 2 ∨ tidx = 3 ∨ tidx = 4 ∨ tidx = 5 ∨
        tidx = 6 ∨ tidx = 7 ∨ tidx = 8 ∨ tidx = 9 ∨ tidx = 10 ∨ tidx = 11) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact t0_ok
    · exact t1_ok
    · exact t2_ok
    · exact t3_ok
    · exact t4_ok
    · exact t5_ok
    · exact t6_ok
    · exact t7_ok
    · exact t8_ok
    · exact t9_ok
    · exact t10_ok
    · exact t11_ok
  exact exists_dual_of_checkZipFast tidx _ _ hchk ks hmem

theorem forall_range_of_all (n : Nat) (p : Nat → Bool) (h : (List.range n).all p = true) :
    ∀ j, j < n → p j = true := by
  intro j hj
  rw [List.all_eq_true] at h
  exact h j (List.mem_range.mpr hj)

def sum7 (f : Nat → Int) : Int :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6

theorem sum7_ite (r : Nat) (hr : r ≤ 6) (w : Nat → Int) (x : Int) :
    sum7 (fun q => w q * (if r == q then x else 0)) = w r * x := by
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [sum7]

theorem sum7_add (f g : Nat → Int) :
    sum7 (fun q => f q + g q) = sum7 f + sum7 g := by
  simp only [sum7]; omega

theorem sum7_sub (f g : Nat → Int) :
    sum7 (fun q => f q - g q) = sum7 f - sum7 g := by
  simp only [sum7]; omega

theorem sum7_zero (f : Nat → Int) (h : ∀ q, q ≤ 6 → f q = 0) : sum7 f = 0 := by
  simp only [sum7, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
    h 4 (by omega), h 5 (by omega), h 6 (by omega)]
  omega

theorem sum7_congr (f g : Nat → Int) (h : ∀ q, q ≤ 6 → f q = g q) : sum7 f = sum7 g := by
  simp only [sum7, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
    h 4 (by omega), h 5 (by omega), h 6 (by omega)]

theorem sum7_ite5 (r0 r1 r2 r3 r4 u0 u1 u2 u3 u4 : Nat)
    (hr0 : r0 ≤ 6) (hr1 : r1 ≤ 6) (hr2 : r2 ≤ 6) (hr3 : r3 ≤ 6) (hr4 : r4 ≤ 6)
    (hu0 : u0 ≤ 6) (hu1 : u1 ≤ 6) (hu2 : u2 ≤ 6) (hu3 : u3 ≤ 6) (hu4 : u4 ≤ 6)
    (w : Nat → Int) (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 : Int) :
    sum7 (fun q => w q *
      (((if r0 == q then x0 else 0) + (if r1 == q then x1 else 0) +
        (if r2 == q then x2 else 0) + (if r3 == q then x3 else 0) +
        (if r4 == q then x4 else 0)) -
       ((if u0 == q then y0 else 0) + (if u1 == q then y1 else 0) +
        (if u2 == q then y2 else 0) + (if u3 == q then y3 else 0) +
        (if u4 == q then y4 else 0)))) =
    (w r0 * x0 + w r1 * x1 + w r2 * x2 + w r3 * x3 + w r4 * x4) -
    (w u0 * y0 + w u1 * y1 + w u2 * y2 + w u3 * y3 + w u4 * y4) := by
  simp only [Int.mul_sub, Int.mul_add, sum7_sub, sum7_add,
    sum7_ite r0 hr0, sum7_ite r1 hr1, sum7_ite r2 hr2, sum7_ite r3 hr3, sum7_ite r4 hr4,
    sum7_ite u0 hu0, sum7_ite u1 hu1, sum7_ite u2 hu2, sum7_ite u3 hu3, sum7_ite u4 hu4]

theorem sum7_ite4 (r0 r1 r2 r3 u0 u1 u2 u3 : Nat)
    (hr0 : r0 ≤ 6) (hr1 : r1 ≤ 6) (hr2 : r2 ≤ 6) (hr3 : r3 ≤ 6)
    (hu0 : u0 ≤ 6) (hu1 : u1 ≤ 6) (hu2 : u2 ≤ 6) (hu3 : u3 ≤ 6)
    (w : Nat → Int) (x0 x1 x2 x3 y0 y1 y2 y3 : Int) :
    sum7 (fun q => w q *
      (((if r0 == q then x0 else 0) + (if r1 == q then x1 else 0) +
        (if r2 == q then x2 else 0) + (if r3 == q then x3 else 0)) -
       ((if u0 == q then y0 else 0) + (if u1 == q then y1 else 0) +
        (if u2 == q then y2 else 0) + (if u3 == q then y3 else 0)))) =
    (w r0 * x0 + w r1 * x1 + w r2 * x2 + w r3 * x3) -
    (w u0 * y0 + w u1 * y1 + w u2 * y2 + w u3 * y3) := by
  simp only [Int.mul_sub, Int.mul_add, sum7_sub, sum7_add,
    sum7_ite r0 hr0, sum7_ite r1 hr1, sum7_ite r2 hr2, sum7_ite r3 hr3,
    sum7_ite u0 hu0, sum7_ite u1 hu1, sum7_ite u2 hu2, sum7_ite u3 hu3]

theorem matches_ZCut {z0 z1 z2 z3 z4 o0 o1 o2 o3 : Nat} {ks xs ys : List Nat}
    (h : MatchesSplit [(false, z0), (true, o0), (false, z1), (true, o1),
        (false, z2), (true, o2), (false, z3), (true, o3), (false, z4)] ks xs ys) :
    ∃ k0 k1 k2 k3 x0 x1 x2 x3 x4 y0 y1 y2 y3 y4,
      ks = [k0, k1, k2, k3] ∧ xs = [x0, x1, x2, x3, x4] ∧ ys = [y0, y1, y2, y3, y4] ∧
      k0 ≤ o0 ∧ k1 ≤ o1 ∧ k2 ≤ o2 ∧ k3 ≤ o3 ∧
      x0 + y0 = z0 ∧ x1 + y1 = z1 ∧ x2 + y2 = z2 ∧ x3 + y3 = z3 ∧ x4 + y4 = z4 := by
  cases h with | zero hx0 h =>
  cases h with | onetrue hk0 h =>
  cases h with | zero hx1 h =>
  cases h with | onetrue hk1 h =>
  cases h with | zero hx2 h =>
  cases h with | onetrue hk2 h =>
  cases h with | zero hx3 h =>
  cases h with | onetrue hk3 h =>
  cases h with | zero hx4 h =>
  cases h
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl,
    hk0, hk1, hk2, hk3, hx0, hx1, hx2, hx3, hx4⟩

theorem matches_OCut {z0 z1 z2 z3 o0 o1 o2 o3 o4 : Nat} {ks xs ys : List Nat}
    (h : MatchesSplit [(true, o0), (false, z0), (true, o1), (false, z1),
        (true, o2), (false, z2), (true, o3), (false, z3), (true, o4)] ks xs ys) :
    ∃ k0 k1 k2 k3 k4 x0 x1 x2 x3 y0 y1 y2 y3,
      ks = [k0, k1, k2, k3, k4] ∧ xs = [x0, x1, x2, x3] ∧ ys = [y0, y1, y2, y3] ∧
      k0 ≤ o0 ∧ k1 ≤ o1 ∧ k2 ≤ o2 ∧ k3 ≤ o3 ∧ k4 ≤ o4 ∧
      x0 + y0 = z0 ∧ x1 + y1 = z1 ∧ x2 + y2 = z2 ∧ x3 + y3 = z3 := by
  cases h with | onetrue hk0 h =>
  cases h with | zero hx0 h =>
  cases h with | onetrue hk1 h =>
  cases h with | zero hx1 h =>
  cases h with | onetrue hk2 h =>
  cases h with | zero hx2 h =>
  cases h with | onetrue hk3 h =>
  cases h with | zero hx3 h =>
  cases h with | onetrue hk4 h =>
  cases h
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl,
    hk0, hk1, hk2, hk3, hk4, hx0, hx1, hx2, hx3⟩

theorem boundedList_getD4 {k0 k1 k2 k3 : Nat} {ol : List Nat} (hlen : ol.length = 4)
    (h0 : k0 ≤ ol.getD 0 0) (h1 : k1 ≤ ol.getD 1 0)
    (h2 : k2 ≤ ol.getD 2 0) (h3 : k3 ≤ ol.getD 3 0) :
    boundedList [k0, k1, k2, k3] ol := by
  rcases ol with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | _⟩⟩⟩⟩ <;> simp at hlen
  exact ⟨h0, h1, h2, h3, trivial⟩

theorem boundedList_getD5 {k0 k1 k2 k3 k4 : Nat} {ol : List Nat} (hlen : ol.length = 5)
    (h0 : k0 ≤ ol.getD 0 0) (h1 : k1 ≤ ol.getD 1 0) (h2 : k2 ≤ ol.getD 2 0)
    (h3 : k3 ≤ ol.getD 3 0) (h4 : k4 ≤ ol.getD 4 0) :
    boundedList [k0, k1, k2, k3, k4] ol := by
  rcases ol with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | _⟩⟩⟩⟩⟩ <;> simp at hlen
  exact ⟨h0, h1, h2, h3, h4, trivial⟩

theorem template_len4 : ∀ t ∈ List.range 4, (templateOLens t).length = 4 := by decide
theorem template_len5 : ∀ t ∈ List.range 12, t ≥ 4 → (templateOLens t).length = 5 := by decide
theorem template_sum4 : ∀ t ∈ List.range 4,
    (templateOLens t).getD 0 0 + (templateOLens t).getD 1 0 +
    (templateOLens t).getD 2 0 + (templateOLens t).getD 3 0 = 12 := by decide
theorem template_sum5 : ∀ t ∈ List.range 12, t ≥ 4 →
    (templateOLens t).getD 0 0 + (templateOLens t).getD 1 0 +
    (templateOLens t).getD 2 0 + (templateOLens t).getD 3 0 +
    (templateOLens t).getD 4 0 = 12 := by decide

theorem int_mul_nonneg_of_nat (a : Int) (ha : a ≥ 0) (n : Nat) : a * Int.ofNat n ≥ 0 :=
  Int.mul_nonneg ha (Int.natCast_nonneg n)


theorem farkas_zcut_absurd
    (d0 d1 d2 d3 du0 du1 du2 du3 du4 dv0 dv1 dv2 dv3 dv4 : Int)
    (c0 c1 c2 c3 m0 m1 m2 m3 : Int)
    (t x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 : Int)
    (ht : 0 ≤ t) (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3) (hx4 : 0 ≤ x4)
    (hy0 : 0 ≤ y0) (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2) (hy3 : 0 ≤ y3) (hy4 : 0 ≤ y4)
    (hat : 0 ≤ -(d0 * m0 + d1 * m1 + d2 * m2 + d3 * m3))
    (hrhs : d0 * c0 + d1 * c1 + d2 * c2 + d3 * c3 < 0)
    (hax0 : 0 ≤ d0 + du0) (hax1 : 0 ≤ d1 + du1) (hax2 : 0 ≤ d2 + du2)
    (hax3 : 0 ≤ d3 + du3) (hax4 : 0 ≤ d0 + du4)
    (hay0 : 0 ≤ d0 - dv0) (hay1 : 0 ≤ d1 - dv1) (hay2 : 0 ≤ d2 - dv2)
    (hay3 : 0 ≤ d3 - dv3) (hay4 : 0 ≤ d0 - dv4)
    (heq0 : x0 + y0 + x4 + y4 - (c0 + m0 * t) = 0)
    (heq1 : x1 + y1 - (c1 + m1 * t) = 0)
    (heq2 : x2 + y2 - (c2 + m2 * t) = 0)
    (heq3 : x3 + y3 - (c3 + m3 * t) = 0)
    (hgap : (du0 * x0 + du1 * x1 + du2 * x2 + du3 * x3 + du4 * x4) -
            (dv0 * y0 + dv1 * y1 + dv2 * y2 + dv3 * y3 + dv4 * y4) = 0) : False := by
  have hnonneg :
      (-(d0 * m0 + d1 * m1 + d2 * m2 + d3 * m3)) * t +
      ((d0 + du0) * x0 + (d1 + du1) * x1 + (d2 + du2) * x2 +
       (d3 + du3) * x3 + (d0 + du4) * x4) +
      ((d0 - dv0) * y0 + (d1 - dv1) * y1 + (d2 - dv2) * y2 +
       (d3 - dv3) * y3 + (d0 - dv4) * y4) ≥ 0 := by
    have p0 := Int.mul_nonneg hat ht
    have px0 := Int.mul_nonneg hax0 hx0
    have px1 := Int.mul_nonneg hax1 hx1
    have px2 := Int.mul_nonneg hax2 hx2
    have px3 := Int.mul_nonneg hax3 hx3
    have px4 := Int.mul_nonneg hax4 hx4
    have py0 := Int.mul_nonneg hay0 hy0
    have py1 := Int.mul_nonneg hay1 hy1
    have py2 := Int.mul_nonneg hay2 hy2
    have py3 := Int.mul_nonneg hay3 hy3
    have py4 := Int.mul_nonneg hay4 hy4
    omega
  have hid :
      (-(d0 * m0 + d1 * m1 + d2 * m2 + d3 * m3)) * t +
      ((d0 + du0) * x0 + (d1 + du1) * x1 + (d2 + du2) * x2 +
       (d3 + du3) * x3 + (d0 + du4) * x4) +
      ((d0 - dv0) * y0 + (d1 - dv1) * y1 + (d2 - dv2) * y2 +
       (d3 - dv3) * y3 + (d0 - dv4) * y4) =
      d0 * c0 + d1 * c1 + d2 * c2 + d3 * c3 := by
    grind
  omega

theorem farkas_ocut_absurd
    (d0 d1 d2 d3 du0 du1 du2 du3 dv0 dv1 dv2 dv3 : Int)
    (c0 c1 c2 c3 m0 m1 m2 m3 : Int)
    (t x0 x1 x2 x3 y0 y1 y2 y3 : Int)
    (ht : 0 ≤ t) (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3)
    (hy0 : 0 ≤ y0) (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2) (hy3 : 0 ≤ y3)
    (hat : 0 ≤ -(d0 * m0 + d1 * m1 + d2 * m2 + d3 * m3))
    (hrhs : d0 * c0 + d1 * c1 + d2 * c2 + d3 * c3 < 0)
    (hax0 : 0 ≤ d0 + du0) (hax1 : 0 ≤ d1 + du1) (hax2 : 0 ≤ d2 + du2) (hax3 : 0 ≤ d3 + du3)
    (hay0 : 0 ≤ d0 - dv0) (hay1 : 0 ≤ d1 - dv1) (hay2 : 0 ≤ d2 - dv2) (hay3 : 0 ≤ d3 - dv3)
    (heq0 : x0 + y0 - (c0 + m0 * t) = 0)
    (heq1 : x1 + y1 - (c1 + m1 * t) = 0)
    (heq2 : x2 + y2 - (c2 + m2 * t) = 0)
    (heq3 : x3 + y3 - (c3 + m3 * t) = 0)
    (hgap : (du0 * x0 + du1 * x1 + du2 * x2 + du3 * x3) -
            (dv0 * y0 + dv1 * y1 + dv2 * y2 + dv3 * y3) = 0) : False := by
  have hnonneg :
      (-(d0 * m0 + d1 * m1 + d2 * m2 + d3 * m3)) * t +
      ((d0 + du0) * x0 + (d1 + du1) * x1 + (d2 + du2) * x2 + (d3 + du3) * x3) +
      ((d0 - dv0) * y0 + (d1 - dv1) * y1 + (d2 - dv2) * y2 + (d3 - dv3) * y3) ≥ 0 := by
    have p0 := Int.mul_nonneg hat ht
    have px0 := Int.mul_nonneg hax0 hx0
    have px1 := Int.mul_nonneg hax1 hx1
    have px2 := Int.mul_nonneg hax2 hx2
    have px3 := Int.mul_nonneg hax3 hx3
    have py0 := Int.mul_nonneg hay0 hy0
    have py1 := Int.mul_nonneg hay1 hy1
    have py2 := Int.mul_nonneg hay2 hy2
    have py3 := Int.mul_nonneg hay3 hy3
    omega
  have hid :
      (-(d0 * m0 + d1 * m1 + d2 * m2 + d3 * m3)) * t +
      ((d0 + du0) * x0 + (d1 + du1) * x1 + (d2 + du2) * x2 + (d3 + du3) * x3) +
      ((d0 - dv0) * y0 + (d1 - dv1) * y1 + (d2 - dv2) * y2 + (d3 - dv3) * y3) =
      d0 * c0 + d1 * c1 + d2 * c2 + d3 * c3 := by
    grind
  omega

theorem if_nat_coe (c : Nat → Bool) (x : Nat) (q : Nat) :
    Int.ofNat (if c q then x else 0) = if c q then Int.ofNat x else 0 := by
  split <;> rfl

theorem prefSum_zero (l : List Nat) : prefSum l 0 = 0 := by
  cases l <;> rfl

theorem prefSum_getD1 (l : List Nat) : prefSum l 1 = l.getD 0 0 := by
  rcases l with _ | ⟨a, tl⟩
  · rfl
  · simp [prefSum, prefSum_zero, List.getD]

theorem prefSum_getD2 (l : List Nat) : prefSum l 2 = l.getD 0 0 + l.getD 1 0 := by
  rcases l with _ | ⟨a, _ | ⟨b, tl⟩⟩ <;> simp [prefSum, prefSum_zero, List.getD]

theorem prefSum_getD3 (l : List Nat) :
    prefSum l 3 = l.getD 0 0 + l.getD 1 0 + l.getD 2 0 := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩ <;>
    simp [prefSum, prefSum_zero, List.getD] <;> omega

theorem prefSum_getD4 (l : List Nat) :
    prefSum l 4 = l.getD 0 0 + l.getD 1 0 + l.getD 2 0 + l.getD 3 0 := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tl⟩⟩⟩⟩ <;>
    simp [prefSum, prefSum_zero, List.getD] <;> omega

theorem int_ofNat_eq_coe (n : Nat) : Int.ofNat n = (n : Int) := rfl

theorem zLenNat_coe (spec : Nat × Nat) (t : Nat) :
    Int.ofNat (zLenNat spec t) = Int.ofNat spec.1 + Int.ofNat spec.2 * Int.ofNat t := by
  simp only [zLenNat, int_ofNat_eq_coe, Int.natCast_add, Int.natCast_mul]

theorem lenRowOf_lt4_0 {tidx : Nat} (h : tidx < 4) : lenRowOf tidx 0 = 0 := by simp [lenRowOf, h]
theorem lenRowOf_lt4_1 {tidx : Nat} (h : tidx < 4) : lenRowOf tidx 1 = 1 := by simp [lenRowOf, h]
theorem lenRowOf_lt4_2 {tidx : Nat} (h : tidx < 4) : lenRowOf tidx 2 = 2 := by simp [lenRowOf, h]
theorem lenRowOf_lt4_3 {tidx : Nat} (h : tidx < 4) : lenRowOf tidx 3 = 3 := by simp [lenRowOf, h]
theorem lenRowOf_lt4_4 {tidx : Nat} (h : tidx < 4) : lenRowOf tidx 4 = 0 := by simp [lenRowOf, h]

theorem lenRowOf_ge4 {tidx j : Nat} (h : ¬ tidx < 4) : lenRowOf tidx j = j := by
  simp [lenRowOf, h]

theorem oBeforeOf_lt4 {tidx j : Nat} (h : tidx < 4) : oBeforeOf tidx j = j := by
  simp [oBeforeOf, h]

theorem oBeforeOf_ge4_0 {tidx : Nat} (h : ¬ tidx < 4) : oBeforeOf tidx 0 = 1 := by simp [oBeforeOf, h]
theorem oBeforeOf_ge4_1 {tidx : Nat} (h : ¬ tidx < 4) : oBeforeOf tidx 1 = 2 := by simp [oBeforeOf, h]
theorem oBeforeOf_ge4_2 {tidx : Nat} (h : ¬ tidx < 4) : oBeforeOf tidx 2 = 3 := by simp [oBeforeOf, h]
theorem oBeforeOf_ge4_3 {tidx : Nat} (h : ¬ tidx < 4) : oBeforeOf tidx 3 = 4 := by simp [oBeforeOf, h]

theorem template_not_square (tidx z2 z1 t : Nat) (ht : tidx < 12)
    (hsumz : tidx < 4 → z2 + z1 = zLenNat ((templateZSpecs tidx).getD 0 (0, 0)) t) :
    ¬ IsShuffleSquare (render (templateBlocks tidx z2 z1 t)) := by
  rintro ⟨u, hsq⟩
  have hct_sum := IsShuffleSplit_countTrue hsq
  have hct_total : countTrue (render (templateBlocks tidx z2 z1 t)) = 12 := by
    rcases (by omega : tidx = 0 ∨ tidx = 1 ∨ tidx = 2 ∨ tidx = 3 ∨ tidx = 4 ∨ tidx = 5 ∨
        tidx = 6 ∨ tidx = 7 ∨ tidx = 8 ∨ tidx = 9 ∨ tidx = 10 ∨ tidx = 11) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [templateBlocks, templateOLens, countTrue_render, sumList]
  have hcu6 : countTrue u = 6 := by omega
  obtain ⟨ks, xs, ys, hm, hsumks, hgu, hgv⟩ := split_render _ u u hsq 0 0
  have hks6 : sumList ks = 6 := by omega
  let ol := templateOLens tidx
  let zs := templateZSpecs tidx
  by_cases hzcut : tidx < 4
  · have hlenz := hsumz hzcut
    simp only [templateBlocks, hzcut, ↓reduceIte] at hm hgu hgv
    obtain ⟨k0, k1, k2, k3, x0, x1, x2, x3, x4, y0, y1, y2, y3, y4,
      rfl, rfl, rfl, hk0, hk1, hk2, hk3, hx0, hx1, hx2, hx3, hx4⟩ := matches_ZCut hm
    have hL4 : ol.length = 4 := template_len4 tidx (List.mem_range.mpr hzcut)
    have hS4 : ol.getD 0 0 + ol.getD 1 0 + ol.getD 2 0 + ol.getD 3 0 = 12 :=
      template_sum4 tidx (List.mem_range.mpr hzcut)
    have hb := boundedList_getD4 hL4 hk0 hk1 hk2 hk3
    obtain ⟨code, hdual⟩ := exists_dual_template tidx ht [k0, k1, k2, k3] hb hks6
    simp only [checkDualFast, Bool.and_eq_true, decide_eq_true_eq, hzcut, ↓reduceIte] at hdual
    obtain ⟨⟨⟨hat, hrhs⟩, hokX⟩, hokY⟩ := hdual
    have hx_all := forall_range_of_all 5 _ hokX
    have hy_all := forall_range_of_all 5 _ hokY
    have hax0 := hx_all 0 (by omega)
    have hax1 := hx_all 1 (by omega)
    have hax2 := hx_all 2 (by omega)
    have hax3 := hx_all 3 (by omega)
    have hax4 := hx_all 4 (by omega)
    have hay0 := hy_all 0 (by omega)
    have hay1 := hy_all 1 (by omega)
    have hay2 := hy_all 2 (by omega)
    have hay3 := hy_all 3 (by omega)
    have hay4 := hy_all 4 (by omega)
    simp only [lenRowOf_lt4_0 hzcut, lenRowOf_lt4_1 hzcut, lenRowOf_lt4_2 hzcut,
      lenRowOf_lt4_3 hzcut, lenRowOf_lt4_4 hzcut, oBeforeOf_lt4 hzcut,
      prefSum_zero, prefSum_getD1, prefSum_getD2, prefSum_getD3, prefSum_getD4, Nat.sub_zero,
      decide_eq_true_eq] at hax0 hax1 hax2 hax3 hax4 hay0 hay1 hay2 hay3 hay4
    simp only [sumList] at hks6
    let d := unpackD code
    let ur0 := 0
    let ur1 := k0
    let ur2 := k0 + k1
    let ur3 := k0 + k1 + k2
    let ur4 := k0 + k1 + k2 + k3
    let vr0 := 0
    let vr1 := ol.getD 0 0 - k0
    let vr2 := ol.getD 0 0 + ol.getD 1 0 - (k0 + k1)
    let vr3 := ol.getD 0 0 + ol.getD 1 0 + ol.getD 2 0 - (k0 + k1 + k2)
    let vr4 := ol.getD 0 0 + ol.getD 1 0 + ol.getD 2 0 + ol.getD 3 0 - (k0 + k1 + k2 + k3)
    have hax0' : 0 ≤ d 0 + d (4 + ur0) := by exact hax0
    have hax1' : 0 ≤ d 1 + d (4 + ur1) := by exact hax1
    have hax2' : 0 ≤ d 2 + d (4 + ur2) := by exact hax2
    have hax3' : 0 ≤ d 3 + d (4 + ur3) := by exact hax3
    have hax4' : 0 ≤ d 0 + d (4 + ur4) := by exact hax4
    have hay0' : 0 ≤ d 0 - d (4 + vr0) := by exact hay0
    have hay1' : 0 ≤ d 1 - d (4 + vr1) := by exact hay1
    have hay2' : 0 ≤ d 2 - d (4 + vr2) := by exact hay2
    have hay3' : 0 ≤ d 3 - d (4 + vr3) := by exact hay3
    have hay4' : 0 ≤ d 0 - d (4 + vr4) := by exact hay4
    have hat' : 0 ≤ -(d 0 * Int.ofNat (zs.getD 0 (0,0)).2 + d 1 * Int.ofNat (zs.getD 1 (0,0)).2 +
        d 2 * Int.ofNat (zs.getD 2 (0,0)).2 + d 3 * Int.ofNat (zs.getD 3 (0,0)).2) := by exact hat
    have hrhs' : d 0 * Int.ofNat (zs.getD 0 (0,0)).1 + d 1 * Int.ofNat (zs.getD 1 (0,0)).1 +
        d 2 * Int.ofNat (zs.getD 2 (0,0)).1 + d 3 * Int.ofNat (zs.getD 3 (0,0)).1 < 0 := by exact hrhs
    have hgap0 : ∀ q, q ≤ 6 → d (4 + q) * (Int.ofNat (gapU 0 q
        [(false, z2), (true, ol.getD 0 0), (false, zLenNat (zs.getD 1 (0,0)) t), (true, ol.getD 1 0),
         (false, zLenNat (zs.getD 2 (0,0)) t), (true, ol.getD 2 0), (false, zLenNat (zs.getD 3 (0,0)) t),
         (true, ol.getD 3 0), (false, z1)] [k0, k1, k2, k3] [x0, x1, x2, x3, x4]) -
      Int.ofNat (gapV 0 q
        [(false, z2), (true, ol.getD 0 0), (false, zLenNat (zs.getD 1 (0,0)) t), (true, ol.getD 1 0),
         (false, zLenNat (zs.getD 2 (0,0)) t), (true, ol.getD 2 0), (false, zLenNat (zs.getD 3 (0,0)) t),
         (true, ol.getD 3 0), (false, z1)] [k0, k1, k2, k3] [y0, y1, y2, y3, y4])) = 0 := by
      intro q _
      have hg : gapU 0 q
          [(false, z2), (true, ol.getD 0 0), (false, zLenNat (zs.getD 1 (0,0)) t), (true, ol.getD 1 0),
           (false, zLenNat (zs.getD 2 (0,0)) t), (true, ol.getD 2 0), (false, zLenNat (zs.getD 3 (0,0)) t),
           (true, ol.getD 3 0), (false, z1)] [k0, k1, k2, k3] [x0, x1, x2, x3, x4] =
        gapV 0 q
          [(false, z2), (true, ol.getD 0 0), (false, zLenNat (zs.getD 1 (0,0)) t), (true, ol.getD 1 0),
           (false, zLenNat (zs.getD 2 (0,0)) t), (true, ol.getD 2 0), (false, zLenNat (zs.getD 3 (0,0)) t),
           (true, ol.getD 3 0), (false, z1)] [k0, k1, k2, k3] [y0, y1, y2, y3, y4] :=
        (hgu q).symm.trans (hgv q)
      rw [hg, Int.sub_self, Int.mul_zero]
    have hsg := sum7_zero _ hgap0
    have hsg_eval : sum7 (fun q => d (4 + q) * (Int.ofNat (gapU 0 q
        [(false, z2), (true, ol.getD 0 0), (false, zLenNat (zs.getD 1 (0,0)) t), (true, ol.getD 1 0),
         (false, zLenNat (zs.getD 2 (0,0)) t), (true, ol.getD 2 0), (false, zLenNat (zs.getD 3 (0,0)) t),
         (true, ol.getD 3 0), (false, z1)] [k0, k1, k2, k3] [x0, x1, x2, x3, x4]) -
      Int.ofNat (gapV 0 q
        [(false, z2), (true, ol.getD 0 0), (false, zLenNat (zs.getD 1 (0,0)) t), (true, ol.getD 1 0),
         (false, zLenNat (zs.getD 2 (0,0)) t), (true, ol.getD 2 0), (false, zLenNat (zs.getD 3 (0,0)) t),
         (true, ol.getD 3 0), (false, z1)] [k0, k1, k2, k3] [y0, y1, y2, y3, y4]))) =
      (d (4 + ur0) * Int.ofNat x0 + d (4 + ur1) * Int.ofNat x1 + d (4 + ur2) * Int.ofNat x2 +
       d (4 + ur3) * Int.ofNat x3 + d (4 + ur4) * Int.ofNat x4) -
      (d (4 + vr0) * Int.ofNat y0 + d (4 + vr1) * Int.ofNat y1 + d (4 + vr2) * Int.ofNat y2 +
       d (4 + vr3) * Int.ofNat y3 + d (4 + vr4) * Int.ofNat y4) := by
      have ev1 : ol.getD 0 0 - k0 + (ol.getD 1 0 - k1) = vr2 := by dsimp [vr2]; omega
      have ev2 : ol.getD 0 0 - k0 + (ol.getD 1 0 - k1) + (ol.getD 2 0 - k2) = vr3 := by dsimp [vr3]; omega
      have ev3 : ol.getD 0 0 - k0 + (ol.getD 1 0 - k1) + (ol.getD 2 0 - k2) + (ol.getD 3 0 - k3) = vr4 := by
        dsimp [vr4]; omega
      have hite := sum7_ite5 ur0 ur1 ur2 ur3 ur4 vr0 vr1 vr2 vr3 vr4
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (fun q => d (4 + q)) (Int.ofNat x0) (Int.ofNat x1) (Int.ofNat x2) (Int.ofNat x3) (Int.ofNat x4)
        (Int.ofNat y0) (Int.ofNat y1) (Int.ofNat y2) (Int.ofNat y3) (Int.ofNat y4)
      rw [← hite]
      apply sum7_congr
      intro q _
      simp only [gapU, gapV, Nat.zero_add, Nat.add_zero]
      rw [ev1, ev2, ev3]
      simp only [Int.natCast_add, if_nat_coe]
      rfl
    have hgap_z : (d (4 + ur0) * Int.ofNat x0 + d (4 + ur1) * Int.ofNat x1 + d (4 + ur2) * Int.ofNat x2 +
        d (4 + ur3) * Int.ofNat x3 + d (4 + ur4) * Int.ofNat x4) -
        (d (4 + vr0) * Int.ofNat y0 + d (4 + vr1) * Int.ofNat y1 + d (4 + vr2) * Int.ofNat y2 +
         d (4 + vr3) * Int.ofNat y3 + d (4 + vr4) * Int.ofNat y4) = 0 := hsg_eval.symm.trans hsg
    have heq0 : Int.ofNat x0 + Int.ofNat y0 + Int.ofNat x4 + Int.ofNat y4 -
        (Int.ofNat (zs.getD 0 (0,0)).1 + Int.ofNat (zs.getD 0 (0,0)).2 * Int.ofNat t) = 0 := by
      have hm0 : Int.ofNat (x0 + y0 + x4 + y4) = Int.ofNat (zLenNat (zs.getD 0 (0,0)) t) := by
        rw [hx0, hx4, hlenz]
      rw [zLenNat_coe] at hm0; omega
    have heq1 : Int.ofNat x1 + Int.ofNat y1 -
        (Int.ofNat (zs.getD 1 (0,0)).1 + Int.ofNat (zs.getD 1 (0,0)).2 * Int.ofNat t) = 0 := by
      have hm1 : Int.ofNat (x1 + y1) = Int.ofNat (zLenNat (zs.getD 1 (0,0)) t) := by rw [hx1]
      rw [zLenNat_coe] at hm1; omega
    have heq2 : Int.ofNat x2 + Int.ofNat y2 -
        (Int.ofNat (zs.getD 2 (0,0)).1 + Int.ofNat (zs.getD 2 (0,0)).2 * Int.ofNat t) = 0 := by
      have hm2 : Int.ofNat (x2 + y2) = Int.ofNat (zLenNat (zs.getD 2 (0,0)) t) := by rw [hx2]
      rw [zLenNat_coe] at hm2; omega
    have heq3 : Int.ofNat x3 + Int.ofNat y3 -
        (Int.ofNat (zs.getD 3 (0,0)).1 + Int.ofNat (zs.getD 3 (0,0)).2 * Int.ofNat t) = 0 := by
      have hm3 : Int.ofNat (x3 + y3) = Int.ofNat (zLenNat (zs.getD 3 (0,0)) t) := by rw [hx3]
      rw [zLenNat_coe] at hm3; omega
    exact farkas_zcut_absurd
      (d 0) (d 1) (d 2) (d 3)
      (d (4 + ur0)) (d (4 + ur1)) (d (4 + ur2)) (d (4 + ur3)) (d (4 + ur4))
      (d (4 + vr0)) (d (4 + vr1)) (d (4 + vr2)) (d (4 + vr3)) (d (4 + vr4))
      (Int.ofNat (zs.getD 0 (0,0)).1) (Int.ofNat (zs.getD 1 (0,0)).1)
      (Int.ofNat (zs.getD 2 (0,0)).1) (Int.ofNat (zs.getD 3 (0,0)).1)
      (Int.ofNat (zs.getD 0 (0,0)).2) (Int.ofNat (zs.getD 1 (0,0)).2)
      (Int.ofNat (zs.getD 2 (0,0)).2) (Int.ofNat (zs.getD 3 (0,0)).2)
      (Int.ofNat t) (Int.ofNat x0) (Int.ofNat x1) (Int.ofNat x2) (Int.ofNat x3) (Int.ofNat x4)
      (Int.ofNat y0) (Int.ofNat y1) (Int.ofNat y2) (Int.ofNat y3) (Int.ofNat y4)
      (Int.natCast_nonneg t) (Int.natCast_nonneg x0) (Int.natCast_nonneg x1)
      (Int.natCast_nonneg x2) (Int.natCast_nonneg x3) (Int.natCast_nonneg x4)
      (Int.natCast_nonneg y0) (Int.natCast_nonneg y1) (Int.natCast_nonneg y2)
      (Int.natCast_nonneg y3) (Int.natCast_nonneg y4)
      hat' hrhs' hax0' hax1' hax2' hax3' hax4' hay0' hay1' hay2' hay3' hay4'
      heq0 heq1 heq2 heq3 hgap_z
  · have hge4 : tidx ≥ 4 := by omega
    simp only [templateBlocks, hzcut, ↓reduceIte] at hm hgu hgv
    obtain ⟨k0, k1, k2, k3, k4, x0, x1, x2, x3, y0, y1, y2, y3,
      rfl, rfl, rfl, hk0, hk1, hk2, hk3, hk4, hx0, hx1, hx2, hx3⟩ := matches_OCut hm
    have hL5 : ol.length = 5 := template_len5 tidx (List.mem_range.mpr ht) hge4
    have hS5 : ol.getD 0 0 + ol.getD 1 0 + ol.getD 2 0 + ol.getD 3 0 + ol.getD 4 0 = 12 :=
      template_sum5 tidx (List.mem_range.mpr ht) hge4
    have hb := boundedList_getD5 hL5 hk0 hk1 hk2 hk3 hk4
    obtain ⟨code, hdual⟩ := exists_dual_template tidx ht [k0, k1, k2, k3, k4] hb hks6
    simp only [checkDualFast, Bool.and_eq_true, decide_eq_true_eq, hzcut, ↓reduceIte] at hdual
    obtain ⟨⟨⟨hat, hrhs⟩, hokX⟩, hokY⟩ := hdual
    have hx_all := forall_range_of_all 4 _ hokX
    have hy_all := forall_range_of_all 4 _ hokY
    have hax0 := hx_all 0 (by omega)
    have hax1 := hx_all 1 (by omega)
    have hax2 := hx_all 2 (by omega)
    have hax3 := hx_all 3 (by omega)
    have hay0 := hy_all 0 (by omega)
    have hay1 := hy_all 1 (by omega)
    have hay2 := hy_all 2 (by omega)
    have hay3 := hy_all 3 (by omega)
    simp only [lenRowOf_ge4 hzcut, oBeforeOf_ge4_0 hzcut, oBeforeOf_ge4_1 hzcut,
      oBeforeOf_ge4_2 hzcut, oBeforeOf_ge4_3 hzcut,
      prefSum_getD1, prefSum_getD2, prefSum_getD3, prefSum_getD4,
      decide_eq_true_eq] at hax0 hax1 hax2 hax3 hay0 hay1 hay2 hay3
    simp only [sumList] at hks6
    let d := unpackD code
    let ur0 := k0
    let ur1 := k0 + k1
    let ur2 := k0 + k1 + k2
    let ur3 := k0 + k1 + k2 + k3
    let vr0 := ol.getD 0 0 - k0
    let vr1 := ol.getD 0 0 + ol.getD 1 0 - (k0 + k1)
    let vr2 := ol.getD 0 0 + ol.getD 1 0 + ol.getD 2 0 - (k0 + k1 + k2)
    let vr3 := ol.getD 0 0 + ol.getD 1 0 + ol.getD 2 0 + ol.getD 3 0 - (k0 + k1 + k2 + k3)
    have hax0' : 0 ≤ d 0 + d (4 + ur0) := by exact hax0
    have hax1' : 0 ≤ d 1 + d (4 + ur1) := by exact hax1
    have hax2' : 0 ≤ d 2 + d (4 + ur2) := by exact hax2
    have hax3' : 0 ≤ d 3 + d (4 + ur3) := by exact hax3
    have hay0' : 0 ≤ d 0 - d (4 + vr0) := by exact hay0
    have hay1' : 0 ≤ d 1 - d (4 + vr1) := by exact hay1
    have hay2' : 0 ≤ d 2 - d (4 + vr2) := by exact hay2
    have hay3' : 0 ≤ d 3 - d (4 + vr3) := by exact hay3
    have hat' : 0 ≤ -(d 0 * Int.ofNat (zs.getD 0 (0,0)).2 + d 1 * Int.ofNat (zs.getD 1 (0,0)).2 +
        d 2 * Int.ofNat (zs.getD 2 (0,0)).2 + d 3 * Int.ofNat (zs.getD 3 (0,0)).2) := by exact hat
    have hrhs' : d 0 * Int.ofNat (zs.getD 0 (0,0)).1 + d 1 * Int.ofNat (zs.getD 1 (0,0)).1 +
        d 2 * Int.ofNat (zs.getD 2 (0,0)).1 + d 3 * Int.ofNat (zs.getD 3 (0,0)).1 < 0 := by exact hrhs
    have hgap0 : ∀ q, q ≤ 6 → d (4 + q) * (Int.ofNat (gapU 0 q
        [(true, ol.getD 0 0), (false, zLenNat (zs.getD 0 (0,0)) t),
         (true, ol.getD 1 0), (false, zLenNat (zs.getD 1 (0,0)) t),
         (true, ol.getD 2 0), (false, zLenNat (zs.getD 2 (0,0)) t),
         (true, ol.getD 3 0), (false, zLenNat (zs.getD 3 (0,0)) t),
         (true, ol.getD 4 0)] [k0, k1, k2, k3, k4] [x0, x1, x2, x3]) -
      Int.ofNat (gapV 0 q
        [(true, ol.getD 0 0), (false, zLenNat (zs.getD 0 (0,0)) t),
         (true, ol.getD 1 0), (false, zLenNat (zs.getD 1 (0,0)) t),
         (true, ol.getD 2 0), (false, zLenNat (zs.getD 2 (0,0)) t),
         (true, ol.getD 3 0), (false, zLenNat (zs.getD 3 (0,0)) t),
         (true, ol.getD 4 0)] [k0, k1, k2, k3, k4] [y0, y1, y2, y3])) = 0 := by
      intro q _
      have hg : gapU 0 q
          [(true, ol.getD 0 0), (false, zLenNat (zs.getD 0 (0,0)) t),
           (true, ol.getD 1 0), (false, zLenNat (zs.getD 1 (0,0)) t),
           (true, ol.getD 2 0), (false, zLenNat (zs.getD 2 (0,0)) t),
           (true, ol.getD 3 0), (false, zLenNat (zs.getD 3 (0,0)) t),
           (true, ol.getD 4 0)] [k0, k1, k2, k3, k4] [x0, x1, x2, x3] =
        gapV 0 q
          [(true, ol.getD 0 0), (false, zLenNat (zs.getD 0 (0,0)) t),
           (true, ol.getD 1 0), (false, zLenNat (zs.getD 1 (0,0)) t),
           (true, ol.getD 2 0), (false, zLenNat (zs.getD 2 (0,0)) t),
           (true, ol.getD 3 0), (false, zLenNat (zs.getD 3 (0,0)) t),
           (true, ol.getD 4 0)] [k0, k1, k2, k3, k4] [y0, y1, y2, y3] :=
        (hgu q).symm.trans (hgv q)
      rw [hg, Int.sub_self, Int.mul_zero]
    have hsg := sum7_zero _ hgap0
    have hsg_eval : sum7 (fun q => d (4 + q) * (Int.ofNat (gapU 0 q
        [(true, ol.getD 0 0), (false, zLenNat (zs.getD 0 (0,0)) t),
         (true, ol.getD 1 0), (false, zLenNat (zs.getD 1 (0,0)) t),
         (true, ol.getD 2 0), (false, zLenNat (zs.getD 2 (0,0)) t),
         (true, ol.getD 3 0), (false, zLenNat (zs.getD 3 (0,0)) t),
         (true, ol.getD 4 0)] [k0, k1, k2, k3, k4] [x0, x1, x2, x3]) -
      Int.ofNat (gapV 0 q
        [(true, ol.getD 0 0), (false, zLenNat (zs.getD 0 (0,0)) t),
         (true, ol.getD 1 0), (false, zLenNat (zs.getD 1 (0,0)) t),
         (true, ol.getD 2 0), (false, zLenNat (zs.getD 2 (0,0)) t),
         (true, ol.getD 3 0), (false, zLenNat (zs.getD 3 (0,0)) t),
         (true, ol.getD 4 0)] [k0, k1, k2, k3, k4] [y0, y1, y2, y3]))) =
      (d (4 + ur0) * Int.ofNat x0 + d (4 + ur1) * Int.ofNat x1 +
       d (4 + ur2) * Int.ofNat x2 + d (4 + ur3) * Int.ofNat x3) -
      (d (4 + vr0) * Int.ofNat y0 + d (4 + vr1) * Int.ofNat y1 +
       d (4 + vr2) * Int.ofNat y2 + d (4 + vr3) * Int.ofNat y3) := by
      have ev1 : ol.getD 0 0 - k0 + (ol.getD 1 0 - k1) = vr1 := by dsimp [vr1]; omega
      have ev2 : ol.getD 0 0 - k0 + (ol.getD 1 0 - k1) + (ol.getD 2 0 - k2) = vr2 := by dsimp [vr2]; omega
      have ev3 : ol.getD 0 0 - k0 + (ol.getD 1 0 - k1) + (ol.getD 2 0 - k2) + (ol.getD 3 0 - k3) = vr3 := by
        dsimp [vr3]; omega
      have hite := sum7_ite4 ur0 ur1 ur2 ur3 vr0 vr1 vr2 vr3
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
        (fun q => d (4 + q)) (Int.ofNat x0) (Int.ofNat x1) (Int.ofNat x2) (Int.ofNat x3)
        (Int.ofNat y0) (Int.ofNat y1) (Int.ofNat y2) (Int.ofNat y3)
      rw [← hite]
      apply sum7_congr
      intro q _
      simp only [gapU, gapV, Nat.zero_add, Nat.add_zero]
      rw [ev1, ev2, ev3]
      simp only [Int.natCast_add, if_nat_coe]
      rfl
    have hgap_o : (d (4 + ur0) * Int.ofNat x0 + d (4 + ur1) * Int.ofNat x1 +
        d (4 + ur2) * Int.ofNat x2 + d (4 + ur3) * Int.ofNat x3) -
        (d (4 + vr0) * Int.ofNat y0 + d (4 + vr1) * Int.ofNat y1 +
         d (4 + vr2) * Int.ofNat y2 + d (4 + vr3) * Int.ofNat y3) = 0 := hsg_eval.symm.trans hsg
    have heq0 : Int.ofNat x0 + Int.ofNat y0 -
        (Int.ofNat (zs.getD 0 (0,0)).1 + Int.ofNat (zs.getD 0 (0,0)).2 * Int.ofNat t) = 0 := by
      have hm0 : Int.ofNat (x0 + y0) = Int.ofNat (zLenNat (zs.getD 0 (0,0)) t) := by rw [hx0]
      rw [zLenNat_coe] at hm0; omega
    have heq1 : Int.ofNat x1 + Int.ofNat y1 -
        (Int.ofNat (zs.getD 1 (0,0)).1 + Int.ofNat (zs.getD 1 (0,0)).2 * Int.ofNat t) = 0 := by
      have hm1 : Int.ofNat (x1 + y1) = Int.ofNat (zLenNat (zs.getD 1 (0,0)) t) := by rw [hx1]
      rw [zLenNat_coe] at hm1; omega
    have heq2 : Int.ofNat x2 + Int.ofNat y2 -
        (Int.ofNat (zs.getD 2 (0,0)).1 + Int.ofNat (zs.getD 2 (0,0)).2 * Int.ofNat t) = 0 := by
      have hm2 : Int.ofNat (x2 + y2) = Int.ofNat (zLenNat (zs.getD 2 (0,0)) t) := by rw [hx2]
      rw [zLenNat_coe] at hm2; omega
    have heq3 : Int.ofNat x3 + Int.ofNat y3 -
        (Int.ofNat (zs.getD 3 (0,0)).1 + Int.ofNat (zs.getD 3 (0,0)).2 * Int.ofNat t) = 0 := by
      have hm3 : Int.ofNat (x3 + y3) = Int.ofNat (zLenNat (zs.getD 3 (0,0)) t) := by rw [hx3]
      rw [zLenNat_coe] at hm3; omega
    exact farkas_ocut_absurd
      (d 0) (d 1) (d 2) (d 3)
      (d (4 + ur0)) (d (4 + ur1)) (d (4 + ur2)) (d (4 + ur3))
      (d (4 + vr0)) (d (4 + vr1)) (d (4 + vr2)) (d (4 + vr3))
      (Int.ofNat (zs.getD 0 (0,0)).1) (Int.ofNat (zs.getD 1 (0,0)).1)
      (Int.ofNat (zs.getD 2 (0,0)).1) (Int.ofNat (zs.getD 3 (0,0)).1)
      (Int.ofNat (zs.getD 0 (0,0)).2) (Int.ofNat (zs.getD 1 (0,0)).2)
      (Int.ofNat (zs.getD 2 (0,0)).2) (Int.ofNat (zs.getD 3 (0,0)).2)
      (Int.ofNat t) (Int.ofNat x0) (Int.ofNat x1) (Int.ofNat x2) (Int.ofNat x3)
      (Int.ofNat y0) (Int.ofNat y1) (Int.ofNat y2) (Int.ofNat y3)
      (Int.natCast_nonneg t) (Int.natCast_nonneg x0) (Int.natCast_nonneg x1)
      (Int.natCast_nonneg x2) (Int.natCast_nonneg x3)
      (Int.natCast_nonneg y0) (Int.natCast_nonneg y1) (Int.natCast_nonneg y2)
      (Int.natCast_nonneg y3)
      hat' hrhs' hax0' hax1' hax2' hax3' hay0' hay1' hay2' hay3'
      heq0 heq1 heq2 heq3 hgap_o

theorem rotate_split_block_exact (l1 l2 : List Bool) (L len1 sufLen preLen : Nat)
    (b : Bool) (s : Nat) (hlen1 : l1.length = len1) (hlo : len1 ≤ s) (hhi : s ≤ len1 + L)
    (hsuf : sufLen = len1 + L - s) (hpre : preLen = s - len1) :
    rotate (l1 ++ List.replicate L b ++ l2) s =
      List.replicate sufLen b ++ l2 ++ l1 ++ List.replicate preLen b := by
  have hlo' : l1.length ≤ s := by omega
  have hhi' : s ≤ l1.length + L := by omega
  have hrot := rotate_split_block l1 l2 L b s hlo' hhi'
  have hs' : l1.length + L - s = sufLen := by omega
  have hp' : s - l1.length = preLen := by omega
  rwa [hs', hp'] at hrot

theorem rotate_W_matches (t s : Nat) (hs : s < (W t).length) :
    ∃ tidx z2 z1, tidx < 12 ∧
      (tidx < 4 → z2 + z1 = zLenNat ((templateZSpecs tidx).getD 0 (0,0)) t) ∧
      rotate (W t) s = render (templateBlocks tidx z2 z1 t) := by
  have hslen : s < 24 + 2 * t := by
    rw [length_W] at hs; omega
  by_cases h0 : s ≤ 5 + t
  · refine ⟨0, 5 + t - s, s, by omega, ?_, ?_⟩
    · intro _; simp [templateZSpecs, zLenNat]; omega
    · have hrot := rotate_split_block_exact []
        (List.replicate 1 true ++ List.replicate 2 false ++ List.replicate 4 true ++
         List.replicate (4 + t) false ++ List.replicate 3 true ++ List.replicate 1 false ++
         List.replicate 4 true)
        (5 + t) 0 (5 + t - s) s false s
        rfl (by omega) (by omega) (by omega) (by omega)
      simpa [W, templateBlocks, templateZSpecs, templateOLens, zLenNat, render,
        List.append_assoc] using hrot
  · by_cases h1 : s < 6 + t
    · omega
    · by_cases h2 : s ≤ 8 + t
      · refine ⟨1, 8 + t - s, s - (6 + t), by omega, ?_, ?_⟩
        · intro _; simp [templateZSpecs, zLenNat]; omega
        · have hrot := rotate_split_block_exact
            (List.replicate (5 + t) false ++ List.replicate 1 true)
            (List.replicate 4 true ++ List.replicate (4 + t) false ++ List.replicate 3 true ++
             List.replicate 1 false ++ List.replicate 4 true)
            2 (6 + t) (8 + t - s) (s - (6 + t)) false s
            (by simp [List.length_append, List.length_replicate]; omega) (by omega) (by omega) (by omega) (by omega)
          simpa [W, templateBlocks, templateZSpecs, templateOLens, zLenNat, render,
            List.append_assoc] using hrot
      · by_cases h3 : s ≤ 11 + t
        · have h12 : s = 9 + t ∨ s = 10 + t ∨ s = 11 + t := by omega
          rcases h12 with rfl | rfl | rfl
          · refine ⟨4, 0, 0, by omega, by omega, ?_⟩
            have hrot := rotate_split_block_exact
              (List.replicate (5 + t) false ++ List.replicate 1 true ++ List.replicate 2 false)
              (List.replicate (4 + t) false ++ List.replicate 3 true ++ List.replicate 1 false ++
               List.replicate 4 true)
              4 (8 + t) 3 1 true (9 + t)
              (by simp [List.length_append, List.length_replicate]; omega)
              (by omega) (by omega) (by omega) (by omega)
            simpa [W, templateBlocks, templateZSpecs, templateOLens, zLenNat, render,
              List.append_assoc] using hrot
          · refine ⟨5, 0, 0, by omega, by omega, ?_⟩
            have hrot := rotate_split_block_exact
              (List.replicate (5 + t) false ++ List.replicate 1 true ++ List.replicate 2 false)
              (List.replicate (4 + t) false ++ List.replicate 3 true ++ List.replicate 1 false ++
               List.replicate 4 true)
              4 (8 + t) 2 2 true (10 + t)
              (by simp [List.length_append, List.length_replicate]; omega)
              (by omega) (by omega) (by omega) (by omega)
            simpa [W, templateBlocks, templateZSpecs, templateOLens, zLenNat, render,
              List.append_assoc] using hrot
          · refine ⟨6, 0, 0, by omega, by omega, ?_⟩
            have hrot := rotate_split_block_exact
              (List.replicate (5 + t) false ++ List.replicate 1 true ++ List.replicate 2 false)
              (List.replicate (4 + t) false ++ List.replicate 3 true ++ List.replicate 1 false ++
               List.replicate 4 true)
              4 (8 + t) 1 3 true (11 + t)
              (by simp [List.length_append, List.length_replicate]; omega)
              (by omega) (by omega) (by omega) (by omega)
            simpa [W, templateBlocks, templateZSpecs, templateOLens, zLenNat, render,
              List.append_assoc] using hrot
        · by_cases h4 : s ≤ 16 + 2 * t
          · refine ⟨2, 16 + 2 * t - s, s - (12 + t), by omega, ?_, ?_⟩
            · intro _; simp [templateZSpecs, zLenNat]; omega
            · have hrot := rotate_split_block_exact
                (List.replicate (5 + t) false ++ List.replicate 1 true ++ List.replicate 2 false ++
                 List.replicate 4 true)
                (List.replicate 3 true ++ List.replicate 1 false ++ List.replicate 4 true)
                (4 + t) (12 + t) (16 + 2 * t - s) (s - (12 + t)) false s
                (by simp [List.length_append, List.length_replicate]; omega)
                (by omega) (by omega) (by omega) (by omega)
              simpa [W, templateBlocks, templateZSpecs, templateOLens, zLenNat, render,
                List.append_assoc] using hrot
          · by_cases h5 : s ≤ 18 + 2 * t
            · have h52 : s = 17 + 2 * t ∨ s = 18 + 2 * t := by omega
              rcases h52 with rfl | rfl
              · refine ⟨7, 0, 0, by omega, by omega, ?_⟩
                have hrot := rotate_split_block_exact
                  (List.replicate (5 + t) false ++ List.replicate 1 true ++ List.replicate 2 false ++
                   List.replicate 4 true ++ List.replicate (4 + t) false)
                  (List.replicate 1 false ++ List.replicate 4 true)
                  3 (16 + 2 * t) 2 1 true (17 + 2 * t)
                  (by simp [List.length_append, List.length_replicate]; omega)
                  (by omega) (by omega) (by omega) (by omega)
                simpa [W, templateBlocks, templateZSpecs, templateOLens, zLenNat, render,
                  List.append_assoc] using hrot
              · refine ⟨8, 0, 0, by omega, by omega, ?_⟩
                have hrot := rotate_split_block_exact
                  (List.replicate (5 + t) false ++ List.replicate 1 true ++ List.replicate 2 false ++
                   List.replicate 4 true ++ List.replicate (4 + t) false)
                  (List.replicate 1 false ++ List.replicate 4 true)
                  3 (16 + 2 * t) 1 2 true (18 + 2 * t)
                  (by simp [List.length_append, List.length_replicate]; omega)
                  (by omega) (by omega) (by omega) (by omega)
                simpa [W, templateBlocks, templateZSpecs, templateOLens, zLenNat, render,
                  List.append_assoc] using hrot
            · by_cases h6 : s ≤ 20 + 2 * t
              · refine ⟨3, 20 + 2 * t - s, s - (19 + 2 * t), by omega, ?_, ?_⟩
                · intro _; simp [templateZSpecs, zLenNat]; omega
                · have hrot := rotate_split_block_exact
                    (List.replicate (5 + t) false ++ List.replicate 1 true ++ List.replicate 2 false ++
                     List.replicate 4 true ++ List.replicate (4 + t) false ++ List.replicate 3 true)
                    (List.replicate 4 true)
                    1 (19 + 2 * t) (20 + 2 * t - s) (s - (19 + 2 * t)) false s
                    (by simp [List.length_append, List.length_replicate]; omega)
                    (by omega) (by omega) (by omega) (by omega)
                  simpa [W, templateBlocks, templateZSpecs, templateOLens, zLenNat, render,
                    List.append_assoc] using hrot
              · have h72 : s = 21 + 2 * t ∨ s = 22 + 2 * t ∨ s = 23 + 2 * t := by omega
                rcases h72 with rfl | rfl | rfl
                · refine ⟨9, 0, 0, by omega, by omega, ?_⟩
                  have hrot := rotate_split_block_exact
                    (List.replicate (5 + t) false ++ List.replicate 1 true ++ List.replicate 2 false ++
                     List.replicate 4 true ++ List.replicate (4 + t) false ++ List.replicate 3 true ++
                     List.replicate 1 false)
                    [] 4 (20 + 2 * t) 3 1 true (21 + 2 * t)
                    (by simp [List.length_append, List.length_replicate]; omega)
                    (by omega) (by omega) (by omega) (by omega)
                  simpa [W, templateBlocks, templateZSpecs, templateOLens, zLenNat, render,
                    List.append_assoc] using hrot
                · refine ⟨10, 0, 0, by omega, by omega, ?_⟩
                  have hrot := rotate_split_block_exact
                    (List.replicate (5 + t) false ++ List.replicate 1 true ++ List.replicate 2 false ++
                     List.replicate 4 true ++ List.replicate (4 + t) false ++ List.replicate 3 true ++
                     List.replicate 1 false)
                    [] 4 (20 + 2 * t) 2 2 true (22 + 2 * t)
                    (by simp [List.length_append, List.length_replicate]; omega)
                    (by omega) (by omega) (by omega) (by omega)
                  simpa [W, templateBlocks, templateZSpecs, templateOLens, zLenNat, render,
                    List.append_assoc] using hrot
                · refine ⟨11, 0, 0, by omega, by omega, ?_⟩
                  have hrot := rotate_split_block_exact
                    (List.replicate (5 + t) false ++ List.replicate 1 true ++ List.replicate 2 false ++
                     List.replicate 4 true ++ List.replicate (4 + t) false ++ List.replicate 3 true ++
                     List.replicate 1 false)
                    [] 4 (20 + 2 * t) 1 3 true (23 + 2 * t)
                    (by simp [List.length_append, List.length_replicate]; omega)
                    (by omega) (by omega) (by omega) (by omega)
                  simpa [W, templateBlocks, templateZSpecs, templateOLens, zLenNat, render,
                    List.append_assoc] using hrot

/-- Complete resolution of arXiv:2308.13882v2 Conjecture 1: for every n >= 12,
    there exists an even binary shuffle anti-square W(n - 12) of length 2n. -/
theorem grytczuk_conjecture_1_true (n : Nat) (hn : n ≥ 12) :
    (W (n - 12)).length = 2 * n ∧
    (W (n - 12)).count true = 12 ∧
    (W (n - 12)).count false = 2 * n - 12 ∧
    IsShuffleAntiSquare (W (n - 12)) := by
  have hlen : (W (n - 12)).length = 2 * n := by
    rw [length_W]; omega
  refine ⟨hlen, count_true_W (n - 12), ?_, ?_⟩
  · rw [count_false_W]; omega
  · intro s hs
    obtain ⟨tidx, z2, z1, ht, hsumz, hrot⟩ := rotate_W_matches (n - 12) s hs
    rw [hrot]
    exact template_not_square tidx z2 z1 (n - 12) ht hsumz

end ShuffleAntiSquares

#print axioms ShuffleAntiSquares.grytczuk_conjecture_1_true
