/-
  Formal Algebraic Verification of Nathaniel Johnston's Conjecture (MathOverflow #476077)
  for m = 3, 4, 5 (all n >= m and all 1 <= k < m, arbitrary-sign real entries).
  Zero external dependencies (Lean 4.36.0 core Init only).

  Rescaling y_i = (m - 1) x_i, we have y_i <= 1, e_1 = m - 1, and e_k >= 0 (1 <= k <= m).
  Because S_{2,r} = sum y_i^2 (1 - y_i)^r >= 0 holds even for negative y_i <= 1,
  expressing S_{2,r} in terms of e_2, ..., e_m via Newton's identities gives exact
  polynomial identities over any commutative ring (verified here over Int, hence
  valid identically in Z[e_2, ..., e_m] and therefore over R).
-/

namespace JohnstonEsymmM345

-- Newton power sums p_k(e_1, ..., e_5)
def p1 (e1 : Int) : Int := e1
def p2 (e1 e2 : Int) : Int := e1 ^ 2 - 2 * e2
def p3 (e1 e2 e3 : Int) : Int := e1 ^ 3 - 3 * e1 * e2 + 3 * e3
def p4 (e1 e2 e3 e4 : Int) : Int :=
  e1 ^ 4 - 4 * e1 ^ 2 * e2 + 2 * e2 ^ 2 + 4 * e1 * e3 - 4 * e4
def p5 (e1 e2 e3 e4 e5 : Int) : Int :=
  e1 ^ 5 - 5 * e1 ^ 3 * e2 + 5 * e1 * e2 ^ 2 + 5 * e1 ^ 2 * e3
  - 5 * e2 * e3 - 5 * e1 * e4 + 5 * e5

def S21 (e1 e2 e3 : Int) : Int := p2 e1 e2 - p3 e1 e2 e3
def S22 (e1 e2 e3 e4 : Int) : Int := p2 e1 e2 - 2 * p3 e1 e2 e3 + p4 e1 e2 e3 e4
def S23 (e1 e2 e3 e4 e5 : Int) : Int :=
  p2 e1 e2 - 3 * p3 e1 e2 e3 + 3 * p4 e1 e2 e3 e4 - p5 e1 e2 e3 e4 e5

/-! ### Theorem 1: m = 3 (e_1 = 2) => e_2 >= 1 -/

theorem identity_m3_e2 (e2 e3 : Int) :
    4 * (e2 - 1) = 3 * e3 + S21 2 e2 e3 := by
  simp only [S21, p2, p3]
  omega

/-! ### Theorem 2: m = 4 (e_1 = 3) => e_2 >= 3 and e_3 >= 1 -/

theorem identity_m4_e2 (e2 e3 e4 : Int) :
    2 * e2 * (e2 - 3) = 4 * e4 + 2 * S21 3 e2 e3 + S22 3 e2 e3 e4 := by
  simp only [S21, S22, p2, p3, p4]
  grind

theorem identity_m4_e3 (e2 e3 e4 : Int) :
    6 * (e3 - 1) = S22 3 e2 e3 e4 + 4 * e4 + 2 * (e2 - 3) * (7 - e2) := by
  simp only [S22, p2, p3, p4]
  grind

/-! ### Theorem 3: m = 5 (e_1 = 4) => e_2 >= 6, e_3 >= 4, e_4 >= 1 -/

def E1_m5 (e2 e3 e4 e5 : Int) : Int :=
  2 * S22 4 e2 e3 e4 + S23 4 e2 e3 e4 e5

theorem identity_m5_e2 (e2 e3 e4 e5 : Int) :
    4 * (e2 - 6) * (5 * e2 - 24) =
    3 * E1_m5 e2 e3 e4 e5 + (5 * e2 - 21) * S21 4 e2 e3 + 15 * e5 := by
  simp only [E1_m5, S21, S22, S23, p2, p3, p4, p5]
  grind

theorem identity_m5_e3 (e2 e3 e4 e5 : Int) :
    (5 * e2 - 21) * (e3 - 4) =
    E1_m5 e2 e3 e4 e5 + 5 * e5 + 2 * (e2 - 6) * (5 * e2 - 19) := by
  simp only [E1_m5, S22, S23, p2, p3, p4, p5]
  grind

theorem identity_m5_e4 (e2 e3 e4 e5 : Int) :
    8 * (5 * e2 - 21) * (e4 - 1) =
    (5 * e2 - 21) * (S23 4 e2 e3 e4 e5 + 5 * e5) +
    (41 - 5 * e2) * (E1_m5 e2 e3 e4 e5 + 5 * e5) +
    4 * (e2 - 6) * (5 * e2 ^ 2 - 46 * e2 + 125) := by
  simp only [E1_m5, S22, S23, p2, p3, p4, p5]
  grind

/-- Positivity of the quadratic factor in Theorem 3 (m = 5, e_4 >= 1):
    5 * (5 * e2^2 - 46 * e2 + 125) = (5 * e2 - 23)^2 + 96 > 0. -/
theorem m5_quadratic_pos (e2 : Int) :
    5 * (5 * e2 ^ 2 - 46 * e2 + 125) = (5 * e2 - 23) ^ 2 + 96 := by
  grind

#print axioms identity_m3_e2
#print axioms identity_m4_e2
#print axioms identity_m4_e3
#print axioms identity_m5_e2
#print axioms identity_m5_e3
#print axioms identity_m5_e4
#print axioms m5_quadratic_pos

end JohnstonEsymmM345
