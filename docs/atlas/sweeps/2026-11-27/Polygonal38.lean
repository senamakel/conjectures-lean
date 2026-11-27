import FormalConjectures.OEIS.«255916»

/-! The square-completion criterion for the omitted pair (4, 38). -/

namespace Polygonal38

private theorem g7_twice (x : ℤ) :
    2 * (Nat.generalizedPolygonalNumber 7 x : ℤ) = 5 * x ^ 2 - 3 * x := by
  have hnonneg : 0 ≤ 5 * x ^ 2 - 3 * x := by
    by_cases hx : x ≤ 0
    · nlinarith [sq_nonneg x]
    · have hx' : 0 ≤ x - 1 := by omega
      have hp := mul_nonneg (show 0 ≤ x by omega) hx'
      nlinarith [sq_nonneg x]
  have hpar : (5 * x ^ 2 - 3 * x) % 2 = 0 := by
    have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
    obtain h | h := hx <;> simp [Int.sub_emod, pow_two, Int.mul_emod, h]
  have hcast := Int.toNat_of_nonneg (show 0 ≤ (5 * x ^ 2 - 3 * x) / 2 by omega)
  simp only [Nat.generalizedPolygonalNumber, Nat.reduceLeDiff, Nat.cast_ofNat,
    if_true]
  norm_num
  omega

private theorem p38_twice (z : ℕ) :
    2 * (Nat.polygonalNumber 38 z : ℤ) = 36 * (z : ℤ) ^ 2 - 34 * z := by
  cases z with
  | zero => norm_num [Nat.polygonalNumber]
  | succ k =>
    have hd : 36 * (k + 1) * k = 2 * (18 * (k + 1) * k) := by ring
    change 2 * (((36 * (k + 1) * k) / 2 + (k + 1) : ℕ) : ℤ) =
      36 * ((k + 1 : ℕ) : ℤ) ^ 2 - 34 * ((k + 1 : ℕ) : ℤ)
    simp [hd]
    ring

private theorem p4_square (y : ℕ) : Nat.polygonalNumber 4 y = y ^ 2 := by
  cases y with
  | zero => decide
  | succ k =>
    simp [Nat.polygonalNumber, mul_assoc]
    ring

theorem iffQuadratic (n : ℕ) :
    OeisA255916.IsSumOfGmPjPk 7 n 4 38 ↔
      ∃ a b : ℤ, ∃ c : ℕ,
        a % 10 = 7 ∧ b % 36 = 19 ∧ -17 ≤ b ∧
          9 * a ^ 2 + 5 * b ^ 2 + 360 * (c : ℤ) ^ 2 = 360 * (n : ℤ) + 1526 := by
  constructor
  · rintro ⟨x, y, z, h⟩
    refine ⟨10 * x - 3, 36 * z - 17, y, by omega, by omega, by omega, ?_⟩
    rw [p4_square] at h
    have hc : (Nat.generalizedPolygonalNumber 7 x : ℤ) + (y : ℤ) ^ 2
      + Nat.polygonalNumber 38 z = n := by exact_mod_cast h
    linear_combination 360 * hc - 180 * g7_twice x - 180 * p38_twice z
  · rintro ⟨a, b, y, ha, hb, hb0, h⟩
    let x := (a + 3) / 10
    let z := ((b + 17) / 36).toNat
    have hx : a = 10 * x - 3 := by dsimp [x]; omega
    have hz : b = 36 * (z : ℤ) - 17 := by
      have hpos : 0 ≤ (b + 17) / 36 := by omega
      dsimp [z]
      rw [Int.toNat_of_nonneg hpos]
      omega
    rw [hx, hz] at h
    refine ⟨x, y, z, ?_⟩
    rw [p4_square]
    have hc : (Nat.generalizedPolygonalNumber 7 x : ℤ) + (y : ℤ) ^ 2
      + Nat.polygonalNumber 38 z = n := by
      have hmul : 360 * ((Nat.generalizedPolygonalNumber 7 x : ℤ) + (y : ℤ) ^ 2
        + Nat.polygonalNumber 38 z) = 360 * n := by
        linear_combination h + 180 * g7_twice x + 180 * p38_twice z
      omega
    exact_mod_cast hc

set_option maxRecDepth 4000 in
theorem refutesClassification_of_quadratic
    (h : ∀ n : ℕ, ∃ a b : ℤ, ∃ c : ℕ,
      a % 10 = 7 ∧ b % 36 = 19 ∧ -17 ≤ b ∧
        9 * a ^ 2 + 5 * b ^ 2 + 360 * (c : ℤ) ^ 2 = 360 * (n : ℤ) + 1526) :
    ¬ (∀ j k : ℕ, 3 ≤ j ∧ j ≤ k →
      ((∀ n : ℕ, OeisA255916.IsSumOfGmPjPk 7 n j k) ↔
        (j, k) ∈ OeisA255916.sunPolygonalPairsSet1)) := by
  intro classify
  have omitted : (4, 38) ∉ OeisA255916.sunPolygonalPairsSet1 := by decide
  exact omitted ((classify 4 38 (by decide)).mp fun n => (iffQuadratic n).mpr (h n))

#print axioms iffQuadratic
#print axioms refutesClassification_of_quadratic

end Polygonal38
