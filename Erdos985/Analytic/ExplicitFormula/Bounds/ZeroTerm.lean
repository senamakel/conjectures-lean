import Erdos985.Analytic.ExplicitFormula.Basic

/-!
# Bound for a single zero term

For `Re ρ = 1/2` and `x ≥ 1`:
`zeroTerm x ρ = 2/(ρ(2−ρ)) − (3/x)/((2−ρ)(1+ρ)) − x^ρ/(ρ(ρ+1))`, and `|2−ρ| = |ρ+1| ≥ |ρ|`.
-/

namespace Erdos985.Analytic.BoundsAux

open Complex

lemma zeroTerm_eq (x : ℕ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    zeroTerm x ρ = 2 / (ρ * (2 - ρ)) - (3 / (x : ℂ)) / ((2 - ρ) * (1 + ρ))
      - (x : ℂ) ^ ρ / (ρ * (ρ + 1)) := by
  have h0 : ρ ≠ 0 := fun h => by rw [h] at hρ; norm_num at hρ
  have h2 : (2 : ℂ) - ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hρ] at this; norm_num at this
  have h1 : (1 : ℂ) + ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hρ] at this; norm_num at this
  have h1' : ρ + 1 ≠ 0 := by rwa [add_comm]
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  unfold zeroTerm
  rw [cpow_neg_one]
  field_simp
  ring

lemma norm_two_sub_eq {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ‖(2 : ℂ) - ρ‖ = ‖ρ + 1‖ := by
  rw [← Complex.norm_conj (ρ + 1)]
  congr 1
  apply Complex.ext <;> norm_num [hρ]

lemma norm_le_norm_add_one {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ‖ρ‖ ≤ ‖ρ + 1‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  simp [Complex.normSq_apply, hρ]
  norm_num

end Erdos985.Analytic.BoundsAux

namespace Erdos985.Analytic

open Complex BoundsAux

theorem norm_zeroTerm_le' (x : ℕ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ‖zeroTerm x ρ‖ ≤ (√(x : ℝ) + 2 + 3 / x) / ‖ρ * (ρ + 1)‖ := by
  have h0 : ρ ≠ 0 := fun h => by rw [h] at hρ; norm_num at hρ
  have h1' : ρ + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hρ] at this; norm_num at this
  have hxr : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hP : 0 < ‖ρ * (ρ + 1)‖ := norm_pos_iff.mpr (mul_ne_zero h0 h1')
  have hn0 : 0 < ‖ρ‖ := norm_pos_iff.mpr h0
  have hn1 : 0 < ‖ρ + 1‖ := norm_pos_iff.mpr h1'
  have e2 := norm_two_sub_eq hρ
  have hle := norm_le_norm_add_one hρ
  rw [zeroTerm_eq x hx hρ]
  have t1 : ‖2 / (ρ * (2 - ρ))‖ = 2 / ‖ρ * (ρ + 1)‖ := by
    rw [norm_div, norm_mul, norm_mul, e2]; simp
  have t2 : ‖(3 / (x : ℂ)) / ((2 - ρ) * (1 + ρ))‖ ≤ (3 / x) / ‖ρ * (ρ + 1)‖ := by
    rw [norm_div, norm_mul, norm_mul, e2, add_comm 1 ρ, norm_div]
    simp only [Complex.norm_natCast, Complex.norm_ofNat]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right hle hn1.le
  have t3 : ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1))‖ = √(x : ℝ) / ‖ρ * (ρ + 1)‖ := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega), hρ, Real.sqrt_eq_rpow]
  calc _ ≤ ‖2 / (ρ * (2 - ρ)) - (3 / (x : ℂ)) / ((2 - ρ) * (1 + ρ))‖
          + ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1))‖ := norm_sub_le _ _
    _ ≤ ‖2 / (ρ * (2 - ρ))‖ + ‖(3 / (x : ℂ)) / ((2 - ρ) * (1 + ρ))‖
          + ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1))‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ 2 / ‖ρ * (ρ + 1)‖ + (3 / x) / ‖ρ * (ρ + 1)‖ + √(x : ℝ) / ‖ρ * (ρ + 1)‖ := by
          rw [t1, t3]; linarith
    _ = _ := by field_simp; ring

end Erdos985.Analytic
