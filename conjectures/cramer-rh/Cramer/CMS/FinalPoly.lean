import Mathlib

/-!
# The last inequality in `t = log x`
-/

namespace Cramer.CMS

/-- The bound on the main zero term. -/
noncomputable def Mb (t : ℝ) : ℝ :=
  (1 + 0.024 / t) / (0.055 * 3.141592 * t) *
    ((t / 2 - 2.88 + 1.063 + 0.05 / t) *
        (4252035564110250469740648 / (1099511627776 * 1048576) +
          0.0019 / t * (760852761666848834989 / (1048576 * 1048576))) +
      0.6931471808 / 4 * (463585232095674405339284 / (1099511627776 * 1048576) +
          0.0019 / t * (5587348473184294079485 / (1048576 * 1048576))) -
      0.6931471803 / 4 * (44601726036410213767724532 / (1099511627776 * 1048576)))

/-- The bound on Rosser's error term. -/
noncomputable def EVb (t : ℝ) : ℝ :=
  2 * (t + 7) * ((13182834354755211737 + 20625534903171 + 15568535259931704074) / 1099511627776 +
    0.0019 / t * ((72271341813760 + 639958350772 + 1207134689330252) / 1048576)) / (29 * t ^ 2)

/-- The bound on the tail. -/
noncomputable def Cb (t : ℝ) : ℝ :=
  2 * 740648 / 120 * ((1 + 0.024 / t) / (0.055 * 3.141592 * t)) * 1.005 *
    ((t / 2 + 5) + 0.31 * 3.141593)

/-- The bound on the Brun–Titchmarsh term. -/
noncomputable def BTb (t : ℝ) : ℝ :=
  18838744 * (t + 0.003) / (16 * t - 96)

/-- The bound on the prime powers. -/
noncomputable def PPt (t : ℝ) : ℝ :=
  131072 * (t + 0.003) * (128.1 / (29 * t ^ 2) + 148 / (3.3 * (t - 12) * t))

theorem final_poly {t : ℝ} (ht : 18 ≤ t) :
    Mb t + EVb t + Cb t + BTb t + PPt t + 11 < 11989718 := by
  have h0 : t ≠ 0 := by intro h; linarith
  have h1 : t - 12 ≠ 0 := by intro h; linarith
  have h2 : 16 * t - 96 ≠ 0 := by intro h; linarith
  have h1' : 0 < t - 12 := by linarith
  have h2' : 0 < 16 * t - 96 := by linarith
  have hR : BTb t < 11989718 - (Mb t + EVb t + Cb t + PPt t + 11) := by
    unfold BTb
    rw [div_lt_iff₀ h2']
    unfold Mb EVb Cb PPt
    rw [← sub_pos]
    have e : ∀ A : ℝ, 0 < A * (t ^ 4 * (t - 12)) → 0 < A := fun A hA =>
      pos_of_mul_pos_left hA (by positivity)
    apply e
    field_simp
    obtain ⟨v, hv, rfl⟩ : ∃ v, 0 ≤ v ∧ t = v + 18 := ⟨t - 18, by linarith, by ring⟩
    ring_nf
    nlinarith [pow_nonneg hv 2, pow_nonneg hv 3, pow_nonneg hv 4, pow_nonneg hv 5, pow_nonneg hv 6,
      pow_nonneg hv 7, pow_nonneg hv 8]
  linarith
end Cramer.CMS
