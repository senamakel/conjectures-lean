import Speiser.Band.Check
import Speiser.Band.Run
import Speiser.Statement

/-!
# `ζ'(s) ≠ 0` on the band `0 < σ < 1/2`, `5/2 ≤ |t| < 7` (no hypothesis)

`deriv_ne_zero_of_coverOK` turns a `true` answer of the bisection into the statement on the
box; `coverOK_upper` and `coverOK_lower` (`native_decide`) are the two answers.
-/

open Complex SpeiserCompute

namespace Speiser.Band

theorem deriv_ne_zero_of_coverOK (k : ℕ) : ∀ {s0 s1 t0 t1 : ℤ},
    coverOK s0 s1 t0 t1 k = true → ∀ {s : ℂ}, (s0 : ℝ) / δ ≤ s.re → s.re ≤ (s1 : ℝ) / δ →
      (t0 : ℝ) / δ ≤ s.im → s.im ≤ (t1 : ℝ) / δ → deriv riemannZeta s ≠ 0 := by
  induction k with
  | zero => intro s0 s1 t0 t1 h s h1 h2 h3 h4; exact deriv_ne_zero_of_cellOK h h1 h2 h3 h4
  | succ k ih =>
    intro s0 s1 t0 t1 h s h1 h2 h3 h4
    unfold coverOK at h
    rcases Bool.or_eq_true_iff.mp h with hc | hc
    · exact deriv_ne_zero_of_cellOK hc h1 h2 h3 h4
    · split_ifs at hc with hsplit
      · obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hc
        rcases le_total s.re ((((s0 + s1) / 2 : ℤ) : ℝ) / δ) with hm | hm
        · exact ih ha h1 hm h3 h4
        · exact ih hb hm h2 h3 h4
      · obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hc
        rcases le_total s.im ((((t0 + t1) / 2 : ℤ) : ℝ) / δ) with hm | hm
        · exact ih ha h1 h2 h3 hm
        · exact ih hb h1 h2 hm h4

lemma scaled (q : ℚ) (n : ℤ) (h : (n : ℝ) = (q : ℝ) * δ) : (n : ℝ) / δ = q := by
  rw [h, mul_div_assoc, div_self δ_pos.ne', mul_one]

/-- **`ζ'(s) ≠ 0` for `0 < σ < 1/2`, `5/2 ≤ |t| < 7`.** Unconditional. -/
theorem speiserBand : SpeiserBand (5 / 2) 7 := by
  intro s h0 h1 ha hb
  have hδ : δ = 2 ^ 64 := δ_eq
  have e0 : ((0 : ℤ) : ℝ) / δ = 0 := by simp
  have e1 : ((D / 2 : ℤ) : ℝ) / δ = 1 / 2 := by
    rw [show D / 2 = 2 ^ 63 by unfold D; norm_num, hδ]; norm_num
  rcases le_or_gt 0 s.im with hpos | hneg
  · rw [abs_of_nonneg hpos] at ha hb
    refine deriv_ne_zero_of_coverOK 40 coverOK_upper (by rw [e0]; exact h0.le)
      (by rw [e1]; exact h1.le) ?_ ?_
    · rw [show 5 * D / 2 = 5 * 2 ^ 63 by unfold D; norm_num, hδ]; push_cast; linarith
    · rw [show 7 * D = 7 * 2 ^ 64 by unfold D; norm_num, hδ]; push_cast; linarith
  · rw [abs_of_neg hneg] at ha hb
    refine deriv_ne_zero_of_coverOK 40 coverOK_lower (by rw [e0]; exact h0.le)
      (by rw [e1]; exact h1.le) ?_ ?_
    · rw [show -7 * D = -7 * 2 ^ 64 by unfold D; norm_num, hδ]; push_cast; linarith
    · rw [show -5 * D / 2 = -5 * 2 ^ 63 by unfold D; norm_num, hδ]; push_cast; linarith

end Speiser.Band
