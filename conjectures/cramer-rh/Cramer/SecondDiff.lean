import Mathlib

/-!
# Second differences of `t^{ρ+1} / (ρ(ρ+1))` on the critical line

For `Re ρ = 1/2`, `a > 0`, `h ≥ 0` and `D = ((a+2h)^{ρ+1} − 2(a+h)^{ρ+1} + a^{ρ+1}) / (ρ(ρ+1))`:

* `‖D‖ ≤ h² / √a` (two mean-value steps; `(d/dt)² t^{ρ+1}/(ρ(ρ+1)) = t^{ρ−1}`, of size `t^{−1/2}`);
* `‖D‖ ≤ 4 (a+2h)^{3/2} / ‖ρ(ρ+1)‖` (triangle inequality).
-/

namespace Cramer

open Complex Set

/-- `g(t) = t^{ρ+1} / (ρ+1) / ρ`. -/
noncomputable def gρ (ρ : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ (ρ + 1) / (ρ + 1) / ρ

/-- `g'(t) = t^ρ / ρ`. -/
noncomputable def gρ' (ρ : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ ρ / ρ

lemma hasDerivAt_gρ {ρ : ℂ} (hρ1 : ρ ≠ -1) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (gρ ρ) (gρ' ρ t) t :=
  (hasDerivAt_ofReal_cpow_const' ht hρ1).div_const ρ

lemma hasDerivAt_gρ' {ρ : ℂ} (hρ0 : ρ ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (gρ' ρ) ((t : ℂ) ^ (ρ - 1)) t := by
  have h := hasDerivAt_ofReal_cpow_const' ht (r := ρ - 1) (by
    intro h; apply hρ0; linear_combination h)
  simp only [sub_add_cancel] at h
  exact h

lemma norm_cpow_sub_one_le {ρ : ℂ} (hρ : ρ.re = 1 / 2) {p t : ℝ} (hp : 0 < p) (hpt : p ≤ t) :
    ‖(t : ℂ) ^ (ρ - 1)‖ ≤ p ^ (-(1 / 2 : ℝ)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp only [sub_re, one_re, hρ]
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
  exact Real.rpow_le_rpow_of_nonpos hp hpt (by norm_num)

/-- `‖g'(q) − g'(p)‖ ≤ p^{−1/2} (q − p)` for `0 < p ≤ q`. -/
lemma norm_gρ'_sub_le {ρ : ℂ} (hρ : ρ.re = 1 / 2) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    ‖gρ' ρ q - gρ' ρ p‖ ≤ p ^ (-(1 / 2 : ℝ)) * (q - p) := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hρ; norm_num at hρ
  refine norm_image_sub_le_of_norm_deriv_le_segment' (f' := fun t => (t : ℂ) ^ (ρ - 1))
    (fun t ht => (hasDerivAt_gρ' hρ0 (by linarith [ht.1])).hasDerivWithinAt)
    (fun t ht => norm_cpow_sub_one_le hρ hp ht.1) q ⟨hpq, le_rfl⟩

/-- The second difference, bound (b): `‖g(a+2h) − 2g(a+h) + g(a)‖ ≤ h² a^{−1/2}`. -/
theorem norm_second_diff_gρ_le {ρ : ℂ} (hρ : ρ.re = 1 / 2) {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) :
    ‖gρ ρ (a + 2 * h) - 2 * gρ ρ (a + h) + gρ ρ a‖ ≤ h ^ 2 * a ^ (-(1 / 2 : ℝ)) := by
  have hρ1 : ρ ≠ -1 := fun h => by rw [h] at hρ; norm_num at hρ
  set F : ℝ → ℂ := fun u => gρ ρ (a + h + u) - gρ ρ (a + u)
  have hF : ∀ u ∈ Icc (0 : ℝ) h,
      HasDerivWithinAt F (gρ' ρ (a + h + u) - gρ' ρ (a + u)) (Icc 0 h) u := by
    intro u hu
    have h1 := (hasDerivAt_gρ hρ1 (t := a + h + u) (by linarith [hu.1])).comp_const_add (a + h) u
    have h2 := (hasDerivAt_gρ hρ1 (t := a + u) (by linarith [hu.1])).comp_const_add a u
    exact (h1.sub h2).hasDerivWithinAt
  have hb : ∀ u ∈ Ico (0 : ℝ) h, ‖gρ' ρ (a + h + u) - gρ' ρ (a + u)‖ ≤ a ^ (-(1 / 2 : ℝ)) * h := by
    intro u hu
    have := norm_gρ'_sub_le hρ (p := a + u) (q := a + h + u) (by linarith [hu.1]) (by linarith)
    calc _ ≤ (a + u) ^ (-(1 / 2 : ℝ)) * (a + h + u - (a + u)) := this
      _ ≤ a ^ (-(1 / 2 : ℝ)) * h := by
        rw [show a + h + u - (a + u) = h by ring]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos ha (by linarith [hu.1]) (by norm_num)) hh
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hF hb h ⟨hh, le_rfl⟩
  have e : F h - F 0 = gρ ρ (a + 2 * h) - 2 * gρ ρ (a + h) + gρ ρ a := by
    simp only [F, add_zero]
    rw [show a + h + h = a + 2 * h by ring]
    ring
  rw [e] at key
  calc _ ≤ a ^ (-(1 / 2 : ℝ)) * h * (h - 0) := key
    _ = h ^ 2 * a ^ (-(1 / 2 : ℝ)) := by ring

/-- The second difference, bound (a): `‖Σ‖ ≤ 4 (a+2h)^{3/2} / ‖ρ(ρ+1)‖`. -/
theorem norm_second_diff_gρ_le' {ρ : ℂ} (hρ : ρ.re = 1 / 2) {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) :
    ‖gρ ρ (a + 2 * h) - 2 * gρ ρ (a + h) + gρ ρ a‖
      ≤ 4 * (a + 2 * h) ^ (3 / 2 : ℝ) / ‖ρ * (ρ + 1)‖ := by
  have hpow : ∀ t : ℝ, 0 < t → t ≤ a + 2 * h →
      ‖(t : ℂ) ^ (ρ + 1)‖ ≤ (a + 2 * h) ^ (3 / 2 : ℝ) := by
    intro t ht htb
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp only [add_re, one_re, hρ]
    rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num]
    exact Real.rpow_le_rpow ht.le htb (by norm_num)
  have e : gρ ρ (a + 2 * h) - 2 * gρ ρ (a + h) + gρ ρ a
      = (((a + 2 * h : ℝ) : ℂ) ^ (ρ + 1) - 2 * ((a + h : ℝ) : ℂ) ^ (ρ + 1)
          + ((a : ℝ) : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1)) := by
    simp only [gρ]
    rw [div_div, div_div, div_div, mul_comm (ρ + 1) ρ]
    ring
  rw [e, norm_div]
  gcongr
  calc _ ≤ ‖((a + 2 * h : ℝ) : ℂ) ^ (ρ + 1) - 2 * ((a + h : ℝ) : ℂ) ^ (ρ + 1)‖
        + ‖((a : ℝ) : ℂ) ^ (ρ + 1)‖ := norm_add_le _ _
    _ ≤ (‖((a + 2 * h : ℝ) : ℂ) ^ (ρ + 1)‖ + ‖2 * ((a + h : ℝ) : ℂ) ^ (ρ + 1)‖)
        + ‖((a : ℝ) : ℂ) ^ (ρ + 1)‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ((a + 2 * h) ^ (3 / 2 : ℝ) + 2 * (a + 2 * h) ^ (3 / 2 : ℝ)) + (a + 2 * h) ^ (3 / 2 : ℝ) := by
        rw [norm_mul, Complex.norm_two]
        gcongr
        · exact hpow _ (by linarith) le_rfl
        · exact hpow _ (by linarith) (by linarith)
        · exact hpow _ ha (by linarith)
    _ ≤ 4 * (a + 2 * h) ^ (3 / 2 : ℝ) := by
        have : 0 ≤ (a + 2 * h) ^ (3 / 2 : ℝ) := by positivity
        linarith

end Cramer
