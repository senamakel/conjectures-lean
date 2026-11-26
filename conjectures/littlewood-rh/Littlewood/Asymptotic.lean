import Mathlib

/-!
# Step 11: the choice `x = √(log t)` (real analysis only)

With `u = log t`, `ℓ = log u` and `x = √u` (so `log x = ℓ/2`), the bound of
`Littlewood.log_norm_zeta_le` is `3u/ℓ + O(√u ℓ)`, which is at most `4u/ℓ` once `u` is large.
The only analytic input is `log u ≤ u^{1/8}` for large `u`; then everything is a polynomial
inequality in `v = u^{1/8}`.
-/

open Filter Asymptotics

namespace Littlewood

lemma eventually_log_le_rpow : ∃ U : ℝ, ∀ u : ℝ, U ≤ u → Real.log u ≤ u ^ (1 / 8 : ℝ) := by
  have h := (isLittleO_log_rpow_atTop (r := 1 / 8) (by norm_num)).bound (c := 1) one_pos
  obtain ⟨U, hU⟩ := eventually_atTop.1 (h.and (eventually_gt_atTop 0))
  refine ⟨U, fun u hu => ?_⟩
  obtain ⟨h1, h2⟩ := hU u hu
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h2.le _)] at h1
  exact (le_abs_self _).trans h1

/-- The polynomial inequality in `v = u^{1/8}`. -/
lemma poly_le {A B S v : ℝ} (hv : |A| + 14 + 4 * |S| + 2 * |B| ≤ v) :
    |A| * v + 2 * v ^ 6 + 4 * v ^ 4 + 8 + 4 * |S| + 2 * |B| ≤ v ^ 8 := by
  have hv1 : 1 ≤ v := by linarith [abs_nonneg A, abs_nonneg S, abs_nonneg B]
  have p1 : v ≤ v ^ 7 := by simpa using pow_le_pow_right₀ hv1 (show 1 ≤ 7 by norm_num)
  have p6 : v ^ 6 ≤ v ^ 7 := pow_le_pow_right₀ hv1 (by norm_num)
  have p4 : v ^ 4 ≤ v ^ 7 := pow_le_pow_right₀ hv1 (by norm_num)
  have p0 : 1 ≤ v ^ 7 := one_le_pow₀ hv1
  have hA := abs_nonneg A
  have hS := abs_nonneg S
  have hB := abs_nonneg B
  have h8 : v ^ 8 = v * v ^ 7 := by ring
  have hsum : |A| * v + 2 * v ^ 6 + 4 * v ^ 4 + 8 + 4 * |S| + 2 * |B|
      ≤ (|A| + 14 + 4 * |S| + 2 * |B|) * v ^ 7 := by nlinarith
  rw [h8]
  calc _ ≤ (|A| + 14 + 4 * |S| + 2 * |B|) * v ^ 7 := hsum
    _ ≤ v * v ^ 7 := by gcongr

/-- **The choice of `x`.** -/
theorem exists_threshold (A B S : ℝ) :
    ∃ U : ℝ, Real.exp 4 ≤ U ∧ ∀ u : ℝ, U ≤ u → ∀ w : ℝ, w ≤ u + 2 →
      A + u / (2 * Real.log (Real.sqrt u)) +
        (2 * ((Real.sqrt u + 1) * Real.log (Real.sqrt u) ^ 2 + (Real.sqrt u + 1 + S)) + B + w) /
          Real.log (Real.sqrt u) ≤ 4 * u / Real.log u := by
  obtain ⟨U₁, hU₁⟩ := eventually_log_le_rpow
  set M := |A| + 14 + 4 * |S| + 2 * |B| with hM
  refine ⟨max (max U₁ (Real.exp 4)) (M ^ 8), le_trans (le_max_right _ _) (le_max_left _ _),
    fun u hu w hw => ?_⟩
  have hu1 : U₁ ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu
  have hu4 : Real.exp 4 ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
  have huM : M ^ 8 ≤ u := le_trans (le_max_right _ _) hu
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos 4) hu4
  set ℓ := Real.log u with hℓ
  have hℓ4 : 4 ≤ ℓ := by rw [hℓ, Real.le_log_iff_exp_le hu0]; exact hu4
  have hℓ0 : 0 < ℓ := by linarith
  have hlogsqrt : Real.log (Real.sqrt u) = ℓ / 2 := by
    rw [Real.log_sqrt hu0.le]
  rw [hlogsqrt]
  set v := u ^ (1 / 8 : ℝ) with hv
  have hv0 : 0 ≤ v := Real.rpow_nonneg hu0.le _
  have hv8 : v ^ 8 = u := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
  have hsq : Real.sqrt u = v ^ 4 := by
    rw [Real.sqrt_eq_rpow, hv, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
  have hℓv : ℓ ≤ v := hU₁ u hu1
  have hMv : M ≤ v := by
    by_contra h
    push Not at h
    have hM0 : 0 ≤ M := by positivity
    have : v ^ 8 < M ^ 8 := pow_lt_pow_left₀ h hv0 (by norm_num)
    linarith
  have hpoly := poly_le (A := A) (B := B) (S := S) hMv
  have hv1 : 1 ≤ v := by linarith [abs_nonneg A, abs_nonneg S, abs_nonneg B]
  rw [hsq]
  -- the claim, multiplied by `ℓ`
  have key : A * ℓ + (v ^ 4 + 1) * ℓ ^ 2 + 4 * (v ^ 4 + 1 + S) + 2 * B + 4 ≤ u := by
    have e1 : A * ℓ ≤ |A| * v := by
      calc A * ℓ ≤ |A| * ℓ := mul_le_mul_of_nonneg_right (le_abs_self A) hℓ0.le
        _ ≤ |A| * v := mul_le_mul_of_nonneg_left hℓv (abs_nonneg A)
    have e2 : (v ^ 4 + 1) * ℓ ^ 2 ≤ 2 * v ^ 6 := by
      have : ℓ ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hℓ0.le hℓv 2
      have h41 : 1 ≤ v ^ 4 := one_le_pow₀ hv1
      nlinarith
    have e3 : S ≤ |S| := le_abs_self S
    have e4 : B ≤ |B| := le_abs_self B
    rw [← hv8]
    linarith
  have e : A + u / (2 * (ℓ / 2)) +
      (2 * ((v ^ 4 + 1) * (ℓ / 2) ^ 2 + (v ^ 4 + 1 + S)) + B + w) / (ℓ / 2)
      = (A * ℓ + u + ((v ^ 4 + 1) * ℓ ^ 2 + 4 * (v ^ 4 + 1 + S) + 2 * B + 2 * w)) / ℓ := by
    field_simp; ring
  rw [e, div_le_div_iff_of_pos_right hℓ0]
  linarith

end Littlewood
