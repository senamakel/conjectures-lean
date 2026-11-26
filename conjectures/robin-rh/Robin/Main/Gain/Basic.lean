import Robin.Defs

/-!
# Auxiliary functions for the gain bound

* `gW t = 1/(t² log t)`, so that `gW p · log p = 1/p²`;
* `vW t = (2 log t + 1)/(t³ log² t) = −gW'(t)`;
* `vW' t = −(6 log² t + 5 log t + 2)/(t⁴ log³ t) = vW'(t)`;
* `cP k = log k` if `k` is prime and `0` otherwise.
-/

namespace Robin.Gain

open Real

noncomputable def gW (t : ℝ) : ℝ := 1 / (t ^ 2 * Real.log t)

noncomputable def vW (t : ℝ) : ℝ := (2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)

noncomputable def vW' (t : ℝ) : ℝ :=
  -(6 * Real.log t ^ 2 + 5 * Real.log t + 2) / (t ^ 4 * Real.log t ^ 3)

noncomputable def cP (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

theorem hasDerivAt_gW {t : ℝ} (ht : 1 < t) : HasDerivAt gW (-vW t) t := by
  have ht0 : t ≠ 0 := by positivity
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h1 : HasDerivAt (fun s => s ^ 2 * Real.log s) (2 * t * Real.log t + t ^ 2 * t⁻¹) t := by
    have := (hasDerivAt_pow 2 t).mul (Real.hasDerivAt_log ht0)
    convert this using 1; push_cast; ring
  have h2 := h1.inv (mul_ne_zero (pow_ne_zero 2 ht0) hl)
  have : gW = fun s => (s ^ 2 * Real.log s)⁻¹ := by funext s; simp [gW]
  rw [this]
  convert h2 using 1
  simp only [vW]
  field_simp

theorem hasDerivAt_vW {t : ℝ} (ht : 1 < t) : HasDerivAt vW (vW' t) t := by
  have ht0 : t ≠ 0 := by positivity
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hn : HasDerivAt (fun s => 2 * Real.log s + 1) (2 * t⁻¹) t := by
    simpa using ((Real.hasDerivAt_log ht0).const_mul 2).add_const 1
  have hd : HasDerivAt (fun s => s ^ 3 * Real.log s ^ 2)
      (3 * t ^ 2 * Real.log t ^ 2 + t ^ 3 * (2 * Real.log t * t⁻¹)) t := by
    have hl2 : HasDerivAt (fun s => Real.log s ^ 2) (2 * Real.log t * t⁻¹) t := by
      convert (Real.hasDerivAt_log ht0).pow 2 using 1; push_cast; ring
    have := (hasDerivAt_pow 3 t).mul hl2
    convert this using 1
  have h := hn.div hd (mul_ne_zero (pow_ne_zero 3 ht0) (pow_ne_zero 2 hl))
  have e : vW = (fun s => 2 * Real.log s + 1) / fun s => s ^ 3 * Real.log s ^ 2 := by
    funext s; simp [vW]
  rw [e]
  convert h using 1
  unfold vW'
  field_simp
  ring

theorem continuousOn_vW : ContinuousOn vW (Set.Ioi 1) := fun _ ht =>
  (hasDerivAt_vW ht).continuousAt.continuousWithinAt

theorem continuousOn_vW' : ContinuousOn vW' (Set.Ioi 1) := by
  intro t ht
  have ht' : (1 : ℝ) < t := ht
  have ht0 : t ≠ 0 := by positivity
  have hl : Real.log t ≠ 0 := (Real.log_pos ht').ne'
  apply ContinuousAt.continuousWithinAt
  unfold vW'
  apply ContinuousAt.div
  · exact ((((continuousAt_log ht0).pow 2).const_mul 6).add
      ((continuousAt_log ht0).const_mul 5)).add continuousAt_const |>.neg
  · exact (continuousAt_id.pow 4).mul ((continuousAt_log ht0).pow 3)
  · exact mul_ne_zero (pow_ne_zero 4 ht0) (pow_ne_zero 3 hl)

/-- Pointwise bound `0 ≤ vW t ≤ 4.14/(L t³)` when `log t ≥ L/2`, `L ≥ 30`. -/
theorem vW_bounds {t L : ℝ} (ht : 1 < t) (hL : 30 ≤ L) (hlt : L / 2 ≤ Real.log t) :
    0 ≤ vW t ∧ vW t ≤ 4.14 / (L * t ^ 3) := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  have hL0 : 0 < L := by linarith
  constructor
  · unfold vW; positivity
  · unfold vW
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 * Real.log t + 1) * L ≤ 4.14 * Real.log t ^ 2 := by nlinarith
    calc (2 * Real.log t + 1) * (L * t ^ 3) = ((2 * Real.log t + 1) * L) * t ^ 3 := by ring
      _ ≤ (4.14 * Real.log t ^ 2) * t ^ 3 := by gcongr
      _ = _ := by ring

/-- Pointwise bound `|vW' t| ≤ 13/(L t⁴)` when `log t ≥ L/2`, `L ≥ 30`. -/
theorem abs_vW'_le {t L : ℝ} (ht : 1 < t) (hL : 30 ≤ L) (hlt : L / 2 ≤ Real.log t) :
    |vW' t| ≤ 13 / (L * t ^ 4) := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  have hL0 : 0 < L := by linarith
  unfold vW'
  rw [abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have : (6 * Real.log t ^ 2 + 5 * Real.log t + 2) * L ≤ 13 * Real.log t ^ 3 := by nlinarith
  calc (6 * Real.log t ^ 2 + 5 * Real.log t + 2) * (L * t ^ 4)
      = ((6 * Real.log t ^ 2 + 5 * Real.log t + 2) * L) * t ^ 4 := by ring
    _ ≤ (13 * Real.log t ^ 3) * t ^ 4 := by gcongr
    _ = _ := by ring

end Robin.Gain
