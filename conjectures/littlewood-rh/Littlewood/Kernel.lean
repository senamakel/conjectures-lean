import Erdos985.Analytic.Perron
import Erdos985.Analytic.Perron.Weighted

/-!
# Step 1: the Perron kernels `y^w / w²` and `y^w / ((w - b) w)` on the line `Re w = 2`

Both are Mellin transforms of profiles supported on `(0, 1]`, so erdos-985's `perron_prof`
(Mathlib's Mellin inversion) evaluates them without any contour shift:

* `(1/2π) ∫ y^w / w² dv = log y` for `y ≥ 1`, and `0` for `0 < y < 1`;
* `(1/2π) ∫ y^w / ((w - b) w) dv = (y^b - 1) / b` for `y ≥ 1`, `Re b < 2`, `b ≠ 0`.
-/

open Complex MeasureTheory Set

namespace Littlewood

open Erdos985.Analytic Erdos985.Analytic.PerronAux

/-- The point `2 + v i` of the Perron line. -/
noncomputable def lineP (v : ℝ) : ℂ := (2 : ℂ) + v * I

@[simp] lemma lineP_re (v : ℝ) : (lineP v).re = 2 := by simp [lineP]

@[simp] lemma lineP_im (v : ℝ) : (lineP v).im = v := by simp [lineP]

lemma lineP_ne_zero (v : ℝ) : lineP v ≠ 0 := fun h => by
  have := congrArg re h; simp at this

lemma continuous_lineP : Continuous lineP :=
  continuous_const.add (continuous_ofReal.mul continuous_const)

lemma two_le_norm_lineP (v : ℝ) : 2 ≤ ‖lineP v‖ := by
  have := re_le_norm (lineP v); simpa using this

/-- `‖w + 1‖ ≤ (3/2) ‖w‖` on the line. -/
lemma norm_lineP_add_one_le (v : ℝ) : ‖lineP v + 1‖ ≤ 3 / 2 * ‖lineP v‖ := by
  have h := two_le_norm_lineP v
  calc ‖lineP v + 1‖ ≤ ‖lineP v‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ = ‖lineP v‖ + 1 := by simp
    _ ≤ 3 / 2 * ‖lineP v‖ := by linarith

lemma lineP_eq (v : ℝ) : lineP v = ((2 : ℝ) : ℂ) + v * I := by simp [lineP]

/-- The kernel `y^w / w²` is integrable on the line. -/
lemma integrable_kerLog {y : ℝ} (hy : 0 < y) :
    Integrable fun v : ℝ => (y : ℂ) ^ lineP v * (1 / lineP v ^ 2) := by
  have hK := PerronKernel.integrable_K 2 y two_pos hy
  refine Integrable.mono' (hK.norm.const_mul (3 / 2)) ?_ (Filter.Eventually.of_forall fun v => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    refine Continuous.mul ?_ ?_
    · exact continuous_lineP.const_cpow (Or.inl (by exact_mod_cast hy.ne'))
    · exact Continuous.div (f := fun _ => (1 : ℂ)) continuous_const (continuous_lineP.pow 2) fun v => pow_ne_zero 2 (lineP_ne_zero v)
  · unfold PerronKernel.K
    have hn : 0 < ‖lineP v‖ := norm_pos_iff.2 (lineP_ne_zero v)
    have h1 : 0 < ‖lineP v + 1‖ := by
      have := one_le_norm_line_add_one (c := 2) (by norm_num) v
      rw [lineP_eq]; linarith
    have hb := norm_lineP_add_one_le v
    rw [← lineP_eq, norm_mul, norm_div, norm_div, norm_mul, norm_one, norm_pow]
    have hy' : 0 ≤ ‖(y : ℂ) ^ lineP v‖ := norm_nonneg _
    have : 1 / ‖lineP v‖ ^ 2 ≤ 3 / 2 * (1 / (‖lineP v‖ * ‖lineP v + 1‖)) := by
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith
    calc ‖(y : ℂ) ^ lineP v‖ * (1 / ‖lineP v‖ ^ 2)
        ≤ ‖(y : ℂ) ^ lineP v‖ * (3 / 2 * (1 / (‖lineP v‖ * ‖lineP v + 1‖))) :=
          mul_le_mul_of_nonneg_left this hy'
      _ = 3 / 2 * (‖(y : ℂ) ^ lineP v‖ / (‖lineP v‖ * ‖lineP v + 1‖)) := by ring

lemma integrable_inv_lineP_sq : Integrable fun v : ℝ => 1 / ((2 : ℂ) + v * I) ^ 2 := by
  have := integrable_kerLog (y := 1) one_pos
  simpa [lineP] using this

/-- **Perron, log kernel**: `(1/2π) ∫ y^w / w² dv = log y` if `y ≥ 1`, else `0`. -/
theorem perron_log {y : ℝ} (hy : 0 < y) :
    (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, (y : ℂ) ^ lineP v * (1 / lineP v ^ 2)
      = if 1 ≤ y then (Real.log y : ℂ) else 0 := by
  have key := perron_prof (c := 2) hy (-1) 0 0 0 0 0 0 0 (by simp) (by simp) (by simp)
    (by simp) (by simp) (fun _ => by simp) (F := fun w => 1 / w ^ 2)
    (fun v => by simp only [ofReal_ofNat, add_zero, zero_mul]; ring)
    integrable_inv_lineP_sq
  simp only [ofReal_ofNat] at key
  have hfun : (fun v : ℝ => (y : ℂ) ^ lineP v * (1 / lineP v ^ 2))
      = fun v : ℝ => (y : ℂ) ^ ((2 : ℂ) + v * I) * (1 / ((2 : ℂ) + v * I) ^ 2) := by
    funext v; simp [lineP]
  rw [hfun, key, prof]
  split_ifs with h
  · rw [indicator_of_mem (show y⁻¹ ∈ Ioc (0 : ℝ) 1 from
      ⟨inv_pos.2 hy, inv_le_one_of_one_le₀ h⟩), Real.log_inv]
    simp
  · rw [indicator_of_notMem]
    intro hm
    rcases inv_le_one_iff₀.1 hm.2 with h' | h'
    · linarith
    · exact h h'

/-- `‖y^w / ((w - b) w)‖ ≤ (3/2) ‖y^w / ((w - b)(w + 1))‖` on the line. -/
lemma norm_kerPole_le (y : ℝ) (b : ℂ) (v : ℝ) :
    ‖(y : ℂ) ^ lineP v * (1 / ((lineP v - b) * lineP v))‖ ≤
      3 / 2 * ‖(y : ℂ) ^ lineP v / ((lineP v - b) * (lineP v + 1))‖ := by
  have hn : 0 < ‖lineP v‖ := norm_pos_iff.2 (lineP_ne_zero v)
  have hb := norm_lineP_add_one_le v
  rw [norm_mul, norm_div, norm_div, norm_mul, norm_mul, norm_one]
  rcases eq_or_ne ‖lineP v - b‖ 0 with h | h
  · simp [h]
  have h' : 0 < ‖lineP v - b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
  have h1 : 0 < ‖lineP v + 1‖ := by
    have := one_le_norm_line_add_one (c := 2) (by norm_num) v
    rw [lineP_eq]; linarith
  have hy' : 0 ≤ ‖(y : ℂ) ^ lineP v‖ := norm_nonneg _
  have : 1 / (‖lineP v - b‖ * ‖lineP v‖) ≤ 3 / 2 * (1 / (‖lineP v - b‖ * ‖lineP v + 1‖)) := by
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  calc ‖(y : ℂ) ^ lineP v‖ * (1 / (‖lineP v - b‖ * ‖lineP v‖))
      ≤ ‖(y : ℂ) ^ lineP v‖ * (3 / 2 * (1 / (‖lineP v - b‖ * ‖lineP v + 1‖))) :=
        mul_le_mul_of_nonneg_left this hy'
    _ = 3 / 2 * (‖(y : ℂ) ^ lineP v‖ / (‖lineP v - b‖ * ‖lineP v + 1‖)) := by ring

/-- Uniform `L¹` bound and integrability for the pole kernel: for `Re b ≤ 1`,
`∫ ‖y^w / ((w - b) w)‖ dv ≤ K y² (1 + ‖b‖)^{-1/2}`. -/
theorem kerPole_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 < y → ∀ b : ℂ, b.re ≤ 1 →
      Integrable (fun v : ℝ => (y : ℂ) ^ lineP v * (1 / ((lineP v - b) * lineP v))) ∧
      ∫ v : ℝ, ‖(y : ℂ) ^ lineP v * (1 / ((lineP v - b) * lineP v))‖
        ≤ K * y ^ (2 : ℝ) * (1 + ‖b‖) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := perron_pair_integral_norm_le (δ := 1) (θ := 1 / 2) one_pos
    (by norm_num) (by norm_num)
  refine ⟨3 / 2 * K, by positivity, fun y hy b hb => ?_⟩
  obtain ⟨hI, hN⟩ := hK y 2 hy two_pos b (by linarith)
  simp only [ofReal_ofNat] at hI hN
  have hI' : Integrable fun v : ℝ => (y : ℂ) ^ lineP v / ((lineP v - b) * (lineP v + 1)) := hI
  have hN' : ∫ v : ℝ, ‖(y : ℂ) ^ lineP v / ((lineP v - b) * (lineP v + 1))‖
      ≤ K * y ^ (2 : ℝ) * (1 + ‖b‖) ^ (-(1 / 2 : ℝ)) := hN
  have hmeas : AEStronglyMeasurable
      (fun v : ℝ => (y : ℂ) ^ lineP v * (1 / ((lineP v - b) * lineP v))) := by
    refine (Continuous.mul ?_ ?_).aestronglyMeasurable
    · exact continuous_lineP.const_cpow (Or.inl (by exact_mod_cast hy.ne'))
    · refine Continuous.div (f := fun _ => (1 : ℂ)) continuous_const ((continuous_lineP.sub continuous_const).mul continuous_lineP)
        fun v => mul_ne_zero (fun h => ?_) (lineP_ne_zero v)
      have := congrArg re h; simp at this; linarith
  have hint : Integrable (fun v : ℝ => (y : ℂ) ^ lineP v * (1 / ((lineP v - b) * lineP v))) :=
    Integrable.mono' (hI'.norm.const_mul (3 / 2)) hmeas
      (Filter.Eventually.of_forall fun v => norm_kerPole_le y b v)
  refine ⟨hint, ?_⟩
  calc ∫ v : ℝ, ‖(y : ℂ) ^ lineP v * (1 / ((lineP v - b) * lineP v))‖
      ≤ ∫ v : ℝ, 3 / 2 * ‖(y : ℂ) ^ lineP v / ((lineP v - b) * (lineP v + 1))‖ :=
        integral_mono hint.norm (hI'.norm.const_mul _) fun v => norm_kerPole_le y b v
    _ = 3 / 2 * ∫ v : ℝ, ‖(y : ℂ) ^ lineP v / ((lineP v - b) * (lineP v + 1))‖ := integral_const_mul _ _
    _ ≤ 3 / 2 * (K * y ^ (2 : ℝ) * (1 + ‖b‖) ^ (-(1 / 2 : ℝ))) := by gcongr
    _ = 3 / 2 * K * y ^ (2 : ℝ) * (1 + ‖b‖) ^ (-(1 / 2 : ℝ)) := by ring

lemma pole_partial {w b : ℂ} (hw : w ≠ 0) (hwb : w - b ≠ 0) (hb : b ≠ 0) :
    0 * (-1 / (w + 0) ^ 2) + (1 / b * (1 / (w + -b)) + -1 / b * (1 / (w + 0)) + 0 * (1 / (w + 0)))
      = 1 / ((w - b) * w) := by
  rw [← sub_eq_add_neg, add_zero]
  field_simp
  ring

/-- **Perron, pole kernel**: `(1/2π) ∫ y^w / ((w - b) w) dv = (y^b - 1) / b` for `y ≥ 1`,
`Re b ≤ 1`, `b ≠ 0`. -/
theorem perron_pole {y : ℝ} (hy : 1 ≤ y) {b : ℂ} (hb : b.re ≤ 1) (hb0 : b ≠ 0) :
    (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, (y : ℂ) ^ lineP v * (1 / ((lineP v - b) * lineP v))
      = ((y : ℂ) ^ b - 1) / b := by
  have hy0 : 0 < y := by linarith
  obtain ⟨K, -, hK⟩ := kerPole_bound
  have hF1 : Integrable fun v : ℝ => 1 / (((2 : ℂ) + v * I - b) * ((2 : ℂ) + v * I)) := by
    have := (hK 1 one_pos b hb).1
    simpa [lineP] using this
  have key := perron_prof (c := 2) hy0 0 0 (1 / b) (-1 / b) 0 (-b) 0 0 (by simp) (by simp)
    (by simp; linarith) (by simp) (by simp) (fun _ => by ring)
    (F := fun w => 1 / ((w - b) * w))
    (fun v => by
      have h0 : (2 : ℂ) + v * I ≠ 0 := lineP_ne_zero v
      have h1 : (2 : ℂ) + v * I - b ≠ 0 := fun h => by
        have := congrArg re h; simp at this; linarith
      simp only [ofReal_ofNat]
      exact pole_partial h0 h1 hb0)
    hF1
  simp only [ofReal_ofNat] at key
  change (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, (y : ℂ) ^ ((2 : ℂ) + v * I) *
      (1 / (((2 : ℂ) + v * I - b) * ((2 : ℂ) + v * I))) = _
  rw [key, prof, indicator_of_mem (show y⁻¹ ∈ Ioc (0 : ℝ) 1 from
      ⟨inv_pos.2 hy0, inv_le_one_of_one_le₀ hy⟩), inv_ofReal_cpow_neg hy0]
  simp only [cpow_zero, zero_mul, zero_add, mul_one, add_zero]
  field_simp
  ring

end Littlewood
