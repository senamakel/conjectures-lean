import Mathlib

/-!
# The Cesàro–Perron kernel via Mellin inversion

The Mellin transform of `t ↦ max 0 (1 - t)` is `1 / (s (s + 1))` for `0 < re s`, and Mellin
inversion then evaluates `(1/2π) ∫ y^(c+ti) / ((c+ti)(c+ti+1)) dt = max 0 (1 - 1/y)`.
-/

open Complex MeasureTheory Set

namespace Erdos985.Analytic.PerronKernel

/-- The function whose Mellin transform is `1 / (s (s + 1))`. -/
noncomputable def cesaro (t : ℝ) : ℂ := ((max 0 (1 - t) : ℝ) : ℂ)

lemma continuous_cesaro : Continuous cesaro := by
  unfold cesaro; fun_prop

lemma cesaro_eq_on_Ioi {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    cesaro t = indicator (Ioc 0 1) (fun _ => 1 : ℝ → ℂ) t
      - indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (1 : ℂ) : ℝ → ℂ) t := by
  simp only [mem_Ioi] at ht
  unfold cesaro
  by_cases h1 : t ≤ 1
  · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, h1⟩
    rw [indicator_of_mem hm, indicator_of_mem hm, cpow_one, max_eq_right (by linarith)]
    push_cast; ring
  · have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => h1 h.2
    rw [indicator_of_notMem hm, indicator_of_notMem hm, max_eq_left (by linarith)]
    simp

lemma hasMellin_cesaro {s : ℂ} (hs : 0 < s.re) : HasMellin cesaro s (1 / (s * (s + 1))) := by
  have h1 := hasMellin_one_Ioc hs
  have h2 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simp; linarith)
  have h := hasMellin_sub h1.1 h2.1
  rw [h1.2, h2.2] at h
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hval : 1 / s - 1 / (s + 1) = 1 / (s * (s + 1)) := by field_simp; ring
  rw [hval] at h
  refine ⟨?_, ?_⟩
  · have := h.1
    unfold MellinConvergent at this ⊢
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [cesaro_eq_on_Ioi ht]
  · rw [← h.2]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [cesaro_eq_on_Ioi ht]

lemma denom_ne_zero (c : ℝ) (hc : 0 < c) (t : ℝ) :
    ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1) ≠ 0 := by
  have h0 : ((c : ℂ) + t * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h1 : ((c : ℂ) + t * I + 1) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  exact mul_ne_zero h0 h1

lemma norm_denom_ge (c : ℝ) (hc : 0 < c) (t : ℝ) :
    min (c ^ 2) 1 * (1 + t ^ 2) ≤ ‖((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)‖ := by
  have hs : ‖(c : ℂ) + t * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have hs1 : ‖(c : ℂ) + t * I‖ ^ 2 ≤ ‖(c : ℂ) + t * I + 1‖ ^ 2 := by
    rw [hs, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; nlinarith
  have hn1 : ‖(c : ℂ) + t * I‖ ≤ ‖(c : ℂ) + t * I + 1‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hs1
  rw [norm_mul]
  calc min (c ^ 2) 1 * (1 + t ^ 2) ≤ c ^ 2 + t ^ 2 := by
        rcases le_total (c ^ 2) 1 with h | h
        · rw [min_eq_left h]; nlinarith [sq_nonneg t]
        · rw [min_eq_right h]; linarith
    _ = ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I‖ := by rw [← hs]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn1 (norm_nonneg _)

lemma continuous_inv_denom (c : ℝ) (hc : 0 < c) :
    Continuous fun t : ℝ => 1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) :=
  Continuous.div continuous_const (by fun_prop) (denom_ne_zero c hc)

/-- The reciprocal of the denominator is integrable on the vertical line. -/
lemma integrable_inv_denom (c : ℝ) (hc : 0 < c) :
    Integrable fun t : ℝ => 1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  have hm : 0 < min (c ^ 2) 1 := lt_min (by positivity) one_pos
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (min (c ^ 2) 1)⁻¹)
    (continuous_inv_denom c hc).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_div, norm_one]
  have h := norm_denom_ge c hc t
  have hpos : 0 < min (c ^ 2) 1 * (1 + t ^ 2) := by positivity
  calc 1 / ‖((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)‖ ≤ 1 / (min (c ^ 2) 1 * (1 + t ^ 2)) :=
        one_div_le_one_div_of_le hpos h
    _ = (min (c ^ 2) 1)⁻¹ * (1 + t ^ 2)⁻¹ := by rw [one_div, mul_inv]

theorem perron_cesaro_aux (y c : ℝ) (hy : 0 < y) (hc : 0 < c) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (max 0 (1 - 1 / y) : ℝ) := by
  have hmel : ∀ t : ℝ, mellin cesaro ((c : ℂ) + t * I)
      = 1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := fun t =>
    (hasMellin_cesaro (s := (c : ℂ) + t * I) (by simpa using hc)).2
  have hconv : MellinConvergent cesaro (c : ℂ) := (hasMellin_cesaro (by simpa using hc)).1
  have hvert : VerticalIntegrable (mellin cesaro) c := by
    unfold VerticalIntegrable
    simp_rw [hmel]
    exact integrable_inv_denom c hc
  have hinv := mellinInv_mellin_eq c cesaro (x := 1 / y) (by positivity) hconv hvert
    continuous_cesaro.continuousAt
  unfold mellinInv cesaro at hinv
  rw [← hinv]
  simp only [smul_eq_mul]
  push_cast
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [hmel t, one_div (y : ℂ), inv_cpow_ofReal_nonneg hy.le, cpow_neg, inv_inv]
  ring

end Erdos985.Analytic.PerronKernel
