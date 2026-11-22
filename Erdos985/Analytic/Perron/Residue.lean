import Erdos985.Analytic.Perron.Kernel

/-!
# Perron kernel with one extra simple pole, via Mellin inversion

For `w ≠ 0, -1` with `re w < c`, the function
`t ↦ t^(-w)/(w(w+1)) - 1/w + t/(1+w)` on `(0, 1]` (and `0` for `t > 1`) is continuous on
`(0, ∞)` and has Mellin transform `1/((s - w) s (s + 1))` on `re s = c`; Mellin inversion
at `1/x` then gives the residue formula.
-/

open Complex MeasureTheory Set Filter Topology

namespace Erdos985.Analytic.PerronKernel

/-- The expression on `(0, 1]`. -/
noncomputable def resExpr (w : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)

/-- The function whose Mellin transform is `1/((s - w) s (s + 1))`. -/
noncomputable def resFun (w : ℂ) (t : ℝ) : ℂ := if t ≤ 1 then resExpr w t else 0

lemma resExpr_one (w : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ -1) : resExpr w 1 = 0 := by
  have h1 : w + 1 ≠ 0 := fun h => hw1 (eq_neg_of_add_eq_zero_left h)
  have h2 : 1 + w ≠ 0 := by rwa [add_comm]
  unfold resExpr
  simp only [ofReal_one, one_cpow]
  field_simp
  ring

lemma resFun_eq_on_Ioi (w : ℂ) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    resFun w t = (1 / (w * (w + 1))) • indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (-w) : ℝ → ℂ) t
      - (1 / w) • indicator (Ioc 0 1) (fun _ => 1 : ℝ → ℂ) t
      + (1 / (1 + w)) • indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (1 : ℂ) : ℝ → ℂ) t := by
  simp only [mem_Ioi] at ht
  unfold resFun resExpr
  by_cases h1 : t ≤ 1
  · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, h1⟩
    simp only [h1, ↓reduceIte]
    rw [indicator_of_mem hm, indicator_of_mem hm, indicator_of_mem hm, cpow_one]
    simp only [smul_eq_mul]
    ring
  · have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => h1 h.2
    simp only [h1, ↓reduceIte]
    rw [indicator_of_notMem hm, indicator_of_notMem hm, indicator_of_notMem hm]
    simp

lemma hasMellin_resFun {s w : ℂ} (hs : 0 < s.re) (hsw : w.re < s.re) (hw0 : w ≠ 0)
    (hw1 : w ≠ -1) : HasMellin (resFun w) s (1 / ((s - w) * s * (s + 1))) := by
  have hA := hasMellin_cpow_Ioc (-w) (s := s) (by simp; linarith)
  have hB := hasMellin_one_Ioc hs
  have hC := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simp; linarith)
  have hA' := hasMellin_const_smul hA.1 (1 / (w * (w + 1)))
  have hB' := hasMellin_const_smul hB.1 (1 / w)
  have hC' := hasMellin_const_smul hC.1 (1 / (1 + w))
  have hAB := hasMellin_sub hA'.1 hB'.1
  have h := hasMellin_add hAB.1 hC'.1
  rw [hAB.2, hA'.2, hB'.2, hC'.2, hA.2, hB.2, hC.2] at h
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hsw0 : s - w ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hsw0' : s + -w ≠ 0 := by rwa [← sub_eq_add_neg]
  have h1 : w + 1 ≠ 0 := fun h => hw1 (eq_neg_of_add_eq_zero_left h)
  have h2 : 1 + w ≠ 0 := by rwa [add_comm]
  have hval : (1 / (w * (w + 1))) • (1 / (s + -w)) - (1 / w) • (1 / s)
      + (1 / (1 + w)) • (1 / (s + 1)) = 1 / ((s - w) * s * (s + 1)) := by
    simp only [smul_eq_mul, ← sub_eq_add_neg]
    field_simp
    ring
  rw [hval] at h
  refine ⟨?_, ?_⟩
  · have := h.1
    unfold MellinConvergent at this ⊢
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [resFun_eq_on_Ioi w ht]
  · rw [← h.2]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [resFun_eq_on_Ioi w ht]

lemma continuousAt_resFun (w : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ -1) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ContinuousAt (resFun w) x₀ := by
  set a := min (x₀ / 2) (1 / 2) with ha
  have ha0 : 0 < a := lt_min (by positivity) (by norm_num)
  have ha1 : a ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hax : a < x₀ := (min_le_left _ _).trans_lt (by linarith)
  let g : ℝ → ℂ := fun t => if t ≤ 1 then resExpr w (max t a) else 0
  have hE : Continuous fun t : ℝ => resExpr w (max t a) := by
    have hm : Continuous fun t : ℝ => max t a := continuous_id.max continuous_const
    have hpow : Continuous fun t : ℝ => ((max t a : ℝ) : ℂ) ^ (-w) := by
      refine continuous_iff_continuousAt.2 fun t => ?_
      refine ContinuousAt.cpow (continuous_ofReal.comp hm).continuousAt continuousAt_const ?_
      exact ofReal_mem_slitPlane.2 (lt_of_lt_of_le ha0 (le_max_right _ _))
    unfold resExpr
    exact ((hpow.div_const _).sub continuous_const).add
      ((continuous_ofReal.comp hm).div_const _)
  have hg : Continuous g := by
    refine continuous_if_le continuous_id continuous_const hE.continuousOn
      continuous_const.continuousOn (fun t ht => ?_)
    rw [ht, max_eq_left ha1]
    exact resExpr_one w hw0 hw1
  have hev : g =ᶠ[𝓝 x₀] resFun w := by
    filter_upwards [Ioi_mem_nhds hax] with t ht
    simp only [g, resFun, max_eq_left (le_of_lt (mem_Ioi.1 ht))]
  exact hg.continuousAt.congr hev

lemma integrable_inv_denom_res (c : ℝ) (hc : 0 < c) (w : ℂ) (hw : w.re < c) :
    Integrable fun t : ℝ =>
      1 / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  have hδ : 0 < c - w.re := by linarith
  have hne : ∀ t : ℝ, ((c : ℂ) + t * I - w) ≠ 0 := by
    intro t h; have := congrArg Complex.re h; simp at this; linarith
  have hcont : Continuous fun t : ℝ =>
      1 / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
    have h0 : Continuous fun t : ℝ => (c : ℂ) + t * I :=
      continuous_const.add (continuous_ofReal.mul continuous_const)
    have h1 : Continuous fun t : ℝ =>
        ((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1) :=
      ((h0.sub continuous_const).mul h0).mul (h0.add continuous_const)
    refine Continuous.div (f := fun _ => (1:ℂ)) continuous_const h1 (fun t => ?_)
    rw [mul_assoc]
    exact mul_ne_zero (hne t) (denom_ne_zero c hc t)
  refine Integrable.mono' ((integrable_inv_denom c hc).norm.const_mul (c - w.re)⁻¹)
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hge : c - w.re ≤ ‖(c : ℂ) + t * I - w‖ := by
    have := re_le_norm ((c : ℂ) + t * I - w); simpa using this
  rw [mul_assoc, norm_div, norm_div, norm_one, norm_mul]
  rw [← one_div_mul_one_div, ← one_div (c - w.re)]
  exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hδ hge)
    (one_div_nonneg.2 (norm_nonneg _))

theorem perron_residue_aux (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w.re < c)
    (hw0 : w ≠ 0) (hw1 : w ≠ -1) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (x : ℂ) ^ w / (w * (w + 1)) - 1 / w + (x : ℂ) ^ (-1 : ℂ) / (1 + w) := by
  have hx0 : 0 < x := by linarith
  have hmel : ∀ t : ℝ, mellin (resFun w) ((c : ℂ) + t * I)
      = 1 / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := fun t =>
    (hasMellin_resFun (s := (c : ℂ) + t * I) (by simpa using hc) (by simpa using hw) hw0 hw1).2
  have hconv : MellinConvergent (resFun w) (c : ℂ) :=
    (hasMellin_resFun (by simpa using hc) (by simpa using hw) hw0 hw1).1
  have hvert : VerticalIntegrable (mellin (resFun w)) c := by
    unfold VerticalIntegrable
    simp_rw [hmel]
    exact integrable_inv_denom_res c hc w hw
  have hinv := mellinInv_mellin_eq (E := ℂ) c (resFun w) (x := 1 / x) (by positivity) hconv hvert
    (continuousAt_resFun w hw0 hw1 (by positivity))
  have hint : (∫ t : ℝ, (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))
      = ∫ t : ℝ, (((1 / x : ℝ)) : ℂ) ^ (-((c : ℂ) + t * I)) • mellin (resFun w) ((c : ℂ) + t * I) := by
    congr 1
    funext t
    rw [hmel t, smul_eq_mul, ofReal_div, ofReal_one, one_div (x : ℂ),
      inv_cpow_ofReal_nonneg hx0.le, cpow_neg, inv_inv]
    ring
  rw [hint]
  unfold mellinInv at hinv
  rw [Complex.real_smul] at hinv
  have h2 : ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 / (2 * (Real.pi : ℂ)) := by push_cast; ring
  rw [h2] at hinv
  rw [hinv]
  have hle : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hx
  unfold resFun resExpr
  simp only [hle, ↓reduceIte]
  rw [ofReal_div, ofReal_one, one_div (x : ℂ), inv_cpow_ofReal_nonneg hx0.le, cpow_neg, inv_inv,
    cpow_neg_one]

end Erdos985.Analytic.PerronKernel
