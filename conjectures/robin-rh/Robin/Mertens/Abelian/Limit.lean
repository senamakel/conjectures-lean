import Mathlib

/-!
# An Abelian lemma for Mellin-type averages

If `F t → C` as `t → ∞` and `F(t) t^{-s}` is integrable on `(1, ∞)` for every `s > 1`, then
`(s − 1) ∫₁^∞ F(t) t^{-s} dt → C` as `s → 1⁺`.
-/

namespace Robin

open Filter Topology Real MeasureTheory Set

/-- `∫₁^∞ t^{-s} dt = 1/(s-1)` for `s > 1`. -/
lemma integral_Ioi_one_rpow_neg {s : ℝ} (hs : 1 < s) :
    ∫ t in Ioi (1:ℝ), t ^ (-s) = 1 / (s - 1) := by
  rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, one_rpow]
  have h1 : -s + 1 = -(s - 1) := by ring
  rw [h1, div_neg, neg_div, neg_neg]

lemma rpow_neg_le_mul_rpow_neg_two {s t T : ℝ} (hs1 : 1 ≤ s) (_hs : s ≤ 2) (ht : 1 ≤ t) (htT : t ≤ T) :
    t ^ (-s) ≤ T * t ^ (-(2:ℝ)) := by
  have ht0 : 0 < t := by linarith
  have hsplit : t ^ (-s) = t ^ (2 - s) * t ^ (-(2:ℝ)) := by
    rw [← rpow_add ht0]; ring_nf
  rw [hsplit]
  have h2 : t ^ (2 - s) ≤ T := by
    calc t ^ (2 - s) ≤ t ^ (1:ℝ) := rpow_le_rpow_of_exponent_le ht (by linarith)
      _ = t := rpow_one t
      _ ≤ T := htT
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

/-- The Abelian lemma with limit `0`. -/
lemma abelian_zero {G : ℝ → ℝ} (hG : Tendsto G atTop (𝓝 0))
    (hint : ∀ s : ℝ, 1 < s → IntegrableOn (fun t => G t * t ^ (-s)) (Ioi 1)) :
    Tendsto (fun s => (s - 1) * ∫ t in Ioi 1, G t * t ^ (-s)) (𝓝[>] 1) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hG (ε / 2) (by positivity))
  set T := max T₀ 1 with hTdef
  have hT1 : 1 ≤ T := le_max_right _ _
  set K := ∫ t in Ioi 1, |G t * t ^ (-(2:ℝ))| with hKdef
  have hK : 0 ≤ K := integral_nonneg (fun _ => abs_nonneg _)
  have hTK : 0 ≤ T * K := mul_nonneg (by linarith) hK
  set δ := min 1 (ε / (2 * (T * K + 1))) with hδdef
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hmem : Ioo 1 (1 + δ) ∈ 𝓝[>] (1:ℝ) := Ioo_mem_nhdsGT (by linarith)
  filter_upwards [hmem] with s hs
  obtain ⟨hs1, hs2⟩ := hs
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ε / (2 * (T * K + 1)) := min_le_right _ _
  have hs2' : s ≤ 2 := by linarith
  set h : ℝ → ℝ := fun t => T * |G t * t ^ (-(2:ℝ))| + ε / 2 * t ^ (-s) with hhdef
  have hint2 : IntegrableOn (fun t : ℝ => t ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hh_int : IntegrableOn h (Ioi 1) :=
    ((hint 2 one_lt_two).abs.const_mul T).add (hint2.const_mul _)
  have hbound : ∀ t ∈ Ioi (1:ℝ), ‖G t * t ^ (-s)‖ ≤ h t := by
    intro t ht
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := by linarith
    have hpos : 0 ≤ t ^ (-s) := by positivity
    have hpos2 : 0 ≤ t ^ (-(2:ℝ)) := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos]
    by_cases htT : t ≤ T
    · have := rpow_neg_le_mul_rpow_neg_two hs1.le hs2' ht1.le htT
      have e1 : T * |G t * t ^ (-(2:ℝ))| = |G t| * (T * t ^ (-(2:ℝ))) := by
        rw [abs_mul, abs_of_nonneg hpos2]; ring
      have : |G t| * t ^ (-s) ≤ T * |G t * t ^ (-(2:ℝ))| := by
        rw [e1]; exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
      simp only [hhdef]
      nlinarith [mul_nonneg hε.le hpos]
    · push Not at htT
      have hGt : |G t| < ε / 2 := by
        have := hT₀ t (le_trans (le_max_left _ _) htT.le)
        simpa [Real.dist_eq] using this
      simp only [hhdef]
      have : 0 ≤ T * |G t * t ^ (-(2:ℝ))| := mul_nonneg (by linarith) (abs_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_right hGt.le hpos]
  have hI : ‖∫ t in Ioi 1, G t * t ^ (-s)‖ ≤ ∫ t in Ioi 1, h t :=
    norm_integral_le_of_norm_le hh_int (ae_restrict_of_forall_mem measurableSet_Ioi hbound)
  have hIh : ∫ t in Ioi 1, h t = T * K + ε / 2 * (1 / (s - 1)) := by
    simp only [hhdef]
    rw [integral_add ((hint 2 one_lt_two).abs.const_mul T) (hint2.const_mul _),
      integral_const_mul, integral_const_mul, integral_Ioi_one_rpow_neg hs1]
  rw [dist_zero_right, norm_mul, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < s - 1)]
  have hs0 : 0 < s - 1 := by linarith
  calc (s - 1) * ‖∫ t in Ioi 1, G t * t ^ (-s)‖
      ≤ (s - 1) * (T * K + ε / 2 * (1 / (s - 1))) := by
        rw [← hIh]; exact mul_le_mul_of_nonneg_left hI hs0.le
    _ = (s - 1) * (T * K) + ε / 2 := by field_simp
    _ < ε := by
        have hlt : s - 1 < ε / (2 * (T * K + 1)) := by linarith
        have : (s - 1) * (T * K + 1) < ε / 2 := by
          rw [lt_div_iff₀ (by positivity)] at hlt; linarith
        nlinarith

/-- **Abelian lemma.** If `F t → C` and `F(t) t^{-s}` is integrable on `(1,∞)` for `s > 1`,
then `(s-1) ∫₁^∞ F(t) t^{-s} dt → C` as `s → 1⁺`. -/
theorem abelian_limit {F : ℝ → ℝ} {C : ℝ} (hF : Tendsto F atTop (𝓝 C))
    (hint : ∀ s : ℝ, 1 < s → IntegrableOn (fun t => F t * t ^ (-s)) (Ioi 1)) :
    Tendsto (fun s => (s - 1) * ∫ t in Ioi 1, F t * t ^ (-s)) (𝓝[>] 1) (𝓝 C) := by
  have hG : Tendsto (fun t => F t - C) atTop (𝓝 0) := by
    simpa using hF.sub_const C
  have hintG : ∀ s : ℝ, 1 < s → IntegrableOn (fun t => (F t - C) * t ^ (-s)) (Ioi 1) := by
    intro s hs
    have h2 : IntegrableOn (fun t : ℝ => t ^ (-s)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine ((hint s hs).sub (h2.const_mul C)).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [sub_mul]
  have h0 := (abelian_zero hG hintG).add_const C
  rw [zero_add] at h0
  refine h0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs : 1 < s := hs
  have h2 : IntegrableOn (fun t : ℝ => t ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have : ∫ t in Ioi 1, (F t - C) * t ^ (-s)
      = (∫ t in Ioi 1, F t * t ^ (-s)) - C * (1 / (s - 1)) := by
    simp_rw [sub_mul]
    rw [integral_sub (hint s hs) (h2.const_mul C), integral_const_mul,
      integral_Ioi_one_rpow_neg hs]
  rw [this]
  have hs0 : s - 1 ≠ 0 := by linarith
  field_simp
  ring

end Robin
