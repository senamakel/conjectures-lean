import Mathlib

/-!
# Asymptotic, step 3: an abstract squeeze

If for every `ε > 0` the mean square `I(X)` is within `t`-weighted error `E(X) ≤ K + ε log X` of
a mean square `W(X) = c_S log X + O(1)` with `|c_S − c| ≤ ε`, in the sense of the pointwise
inequalities `f² ≤ (1+t)g² + (1+1/t)(f+g)²` integrated, then `I(X)/log X → c`.
-/

namespace Cramer.MeanSq

open Filter Topology

/-- `(p + q)² ≤ (1 + t)p² + (1 + 1/t)q²` for `t > 0`. -/
lemma sq_add_le_weighted (p q : ℝ) {t : ℝ} (ht : 0 < t) :
    (p + q) ^ 2 ≤ (1 + t) * p ^ 2 + (1 + 1 / t) * q ^ 2 := by
  have h : t * (p + q) ^ 2 ≤ t * ((1 + t) * p ^ 2 + (1 + 1 / t) * q ^ 2) := by
    have e : t * ((1 + t) * p ^ 2 + (1 + 1 / t) * q ^ 2) = t * (1 + t) * p ^ 2 + (t + 1) * q ^ 2 := by
      field_simp
    rw [e]
    nlinarith [sq_nonneg (t * p - q)]
  exact le_of_mul_le_mul_left h ht

theorem tendsto_of_approx {I : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ ε > 0, ∃ cS M K : ℝ, ∃ W E : ℝ → ℝ, |cS - c| ≤ ε ∧ ∀ᶠ X in atTop,
      |W X - cS * Real.log X| ≤ M ∧ E X ≤ K + ε * Real.log X ∧
      ∀ t > 0, I X ≤ (1 + t) * W X + (1 + 1 / t) * E X ∧
        W X ≤ (1 + t) * I X + (1 + 1 / t) * E X) :
    Tendsto (fun X => I X / Real.log X) atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  set t : ℝ := min 1 (η / (4 * (c + 1))) with htdef
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htc : t * c ≤ η / 4 := by
    have h1 : t ≤ η / (4 * (c + 1)) := min_le_right _ _
    have h2 : t * (c + 1) ≤ η / 4 := by
      rw [le_div_iff₀ (by positivity)] at h1
      linarith
    nlinarith
  set ε : ℝ := η * t / 8 with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨cS, M, K, W, E, hcS, hev⟩ := h ε hε
  set s : ℝ := 1 + 1 / t with hsdef
  have hs0 : 0 < s := by positivity
  have hsε : s * ε ≤ η / 4 := by
    have e : s * ε = (t + 1) * η / 8 := by rw [hsdef, hεdef]; field_simp
    rw [e]; nlinarith
  set P : ℝ := (1 + t) * |M| + s * |K| with hPdef
  have hP0 : 0 ≤ P := by positivity
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop (4 * (P + 1) / η)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hev.and hlog)
  refine ⟨N, fun X hX => ?_⟩
  obtain ⟨⟨hW, hE, hineq⟩, hL⟩ := hN X hX
  set L := Real.log X with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hPL : P + 1 ≤ η * L / 4 := by
    rw [div_le_iff₀ hη] at hL; linarith
  obtain ⟨hup, hlo⟩ := hineq t ht0
  rw [abs_le] at hW hcS
  have hM := le_abs_self M
  have hK := le_abs_self K
  have hM' := neg_abs_le M
  have hK' := neg_abs_le K
  rw [Real.dist_eq, abs_lt]
  constructor
  · -- lower bound
    suffices key : (c - η) * L < I X by
      have := (lt_div_iff₀ hL0).2 key; linarith
    have h1 : (1 + t) * I X ≥ (cS - s * ε) * L - (|M| + s * |K|) := by
      have a2 : s * E X ≤ s * (|K| + ε * L) := mul_le_mul_of_nonneg_left (by linarith) hs0.le
      have e : (cS - s * ε) * L - (|M| + s * |K|) = (cS * L - |M|) - s * (|K| + ε * L) := by ring
      rw [e]; linarith
    have h2 : (cS - s * ε) * L ≥ (c - 3 * η / 8) * L := by
      apply mul_le_mul_of_nonneg_right _ hL0.le
      have : ε ≤ η / 8 := by rw [hεdef]; nlinarith
      linarith
    have h3 : |M| + s * |K| ≤ P := by
      rw [hPdef]; nlinarith [abs_nonneg M]
    have h4 : (1 + t) * ((c - η) * L) ≤ (c - 3 * η / 4) * L := by
      have : (1 + t) * (c - η) ≤ c - 3 * η / 4 := by nlinarith
      nlinarith
    have h5 : (1 + t) * ((c - η) * L) < (1 + t) * I X := by nlinarith
    have := lt_of_mul_lt_mul_left h5 (by linarith)
    linarith
  · -- upper bound
    suffices key : I X < (c + η) * L by
      have := (div_lt_iff₀ hL0).2 key; linarith
    have h1 : I X ≤ ((1 + t) * cS + s * ε) * L + P := by
      have a1 : (1 + t) * W X ≤ (1 + t) * (cS * L + |M|) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have a2 : s * E X ≤ s * (|K| + ε * L) := mul_le_mul_of_nonneg_left (by linarith) hs0.le
      have e : ((1 + t) * cS + s * ε) * L + P = (1 + t) * (cS * L + |M|) + s * (|K| + ε * L) := by
        rw [hPdef]; ring
      rw [e]; linarith
    have h2 : ((1 + t) * cS + s * ε) * L ≤ (c + 3 * η / 4) * L := by
      apply mul_le_mul_of_nonneg_right _ hL0.le
      have : (1 + t) * cS ≤ (1 + t) * (c + ε) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have htt : (1 + t) * t ≤ 2 * 1 :=
        mul_le_mul (by linarith only [ht1]) ht1 ht0.le (by norm_num)
      have : (1 + t) * ε ≤ η / 4 := by
        have e : (1 + t) * ε = η * ((1 + t) * t) / 8 := by rw [hεdef]; ring
        rw [e]
        have := mul_le_mul_of_nonneg_left htt hη.le
        linarith only [this]
      have e2 : (1 + t) * (c + ε) = c + t * c + (1 + t) * ε := by ring
      linarith only [e2, this, htc, hsε, ‹(1 + t) * cS ≤ (1 + t) * (c + ε)›]
    have e3 : (c + η) * L = (c + 3 * η / 4) * L + η * L / 4 := by ring
    linarith only [e3, h1, h2, hPL]

end Cramer.MeanSq
