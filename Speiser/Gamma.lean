import Mathlib
import Erdos985.Analytic.ExplicitFormula.Bounds.DigammaSeries

/-!
# The archimedean part is positive above height 8

For `0 ≤ Re s ≤ 1/2` and `|Im s| ≥ 8`,
`Re (1/s + 1/(s-1) - (1/2) log π + (1/2) ψ(s/2)) > 0`.

Since `ψ(s/2) = ψ(s/2 + 1) - 2/s`, the expression is `1/(s-1) - (1/2) log π + (1/2) ψ(1 + s/2)`.
With `w = 1 + s/2`, erdos-985's series `ψ(w) - ψ(1) = Σ_k (1/(k+1) - 1/(k+w))` has terms with
real part `1/n - u/(u² + v²)` (`n = k+1`, `u = n + σ/2 ∈ [n, n + 1/4]`, `v = t/2`, `v² ≥ 16`),
which are `≥ 0` and `≥ 1/n - (n + 1/4)/(n² + 16)`. The first 20 of these sum to more than
`1.87`; with `γ < 2/3`, `log π < 1.163` and `Re 1/(s-1) ≥ -1/64` the total is `> 0.005`.
-/

open Complex

namespace Speiser

/-- `log π < 1.163`, from `π < 3.15` and `e^{1.163} ≥ e (1 + 0.163 + 0.163²/2) > 3.19`. -/
lemma log_pi_lt : Real.log Real.pi < 1.163 := by
  rw [Real.log_lt_iff_lt_exp Real.pi_pos]
  have he := Real.exp_one_gt_d9
  have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.163 by norm_num)
  have : Real.exp 1.163 = Real.exp 1 * Real.exp 0.163 := by
    rw [← Real.exp_add]; norm_num
  rw [this]
  have hp := Real.pi_lt_d2
  nlinarith [Real.exp_pos 0.163]

/-- Lower bound for the real part of one term of the digamma series. -/
lemma term_re_bounds (k : ℕ) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) (ht : 64 ≤ s.im ^ 2) :
    0 ≤ (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 + s / 2))).re ∧
    1 / ((k : ℝ) + 1) - ((k : ℝ) + 1 + 1 / 4) / (((k : ℝ) + 1) ^ 2 + 16) ≤
      (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 + s / 2))).re := by
  set n : ℝ := (k : ℝ) + 1 with hn
  set u : ℝ := n + s.re / 2 with hu
  set v : ℝ := s.im / 2 with hv
  have hn1 : 1 ≤ n := by simp [hn]
  have hre1 : (1 / ((k : ℂ) + 1)).re = 1 / n := by
    rw [show ((k : ℂ) + 1) = ((n : ℝ) : ℂ) by simp [hn]]
    rw [← ofReal_one, ← ofReal_div, ofReal_re]
  have hre2 : (1 / ((k : ℂ) + (1 + s / 2))).re = u / (u ^ 2 + v ^ 2) := by
    simp only [one_div, inv_re, normSq_apply, add_re, add_im, natCast_re, natCast_im, one_re,
      one_im, div_re, div_im, hu, hv, hn]
    norm_num
    ring_nf
  rw [sub_re, hre1, hre2]
  have hun : n ≤ u := by simp [hu]; linarith
  have hun' : u ≤ n + 1 / 4 := by simp [hu]; linarith
  have hv2 : 16 ≤ v ^ 2 := by simp [hv]; nlinarith
  have hupos : 0 < u := by linarith
  have hD : 0 < u ^ 2 + v ^ 2 := by positivity
  constructor
  · rw [sub_nonneg, div_le_div_iff₀ hD (by linarith)]
    nlinarith
  · have : u / (u ^ 2 + v ^ 2) ≤ (n + 1 / 4) / (n ^ 2 + 16) := by
      rw [div_le_div_iff₀ hD (by positivity)]
      have h2 : n ^ 2 + 16 ≤ u ^ 2 + v ^ 2 := by nlinarith
      exact mul_le_mul hun' h2 (by positivity) (by linarith)
    linarith

lemma partial_sum_ge :
    (1.87 : ℝ) ≤ ∑ k ∈ Finset.range 20,
      (1 / ((k : ℝ) + 1) - ((k : ℝ) + 1 + 1 / 4) / (((k : ℝ) + 1) ^ 2 + 16)) := by
  norm_num [Finset.sum_range_succ]

/-- **The archimedean part is positive above height 8.** -/
theorem re_archimedean_pos {s : ℂ} (h0 : 0 < s.re) (h1 : s.re ≤ 1 / 2) (ht : 8 ≤ |s.im|) :
    0 < (1 / s + 1 / (s - 1) +
      (-(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma (s / 2))).re := by
  have ht2 : 64 ≤ s.im ^ 2 := by
    have := sq_abs s.im; nlinarith [abs_nonneg s.im]
  have hs0 : s ≠ 0 := fun h => by rw [h] at h0; simp at h0
  -- ψ(s/2) = ψ(1 + s/2) - 2/s
  have hrec : digamma (s / 2 + 1) = digamma (s / 2) + (s / 2)⁻¹ := by
    refine digamma_apply_add_one _ fun m h => ?_
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    linarith
  have hw : 1 / 2 < (1 + s / 2).re := by simp; linarith
  have hS := Erdos985.Analytic.BoundsAux.hasSum_digamma hw
  have hSre := Complex.hasSum_re hS
  have hb := fun k => term_re_bounds k h0.le h1 ht2
  have hlow := sum_le_hasSum (Finset.range 20) (fun k _ => (hb k).1) hSre
  have hpart := (Finset.sum_le_sum fun k (_ : k ∈ Finset.range 20) => (hb k).2).trans hlow
  have hpsi1 : digamma 1 = ((-Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    rw [digamma_one]; push_cast; ring
  have hE : 1 / s + 1 / (s - 1) +
      (-(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma (s / 2)) =
      1 / (s - 1) + (-(1 / 2) * (Real.log Real.pi : ℂ)) +
        (1 / 2) * (digamma (1 + s / 2) - digamma 1) + (1 / 2) * digamma 1 := by
    rw [add_comm 1 (s / 2), hrec]
    field_simp
    ring
  rw [hE]
  have hd1 : (digamma 1).re = -Real.eulerMascheroniConstant := by rw [hpsi1, ofReal_re]
  have hre_inv : (1 / (s - 1)).re = (s.re - 1) / ((s.re - 1) ^ 2 + s.im ^ 2) := by
    simp only [one_div, inv_re, normSq_apply, sub_re, sub_im, one_re, one_im, sub_zero]
    ring_nf
  have hre_inv' : -1 / 64 ≤ (1 / (s - 1)).re := by
    rw [hre_inv, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [sq_nonneg (s.re - 1)]
  have hlogpi := log_pi_lt
  have hgam := Real.eulerMascheroniConstant_lt_two_thirds
  have hps := partial_sum_ge
  have hgoal : (1 / (s - 1) + (-(1 / 2) * (Real.log Real.pi : ℂ)) +
      (1 / 2) * (digamma (1 + s / 2) - digamma 1) +
        (1 / 2) * digamma 1).re =
      (1 / (s - 1)).re - 1 / 2 * Real.log Real.pi +
        1 / 2 * (digamma (1 + s / 2) - digamma 1).re + 1 / 2 * (digamma 1).re := by
    simp only [add_re, mul_re, ofReal_re, ofReal_im, neg_re, neg_im]
    norm_num
    ring
  rw [hgoal]
  have hp : (1.87 : ℝ) ≤ (digamma (1 + s / 2) - digamma 1).re := hps.trans hpart
  linarith

end Speiser
