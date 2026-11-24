import Mathlib
import Erdos985.Analytic.ExplicitFormula.Bounds.DigammaSeries

/-!
# The archimedean part is positive above height 7

For `0 ≤ Re s ≤ 1/2` and `|Im s| ≥ 7`,
`Re (1/s + 1/(s-1) - (1/2) log π + (1/2) ψ(s/2)) > 0`.

Since `ψ(s/2) = ψ(s/2 + 1) - 2/s`, the expression is `1/(s-1) - (1/2) log π + (1/2) ψ(1 + s/2)`.
With `w = 1 + s/2`, erdos-985's series `ψ(w) - ψ(1) = Σ_k (1/(k+1) - 1/(k+w))` has terms with
real part `1/n - u/(u² + v²)` (`n = k+1`, `u = n + σ/2 ∈ [n, n + 1/4]`, `v = t/2`, `v² ≥ 49/4`).
They are `≥ 0`, and `≥ cTerm k`, which uses the exact maximum of `u/(u² + 49/4)` on
`[n, n + 1/4]`. The first 20 sum to more than `1.799`; with `γ < 0.5851` (`H₆₄ - log 64`),
`log π < 1.1455` and `Re 1/(s-1) ≥ -1/50` the total is `> 0.014`. The method's limit is
`|t| ≈ 6.52`, where the real part first vanishes (at `σ = 0`).
-/

open Complex

namespace Speiser

/-- `log π < 1.1455`, from `π < 3.1416` and `e^{1.1455} ≥ e (1 + 0.1455 + 0.1455²/2) > 3.142`. -/
lemma log_pi_lt : Real.log Real.pi < 1.1455 := by
  rw [Real.log_lt_iff_lt_exp Real.pi_pos]
  have he := Real.exp_one_gt_d9
  have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.1455 by norm_num)
  have : Real.exp 1.1455 = Real.exp 1 * Real.exp 0.1455 := by
    rw [← Real.exp_add]; norm_num
  rw [this]
  have hp := Real.pi_lt_d4
  nlinarith [Real.exp_pos 0.1455]

/-- `γ < H₆₄ - 6 log 2 < 0.5851`. -/
lemma eulerMascheroni_lt : Real.eulerMascheroniConstant < 0.5851 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 64
  have hl : Real.log (64 : ℕ) = 6 * Real.log 2 := by
    rw [show ((64 : ℕ) : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have hH : ((harmonic 64 : ℚ) : ℝ) ≤ 4.7439 := by
    have : harmonic 64 ≤ (4.7439 : ℚ) := by
      simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
    calc ((harmonic 64 : ℚ) : ℝ) ≤ ((4.7439 : ℚ) : ℝ) := Rat.cast_le.mpr this
      _ = 4.7439 := by norm_num
  simp only [Real.eulerMascheroniSeq', show (64 : ℕ) ≠ 0 by norm_num, ite_false, hl] at h
  linarith [Real.log_two_gt_d9]

/-- `u/(u² + w)` is increasing for `u² ≤ w`: if `u ≤ a` and `a u ≤ w`. -/
lemma frac_le_of_le {u a w : ℝ} (hua : u ≤ a) (hw : a * u ≤ w) (hw0 : 0 < w) :
    u / (u ^ 2 + w) ≤ a / (a ^ 2 + w) := by
  rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hua) (sub_nonneg.mpr hw)]

/-- `u/(u² + w)` is decreasing for `u² ≥ w`: if `n ≤ u` and `w ≤ n u`. -/
lemma frac_le_of_ge {u n w : ℝ} (hn : 0 < n) (hnu : n ≤ u) (hw : w ≤ n * u) (hw0 : 0 < w) :
    u / (u ^ 2 + w) ≤ n / (n ^ 2 + w) := by
  rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hnu) (sub_nonneg.mpr hw)]

/-- The termwise lower bound at height `7` (`v² ≥ 49/4`, `u ∈ [n, n + 1/4]`): the exact maximum of
`u/(u² + 49/4)` over the interval, at `u = n + 1/4` for `n ≤ 3` and at `u = n` for `n ≥ 4`. -/
noncomputable def cTerm (k : ℕ) : ℝ :=
  if k < 3 then 1 / ((k : ℝ) + 1) - ((k : ℝ) + 1 + 1 / 4) / (((k : ℝ) + 1 + 1 / 4) ^ 2 + 49 / 4)
  else 1 / ((k : ℝ) + 1) - ((k : ℝ) + 1) / (((k : ℝ) + 1) ^ 2 + 49 / 4)

/-- Lower bound for the real part of one term of the digamma series. -/
lemma term_re_bounds (k : ℕ) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) (ht : 49 ≤ s.im ^ 2) :
    0 ≤ (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 + s / 2))).re ∧
    cTerm k ≤ (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 + s / 2))).re := by
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
  have hv2 : 49 / 4 ≤ v ^ 2 := by simp [hv]; nlinarith
  have hupos : 0 < u := by linarith
  have hD : 0 < u ^ 2 + v ^ 2 := by positivity
  have hmono : u / (u ^ 2 + v ^ 2) ≤ u / (u ^ 2 + 49 / 4) :=
    div_le_div_of_nonneg_left hupos.le (by positivity) (by linarith)
  constructor
  · rw [sub_nonneg, div_le_div_iff₀ hD (by linarith)]
    nlinarith
  · unfold cTerm
    split_ifs with hk
    · have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.mp hk
      have := frac_le_of_le (w := 49 / 4) hun' (by nlinarith) (by norm_num)
      rw [← hn]; linarith
    · have hk' : (3 : ℝ) ≤ k := by exact_mod_cast not_lt.mp hk
      have := frac_le_of_ge (w := 49 / 4) (by linarith) hun (by nlinarith) (by norm_num)
      rw [← hn]; linarith

lemma partial_sum_ge : (1.799 : ℝ) ≤ ∑ k ∈ Finset.range 20, cTerm k := by
  simp only [cTerm, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- **The archimedean part is positive above height 7.** -/
theorem re_archimedean_pos {s : ℂ} (h0 : 0 < s.re) (h1 : s.re ≤ 1 / 2) (ht : 7 ≤ |s.im|) :
    0 < (1 / s + 1 / (s - 1) +
      (-(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma (s / 2))).re := by
  have ht2 : 49 ≤ s.im ^ 2 := by
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
  have hre_inv' : -1 / 50 ≤ (1 / (s - 1)).re := by
    rw [hre_inv, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ s.re by linarith) (show (0 : ℝ) ≤ 48 + s.re by linarith)]
  have hlogpi := log_pi_lt
  have hgam := eulerMascheroni_lt
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
  have hp : (1.799 : ℝ) ≤ (digamma (1 + s / 2) - digamma 1).re := hps.trans hpart
  linarith

end Speiser
