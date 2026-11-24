import Density.ZeroCount.Xi

/-!
# Riemann–von Mangoldt upper bound `N(T) ≪ T log T`

Jensen's inequality for `ξ = xiZeta` on the discs `|s| ≤ r ⊂ |s| ≤ 2r`, centred at `0` where
`ξ(0) = 1`, with erdos-985's order-one growth `‖ξ s‖ ≤ C exp(C ‖s‖ log(‖s‖ + 2))`
(`Erdos985.Analytic.xiZeta_growth`), gives

* `zeroCountOn_xiZeta_le`: at most `A r log (r + 2)` zeros of `ξ` in `|s| ≤ r`, `r ≥ 1`;
* `zeroCountOn_riemannZeta_le_of_subset_strip`: at most `C T log T` zeros of `ζ`, with
  multiplicity, in any set inside `0 ≤ Re s ≤ 1`, `|Im s| ≤ T`, for `T ≥ 2`.

The constants are not explicit: they come from the (non-explicit) constant of `xiZeta_growth`.
-/

open Complex Metric Set

namespace Density

open Erdos985.Analytic

/-- Zeros of `ξ` in a disc of radius `r ≥ 1` around `0`: at most `A r log (r + 2)`. -/
theorem zeroCountOn_xiZeta_le :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 1 ≤ r → ∀ S : Set ℂ, S ⊆ closedBall 0 r →
      (zeroCountOn xiZeta S : ℝ) ≤ A * r * Real.log (r + 2) := by
  obtain ⟨C, hC⟩ := xiZeta_growth
  set C₀ := max C 1
  have hC₀ : 1 ≤ C₀ := le_max_right _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Real.log C₀ + 4 * C₀) / Real.log 2,
    div_pos (by have := Real.log_nonneg hC₀; linarith) hlog2, fun r hr S hS => ?_⟩
  have hr0 : 0 < r := by linarith
  set L := Real.log (2 * r + 2)
  set M := C₀ * Real.exp (C₀ * (2 * r) * L)
  have hL : 1 ≤ L := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hM : 1 ≤ M := by
    have : 1 ≤ Real.exp (C₀ * (2 * r) * L) := Real.one_le_exp (by positivity)
    nlinarith
  have hb : ∀ z ∈ sphere (0 : ℂ) (2 * r), ‖xiZeta z‖ ≤ M := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    refine (hC z).trans ?_
    rw [hz]
    have hCC : C ≤ C₀ := le_max_left _ _
    have h1 : C * (2 * r) * Real.log (2 * r + 2) ≤ C₀ * (2 * r) * L := by
      have : 0 ≤ Real.log (2 * r + 2) := by linarith
      gcongr
    calc C * Real.exp (C * (2 * r) * Real.log (2 * r + 2))
        ≤ C₀ * Real.exp (C * (2 * r) * Real.log (2 * r + 2)) := by gcongr
      _ ≤ M := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) (by linarith)
  have J := zeroCountOn_le_of_jensen (f := xiZeta) (c := 0) hr0 (by linarith : r < 2 * r) hM
    (fun z _ => analyticAt_xiZeta z) (by rw [xiZeta_zero]; exact one_ne_zero) hb hS
  rw [xiZeta_zero, norm_one, div_one, show 2 * r / r = 2 by field_simp] at J
  refine J.trans ?_
  rw [div_le_iff₀ hlog2]
  have hlogM : Real.log M = Real.log C₀ + C₀ * (2 * r) * L := by
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  have hLr : L ≤ Real.log (r + 2) + Real.log 2 := by
    rw [← Real.log_mul (by linarith) (by norm_num)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hr2 : 1 ≤ r * Real.log (r + 2) := by
    have : 1 ≤ Real.log (r + 2) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith [Real.exp_one_lt_d9]
    nlinarith
  have hl0 := Real.log_nonneg hC₀
  have hlog2' : Real.log 2 ≤ Real.log (r + 2) := Real.log_le_log (by norm_num) (by linarith)
  have e : (Real.log C₀ + 4 * C₀) / Real.log 2 * r * Real.log (r + 2) * Real.log 2
      = (Real.log C₀ + 4 * C₀) * (r * Real.log (r + 2)) := by
    field_simp
  rw [e, hlogM]
  have hL2 : L ≤ 2 * Real.log (r + 2) := by linarith
  have : C₀ * (2 * r) * L ≤ 4 * C₀ * (r * Real.log (r + 2)) := by
    have := mul_le_mul_of_nonneg_left hL2 (by positivity : (0 : ℝ) ≤ C₀ * (2 * r))
    linarith
  nlinarith

/-- **Riemann–von Mangoldt upper bound.** The zeros of `ζ`, counted with multiplicity, in any
set inside the closed critical strip `0 ≤ Re s ≤ 1`, `|Im s| ≤ T`, number at most `C T log T`
for `T ≥ 2`. -/
theorem zeroCountOn_riemannZeta_le_of_subset_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ S : Set ℂ,
      S ⊆ {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T} →
      (zeroCountOn riemannZeta S : ℝ) ≤ C * T * Real.log T := by
  obtain ⟨A, hA, hcount⟩ := zeroCountOn_xiZeta_le
  refine ⟨9 / 2 * A, by positivity, fun T hT S hS => ?_⟩
  have hball : S ⊆ closedBall 0 (T + 1) := by
    intro s hs
    obtain ⟨h0, h1, hT'⟩ := hS hs
    rw [mem_closedBall_zero_iff]
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 1 + T := by rw [abs_of_nonneg h0]; linarith
      _ = T + 1 := by ring
  rw [zeroCountOn_riemannZeta_eq_xiZeta fun s hs => by linarith [(hS hs).1]]
  refine (hcount (T + 1) (by linarith) S hball).trans ?_
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlog3 : Real.log (T + 1 + 2) ≤ 3 * Real.log T := by
    rw [← Real.log_rpow (by linarith)]
    refine Real.log_le_log (by linarith) ?_
    norm_num
    nlinarith [mul_le_mul hT hT (by norm_num) (by linarith : (0:ℝ) ≤ T)]
  calc A * (T + 1) * Real.log (T + 1 + 2) ≤ A * (3 / 2 * T) * (3 * Real.log T) := by
        gcongr
        · exact Real.log_nonneg (by linarith)
        · linarith
    _ = 9 / 2 * A * T * Real.log T := by ring

end Density
