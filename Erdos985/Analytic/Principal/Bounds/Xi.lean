import Erdos985.Analytic.XiGrowth
import Erdos985.Analytic.Hadamard
import Erdos985.Statement
import Erdos985.Analytic.Principal.Bounds.Numerics

/-!
# RH for `ξ` from GRH, and the zero sum `Σ m/|ρ(ρ+1)| ≤ 2 + γ − log 4π < 1/20`
-/

open Complex

namespace Erdos985.Analytic.PrincipalAux

theorem xiZeta_one : xiZeta 1 = 1 := by simp [xiZeta]

theorem xiZeta_one_sub (s : ℂ) : xiZeta (1 - s) = xiZeta s := by
  simp only [xiZeta, completedRiemannZeta₀_one_sub]
  ring

theorem hasDerivAt_xiZeta (s : ℂ) :
    HasDerivAt xiZeta ((1 * (s - 1) + s * 1) * completedRiemannZeta₀ s
      + s * (s - 1) * deriv completedRiemannZeta₀ s) s := by
  have h := (((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).mul
    (differentiable_completedZeta₀ s).hasDerivAt).add_const 1
  exact h

theorem deriv_xiZeta_zero : deriv xiZeta 0 = -completedRiemannZeta₀ 0 := by
  rw [(hasDerivAt_xiZeta 0).deriv]; ring

theorem deriv_xiZeta_one : deriv xiZeta 1 = completedRiemannZeta₀ 1 := by
  rw [(hasDerivAt_xiZeta 1).deriv]; ring

/-- Under GRH, `ξ` has no zeros with `Re s > 1/2`. -/
theorem xiZeta_ne_zero_of_half_lt (hGRH : DirichletLNonvanishingRightOfHalf) {s : ℂ}
    (hs : 1 / 2 < s.re) : xiZeta s ≠ 0 := by
  intro h
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs1 : s ≠ 1 := by rintro rfl; rw [xiZeta_one] at h; norm_num at h
  rw [xiZeta_eq hs0 hs1] at h
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hΛ : completedRiemannZeta s = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hs0
      · exact absurd h hs1'
    · exact h
  have hζ : riemannZeta s = 0 := by rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  have := hGRH 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)
  rw [DirichletCharacter.LFunction_modOne_eq] at this
  exact this hζ

theorem xiZeta_zero_re' (hGRH : DirichletLNonvanishingRightOfHalf) {ρ : ℂ} (hρ : xiZeta ρ = 0) :
    ρ.re = 1 / 2 := by
  have h1 : ¬ 1 / 2 < ρ.re := fun h => xiZeta_ne_zero_of_half_lt hGRH h hρ
  have h2 : ¬ 1 / 2 < (1 - ρ).re := fun h =>
    xiZeta_ne_zero_of_half_lt hGRH h (by rw [xiZeta_one_sub]; exact hρ)
  simp only [sub_re, one_re] at h2
  linarith

/-- For `Re ρ = 1/2`: `Re (1/(1−ρ) + 1/ρ) = 1/|ρ|²` and `1/|ρ(ρ+1)| ≤` that. -/
theorem inv_norm_mul_le_re {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    1 / ‖ρ * (ρ + 1)‖ ≤ (1 / (1 - ρ) + 1 / ρ).re := by
  obtain ⟨a, γ⟩ := ρ
  simp only at hρ
  subst hρ
  have hre : (1 / (1 - (⟨1 / 2, γ⟩ : ℂ)) + 1 / ⟨1 / 2, γ⟩).re = 1 / (1 / 4 + γ ^ 2) := by
    simp [normSq_apply]
    field_simp
    ring
  rw [hre]
  set t := ‖(⟨1 / 2, γ⟩ : ℂ) * (⟨1 / 2, γ⟩ + 1)‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have hsq : t ^ 2 = (1 / 4 + γ ^ 2) * (9 / 4 + γ ^ 2) := by
    rw [ht, ← normSq_eq_norm_sq, normSq_mul]
    simp [normSq_apply]
    ring
  have hpos : 0 < 1 / 4 + γ ^ 2 := by positivity
  have hlow : 1 / 4 + γ ^ 2 ≤ t := by
    have h1 : (1 / 4 + γ ^ 2) ^ 2 ≤ t ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg γ]
    nlinarith [sq_nonneg γ]
  exact one_div_le_one_div_of_le hpos hlow

theorem re_two_completedRiemannZeta₀_one :
    (2 * completedRiemannZeta₀ 1).re = 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
  rw [completedRiemannZeta₀_one]
  have e : Complex.log (4 * (Real.pi : ℂ)) = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
  rw [e]
  simp
  ring

theorem zeroSum_zeta_le' (hGRH : DirichletLNonvanishingRightOfHalf) :
    Summable (fun ρ : {ρ : ℂ // xiZeta ρ = 0} =>
        (analyticOrderNatAt xiZeta ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) ∧
    ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖
      ≤ 1 / 20 := by
  have hx0 : xiZeta 0 ≠ 0 := by rw [xiZeta_zero]; norm_num
  have hx1 : xiZeta 1 ≠ 0 := by rw [xiZeta_one]; norm_num
  obtain ⟨-, b, H⟩ := hadamard_logDeriv differentiable_xiZeta hx0 xiZeta_growth
  obtain ⟨-, e0⟩ := H 0 hx0
  obtain ⟨s1, e1⟩ := H 1 hx1
  have hz : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0},
      (analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (0 - (ρ : ℂ)) + 1 / ρ) = 0 := by
    intro ρ; simp
  simp only [hz, tsum_zero, add_zero, deriv_xiZeta_zero, xiZeta_zero, div_one] at e0
  rw [deriv_xiZeta_one, xiZeta_one, div_one] at e1
  set T := ∑' ρ : {ρ : ℂ // xiZeta ρ = 0},
    (analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (1 - (ρ : ℂ)) + 1 / ρ) with hT
  have hTv : T = 2 * completedRiemannZeta₀ 1 := by
    have h01 : completedRiemannZeta₀ 0 = completedRiemannZeta₀ 1 := by
      rw [← completedRiemannZeta₀_one_sub]; norm_num
    rw [h01] at e0
    linear_combination e0 - e1
  have hre := Complex.reCLM.hasSum s1.hasSum
  rw [← hT, hTv] at hre
  simp only [Complex.reCLM_apply, re_two_completedRiemannZeta₀_one] at hre
  have hcmp : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0},
      (analyticOrderNatAt xiZeta ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ ≤
        ((analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (1 - (ρ : ℂ)) + 1 / ρ)).re := by
    intro ρ
    have h := inv_norm_mul_le_re (xiZeta_zero_re' hGRH ρ.2)
    simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
  have hnn : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0},
      0 ≤ (analyticOrderNatAt xiZeta ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ :=
    fun ρ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hS := Summable.of_nonneg_of_le hnn hcmp hre.summable
  refine ⟨hS, ?_⟩
  have hle := hS.tsum_le_tsum hcmp hre.summable
  rw [hre.tsum_eq] at hle
  linarith [two_add_gamma_sub_log_lt]

end Erdos985.Analytic.PrincipalAux
