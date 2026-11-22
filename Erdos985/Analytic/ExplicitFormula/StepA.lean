import Erdos985.Analytic.ExplicitFormula.StepA.GammaFactor

namespace Erdos985.Analytic

open Complex ArithmeticFunction MeasureTheory
open scoped Classical

variable {N : ℕ} [NeZero N]

/-! ### Step A: zeros, log-derivatives -/

/-- A zero of `Λ(·, χ)` at `1 - s` is a zero of `Λ(·, χ⁻¹)` at `s`. -/
theorem completedLFunction_inv_eq_zero {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive)
    {s : ℂ} (hs : DirichletCharacter.completedLFunction χ (1 - s) = 0) :
    DirichletCharacter.completedLFunction χ⁻¹ s = 0 := by
  rw [hprim.completedLFunction_one_sub] at hs
  rcases mul_eq_zero.mp hs with h | h
  · exfalso
    rcases mul_eq_zero.mp h with h | h
    · rw [cpow_eq_zero_iff] at h
      exact NeZero.ne N (by exact_mod_cast h.1)
    · exact DirichletCharacter.rootNumber_ne_zero hprim h
  · exact h

/-- Unconditionally, zeros of the completed L-function lie in the open strip `0 < Re s < 1`. -/
theorem completedLFunction_zero_re_mem {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) {ρ : ℂ} (hρ : DirichletCharacter.completedLFunction χ ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    push Not at h
    have h1 : DirichletCharacter.completedLFunction χ (1 - (1 - ρ)) = 0 := by simpa using hρ
    exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ⁻¹
      (Or.inl (by simpa using hχ)) (by simp; linarith) (completedLFunction_inv_eq_zero hprim h1)
  · by_contra h
    push Not at h
    exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hρ

/-- At a zero of `Λ` (away from `s = 0`) the L-function vanishes. -/
theorem LFunction_eq_zero_of_completed {χ : DirichletCharacter ℂ N} {s : ℂ} (hs : s ≠ 0)
    (h : DirichletCharacter.completedLFunction χ s = 0) : DirichletCharacter.LFunction χ s = 0 := by
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs), h, zero_div]

/-- Under GRH every zero of the completed L-function lies on `Re s = 1/2`. -/
theorem completedLFunction_zero_re (hGRH : DirichletLNonvanishingRightOfHalf)
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.completedLFunction χ ρ = 0) : ρ.re = 1 / 2 := by
  rcases lt_trichotomy ρ.re (1 / 2) with h | h | h
  · exfalso
    have h1 : DirichletCharacter.completedLFunction χ (1 - (1 - ρ)) = 0 := by simpa using hρ
    have h2 := completedLFunction_inv_eq_zero hprim h1
    have hne : (1 - ρ) ≠ 0 := fun h' => by
      have := congrArg Complex.re h'; simp at this; linarith
    exact hGRH N χ⁻¹ (1 - ρ) (by simp; linarith) (Or.inl (by simpa using hχ))
      (LFunction_eq_zero_of_completed hne h2)
  · exact h
  · exfalso
    have hne : ρ ≠ 0 := fun h' => by rw [h'] at h; simp at h; linarith
    exact hGRH N χ ρ h (Or.inl hχ) (LFunction_eq_zero_of_completed hne hρ)

/-- `L'/L = Λ'/Λ − G` to the right of `Re s = 1`. -/
theorem logDeriv_LFunction_eq {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
      = deriv (DirichletCharacter.completedLFunction χ) s
          / DirichletCharacter.completedLFunction χ s - gammaLogDeriv χ s := by
  have hs0 : 0 < s.re := by linarith
  have hL : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le
  have hγ := StepAAux.gammaFactor_ne_zero χ hs0
  have hev : DirichletCharacter.completedLFunction χ =ᶠ[nhds s]
      fun w => DirichletCharacter.gammaFactor χ w * DirichletCharacter.LFunction χ w := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show s ∈ {w : ℂ | 0 < w.re} from hs0)] with w hw
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ w
      (Or.inl fun h => by rw [h] at hw; simp at hw),
      mul_div_cancel₀ _ (StepAAux.gammaFactor_ne_zero χ hw)]
  have hd : HasDerivAt (fun w => DirichletCharacter.gammaFactor χ w * DirichletCharacter.LFunction χ w) _ s :=
    (StepAAux.hasDerivAt_gammaFactor χ hs0).mul
    (DirichletCharacter.differentiableAt_LFunction χ s (Or.inr hχ)).hasDerivAt
  rw [hev.deriv_eq, hd.deriv, hev.eq_of_nhds]
  field_simp
  ring

end Erdos985.Analytic
