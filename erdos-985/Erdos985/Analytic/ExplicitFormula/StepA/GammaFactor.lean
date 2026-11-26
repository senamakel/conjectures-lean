import Erdos985.Analytic.ExplicitFormula.Basic

/-!
# Derivative of the archimedean gamma factor
-/

namespace Erdos985.Analytic.StepAAux

open Complex

theorem hasDerivAt_Gamma_digamma {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt Gamma (Gamma w * digamma w) w := by
  have hd : DifferentiableAt ℂ Gamma w := differentiableAt_Gamma w fun m h => by
    rw [h] at hw; simp at hw; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  convert hd.hasDerivAt using 1
  rw [digamma_def, logDeriv_apply, mul_div_cancel₀ _ (Gamma_ne_zero_of_re_pos hw)]

theorem hasDerivAt_Gammaℝ {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt Gammaℝ (Gammaℝ w * (-(1 / 2) * (Real.log Real.pi : ℂ)
      + (1 / 2) * digamma (w / 2))) w := by
  have h1 : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) w := by
    simpa using ((hasDerivAt_id w).neg.div_const 2)
  have h2 := h1.const_cpow (c := (Real.pi : ℂ)) (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have h3 : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) w := by
    simpa using (hasDerivAt_id w).div_const 2
  have hw2 : 0 < (w / 2).re := by simp; linarith
  have h4 := (hasDerivAt_Gamma_digamma hw2).comp w h3
  have h5 := h2.mul h4
  have hlog : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (ofReal_log Real.pi_pos.le).symm
  convert h5 using 1
  · rfl
  · rw [hlog, Gammaℝ_def]; simp only [Function.comp_apply]; ring

variable {N : ℕ}

theorem hasDerivAt_gammaFactor (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (DirichletCharacter.gammaFactor χ)
      (DirichletCharacter.gammaFactor χ s * gammaLogDeriv χ s) s := by
  classical
  by_cases he : χ.Even
  · have hfun : DirichletCharacter.gammaFactor χ = Gammaℝ := funext he.gammaFactor_def
    rw [hfun]
    convert hasDerivAt_Gammaℝ hs using 2
    simp [gammaLogDeriv, parity, he]
  · have hfun : DirichletCharacter.gammaFactor χ = fun z => Gammaℝ (z + 1) := by
      funext z; simp [DirichletCharacter.gammaFactor, he]
    rw [hfun]
    have h := (hasDerivAt_Gammaℝ (w := s + 1) (by simp; linarith)).comp s
      ((hasDerivAt_id s).add_const 1)
    convert h using 1
    · rfl
    · simp [gammaLogDeriv, parity, he]

theorem gammaFactor_ne_zero (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  classical
  by_cases he : χ.Even
  · rw [he.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
  · simp only [DirichletCharacter.gammaFactor, he, ite_false]
    exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

end Erdos985.Analytic.StepAAux
