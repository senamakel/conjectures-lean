import LLS.Defs
import LLS.Analytic.Log.Identity

/-! # LLS Lemma 2.2: the log-weighted explicit formula for a primitive character, under GRH

The identity `S(x,χ) = −Σ_ρ m_ρ (x^ρ − 1)/ρ² − D(0, χ) log x + Γ̃(x)` is
`LLS.LogAux.log_explicit_formula` (`LLS/Analytic/Log/Identity.lean`); the gamma term is bounded
in `LLS/Analytic/Log/Gamma.lean`, the Perron and residue formulas for `x^s/s²` are in
`LLS/Analytic/Log/Perron.lean`. -/

namespace LLS

open Complex Erdos985 Erdos985.Analytic

variable {N : ℕ} [NeZero N]

/-- LLS Lemma 2.2 (upper bound for the real part), Mathlib normalisation:
`Re S(x, χ) ≤ (√x + 1) Σ m_ρ/|ρ|² + (log N + Re D(1, χ⁻¹)) log x − ½ log π · log x + Ẽ(x)`.
It comes from `S(x,χ) = −Σ_ρ m_ρ (x^ρ − 1)/ρ² − D(0, χ) log x + Γ̃(x)` and the functional
equation `−D(0, χ) = log N + D(1, χ⁻¹)`. -/
theorem re_logSum_le (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 1 ≤ x) :
    (logSum χ x).re ≤ (√(x : ℝ) + 1) * Z2 χ + (Real.log N + (D χ⁻¹ 1).re) * Real.log x
      - 1 / 2 * Real.log Real.pi * Real.log x + Etil x := by
  set Λf := DirichletCharacter.completedLFunction χ with hΛf
  obtain ⟨hS1, he⟩ := LogAux.log_explicit_formula hprim hχ x hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  obtain ⟨hsum_ε, -⟩ := hadamard_logDeriv (DirichletCharacter.differentiable_completedLFunction hχ)
    (completedLFunction_zero_ne_zero χ hχ hprim) (completedLFunction_growth χ hχ)
  have hsq : Summable fun ρ : {ρ : ℂ // Λf ρ = 0} =>
      (analyticOrderNatAt Λf ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2 := by
    refine (hsum_ε 1 one_pos).congr fun ρ => ?_
    norm_num <;> rfl
  /- the zero sum -/
  set Sz := ∑' ρ : {ρ : ℂ // Λf ρ = 0}, (analyticOrderNatAt Λf ρ : ℂ)
      * (((x : ℂ) ^ (ρ : ℂ) - 1) / (ρ : ℂ) ^ 2) with hSz
  have hterm : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, ‖(analyticOrderNatAt Λf ρ : ℂ)
      * (((x : ℂ) ^ (ρ : ℂ) - 1) / (ρ : ℂ) ^ 2)‖
        ≤ (√(x : ℝ) + 1) * ((analyticOrderNatAt Λf ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
    intro ρ
    have hre := completedLFunction_zero_re hGRH hprim hχ ρ.2
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => by rw [h] at hre; norm_num at hre
    have h1 : ‖(x : ℂ) ^ (ρ : ℂ) - 1‖ ≤ √(x : ℝ) + 1 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, show (x : ℂ) = ((x : ℝ) : ℂ) by simp, norm_cpow_eq_rpow_re_of_pos hx0, hre,
        Real.sqrt_eq_rpow]
    rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow]
    have hρp : 0 < ‖(ρ : ℂ)‖ ^ 2 := by have := norm_pos_iff.2 hρ0; positivity
    rw [mul_div_assoc', div_le_iff₀ hρp]
    calc (analyticOrderNatAt Λf ρ : ℝ) * ‖(x : ℂ) ^ (ρ : ℂ) - 1‖
        ≤ (analyticOrderNatAt Λf ρ : ℝ) * (√(x : ℝ) + 1) := by gcongr
      _ = _ := by rw [mul_assoc, div_mul_cancel₀ _ hρp.ne']; ring
  have hSzb : ‖Sz‖ ≤ (√(x : ℝ) + 1) * Z2 χ := by
    have hs : Summable fun ρ : {ρ : ℂ // Λf ρ = 0} => ‖(analyticOrderNatAt Λf ρ : ℂ)
        * (((x : ℂ) ^ (ρ : ℂ) - 1) / (ρ : ℂ) ^ 2)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hsq.mul_left _)
    calc ‖Sz‖ ≤ _ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' ρ : {ρ : ℂ // Λf ρ = 0}, (√(x : ℝ) + 1)
            * ((analyticOrderNatAt Λf ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) :=
          hs.tsum_le_tsum hterm (hsq.mul_left _)
      _ = (√(x : ℝ) + 1) * Z2 χ := by rw [tsum_mul_left]; rfl
  /- the functional equation at `s = 1` -/
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  have hs1 : DirichletCharacter.completedLFunction χ⁻¹ 1 ≠ 0 :=
    DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχi) (by simp)
  have hFE := ZeroSumAux.logDeriv_functional_equation hprim hχ hs1
  rw [sub_self] at hFE
  have hD0 : -(D χ 0) = (Real.log N : ℂ) + D χ⁻¹ 1 := hFE
  /- gamma part -/
  have hG := LogAux.re_lgammaPart_le χ x hx
  rw [he]
  have hre : (-Sz - D χ 0 * (Real.log x : ℂ)
      + (LogAux.lgammaPart χ x + gammaLogDeriv χ 2 * (Real.log x : ℂ))).re
      = (-Sz).re + (Real.log N + (D χ⁻¹ 1).re) * Real.log x
        + (LogAux.lgammaPart χ x + gammaLogDeriv χ 2 * (Real.log x : ℂ)).re := by
    have : -Sz - D χ 0 * (Real.log x : ℂ)
        + (LogAux.lgammaPart χ x + gammaLogDeriv χ 2 * (Real.log x : ℂ))
        = -Sz + (-(D χ 0)) * (Real.log x : ℂ)
          + (LogAux.lgammaPart χ x + gammaLogDeriv χ 2 * (Real.log x : ℂ)) := by ring
    rw [this, add_re, add_re, re_mul_ofReal, hD0, add_re, ofReal_re]
  rw [hre]
  have h1 : (-Sz).re ≤ (√(x : ℝ) + 1) * Z2 χ :=
    (re_le_norm _).trans ((norm_neg Sz).le.trans hSzb)
  linarith

end LLS
