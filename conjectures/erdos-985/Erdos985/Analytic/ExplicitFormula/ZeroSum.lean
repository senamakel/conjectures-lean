import Erdos985.Analytic.ExplicitFormula.StepA
import Erdos985.Analytic.ExplicitFormula.ZeroSum.Bounds
import Erdos985.Analytic.ExplicitFormula.ZeroSum.FuncEq
import Erdos985.Analytic.XiGrowth

namespace Erdos985.Analytic

open Complex ArithmeticFunction MeasureTheory
open scoped Classical

variable {N : ℕ} [NeZero N]

/-- Hadamard at `s = 3/2` plus the functional equation, under GRH. -/
theorem zeroSum_le (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0} =>
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)
          / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) ∧
    ∑' ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0},
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)
          / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖
      ≤ (2 / 3) * (Real.log N + 5 / 3) := by
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  obtain ⟨-, b, H⟩ := hadamard_logDeriv (DirichletCharacter.differentiable_completedLFunction hχ)
    (completedLFunction_zero_ne_zero χ hχ hprim) (completedLFunction_growth χ hχ)
  set f := DirichletCharacter.completedLFunction χ with hf
  set fi := DirichletCharacter.completedLFunction χ⁻¹ with hfi
  set x : ℝ := 3 / 2 with hx
  have hs0 : f x ≠ 0 :=
    DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp [hx]; norm_num)
  have hsi : fi x ≠ 0 :=
    DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχi)
      (by simp [hx]; norm_num)
  have hs1 : f (1 - x) ≠ 0 := fun h => hsi (completedLFunction_inv_eq_zero hprim h)
  obtain ⟨sA, eA⟩ := H x hs0
  obtain ⟨sB, eB⟩ := H (1 - x) hs1
  set m : {ρ : ℂ // f ρ = 0} → ℕ := fun ρ => analyticOrderNatAt f ρ with hm
  -- the real series `r ρ = m ρ · Re 1/(x − ρ)`
  set r : {ρ : ℂ // f ρ = 0} → ℝ := fun ρ => (m ρ : ℝ) * (1 / ((x : ℂ) - ρ)).re with hr
  have hd := sA.hasSum.sub sB.hasSum
  have hdre := Complex.reCLM.hasSum hd
  have hcrit : ∀ ρ : {ρ : ℂ // f ρ = 0}, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => completedLFunction_zero_re hGRH hprim hχ ρ.2
  have hterm : ∀ ρ : {ρ : ℂ // f ρ = 0},
      Complex.reCLM ((analyticOrderNatAt f ρ : ℂ) * (1 / ((x : ℂ) - ρ) + 1 / ρ)
        - (analyticOrderNatAt f ρ : ℂ) * (1 / ((1 : ℂ) - x - ρ) + 1 / ρ)) = 2 * r ρ := by
    intro ρ
    have := ZeroSumAux.re_inv_reflect (hcrit ρ) x
    simp only [Complex.reCLM_apply, sub_re, mul_re, add_re, natCast_re, natCast_im, zero_mul,
      sub_zero, hr, hm]
    rw [this]; ring
  simp only [hterm] at hdre
  have hrsum : HasSum r ((Complex.reCLM (∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / ((x : ℂ) - ρ) + 1 / ρ)
      - ∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / ((1 : ℂ) - x - ρ) + 1 / ρ))) / 2) := by
    have := hdre.div_const 2
    simpa using this
  -- evaluate the sum
  have hval : Complex.reCLM (∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / ((x : ℂ) - ρ) + 1 / ρ)
      - ∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / ((1 : ℂ) - x - ρ) + 1 / ρ))
      = (deriv f x / f x).re + Real.log N + (deriv fi x / fi x).re := by
    have hFE := ZeroSumAux.logDeriv_functional_equation hprim hχ (s := x) hsi
    have e : ∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / ((x : ℂ) - ρ) + 1 / ρ)
      - ∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / ((1 : ℂ) - x - ρ) + 1 / ρ)
        = deriv f x / f x + (Real.log N + deriv fi x / fi x) := by
      rw [← hFE, eA, eB]; ring
    rw [e]
    simp only [Complex.reCLM_apply, add_re, ofReal_re]
    ring
  rw [hval] at hrsum
  have hB := ZeroSumAux.re_logDeriv_completed_three_halves_le hχ
  have hBi := ZeroSumAux.re_logDeriv_completed_three_halves_le hχi
  have hx' : ((x : ℝ) : ℂ) = 3 / 2 := by simp [hx]
  rw [hx'] at hrsum
  -- comparison
  have hcmp : ∀ ρ : {ρ : ℂ // f ρ = 0},
      (analyticOrderNatAt f ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ ≤ (4 / 3) * r ρ := by
    intro ρ
    have h := ZeroSumAux.inv_norm_mul_le (hcrit ρ)
    simp only [hr, hm, hx']
    rw [div_eq_mul_one_div]
    have : (0 : ℝ) ≤ analyticOrderNatAt f ρ := Nat.cast_nonneg _
    nlinarith
  have hnn : ∀ ρ : {ρ : ℂ // f ρ = 0},
      0 ≤ (analyticOrderNatAt f ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ :=
    fun ρ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hsum4 := hrsum.mul_left (4 / 3)
  have hS : Summable (fun ρ : {ρ : ℂ // f ρ = 0} =>
      (analyticOrderNatAt f ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) :=
    Summable.of_nonneg_of_le hnn hcmp hsum4.summable
  refine ⟨hS, ?_⟩
  have hle := hS.tsum_le_tsum hcmp hsum4.summable
  rw [hsum4.tsum_eq] at hle
  have hpi := ZeroSumAux.log_pi_gt
  linarith
end Erdos985.Analytic
