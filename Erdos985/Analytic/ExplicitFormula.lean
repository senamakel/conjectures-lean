import Erdos985.Analytic.ExplicitFormula.Identity
import Erdos985.Analytic.ExplicitFormula.Bounds
import Erdos985.Analytic.ExplicitFormula.ZeroSum

/-! # Assembly of Bach's non-principal bound (see `ExplicitFormula/Basic.lean` for the plan) -/

namespace Erdos985.Analytic

open Complex ArithmeticFunction MeasureTheory
open scoped Classical

variable {N : ℕ} [NeZero N]

/-! ### Step D: assembly -/

/-- MTT Lemma 1, non-principal part: the statement of `Erdos985.bach_nonprincipal`. -/
theorem bach_nonprincipal_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (x : ℕ) (hx : 1 ≤ x) :
    ‖bachSum χ x‖ ≤ bachC p x * √x * Real.log p := by
  have hp := (Fact.out : p.Prime)
  -- a non-trivial character mod a prime is primitive
  have hprim : χ.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def]
    rcases (Nat.dvd_prime hp).1 (DirichletCharacter.conductor_dvd_level χ) with h | h
    · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h) hχ
    · exact h
  set Λc := DirichletCharacter.completedLFunction χ
  set m : {ρ : ℂ // Λc ρ = 0} → ℝ := fun ρ => (analyticOrderNatAt Λc ρ : ℝ)
  set A : ℝ := √(x : ℝ) + 2 + 3 / x
  obtain ⟨hsum, hZ⟩ := zeroSum_le hGRH hprim hχ
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hA0 : 0 ≤ A := by positivity
  -- each zero term
  have hterm : ∀ ρ : {ρ : ℂ // Λc ρ = 0},
      ‖(analyticOrderNatAt Λc ρ : ℂ) * zeroTerm x ρ‖ ≤ A * (m ρ / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) := by
    intro ρ
    rw [norm_mul, Complex.norm_natCast]
    have h := norm_zeroTerm_le x hx (completedLFunction_zero_re hGRH hprim hχ ρ.2)
    calc (analyticOrderNatAt Λc ρ : ℝ) * ‖zeroTerm x ρ‖
        ≤ (analyticOrderNatAt Λc ρ : ℝ) * (A / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = A * (m ρ / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) := by simp only [m]; ring
  have hsumA : Summable fun ρ : {ρ : ℂ // Λc ρ = 0} =>
      A * (m ρ / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) := hsum.mul_left A
  have hZnorm : ‖∑' ρ : {ρ : ℂ // Λc ρ = 0}, (analyticOrderNatAt Λc ρ : ℂ) * zeroTerm x ρ‖
      ≤ A * ((2 / 3) * (Real.log p + 5 / 3)) := by
    have hs : Summable fun ρ : {ρ : ℂ // Λc ρ = 0} =>
        ‖(analyticOrderNatAt Λc ρ : ℂ) * zeroTerm x ρ‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumA
    calc _ ≤ ∑' ρ : {ρ : ℂ // Λc ρ = 0}, ‖(analyticOrderNatAt Λc ρ : ℂ) * zeroTerm x ρ‖ :=
          norm_tsum_le_tsum_norm hs
      _ ≤ ∑' ρ : {ρ : ℂ // Λc ρ = 0}, A * (m ρ / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) :=
          hs.tsum_le_tsum hterm hsumA
      _ = A * ∑' ρ : {ρ : ℂ // Λc ρ = 0}, m ρ / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ := tsum_mul_left
      _ ≤ A * ((2 / 3) * (Real.log p + 5 / 3)) := mul_le_mul_of_nonneg_left hZ hA0
  have hG := norm_gammaPart_le χ x hx
  have hL := norm_logDeriv_LFunction_two_le χ
  have hfac : ‖(1 - 1 / (x : ℂ))‖ ≤ 1 := by
    have : (1 - 1 / (x : ℂ)) = ((1 - 1 / (x : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h1 : 0 < 1 / (x : ℝ) := by positivity
    have h2 : 1 / (x : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hxR
    constructor <;> linarith
  have hlast : ‖(1 - 1 / (x : ℂ)) * (deriv (DirichletCharacter.LFunction χ) 2
      / DirichletCharacter.LFunction χ 2)‖ ≤ 0.6 := by
    rw [norm_mul]
    calc _ ≤ 1 * 0.6 := mul_le_mul hfac hL (norm_nonneg _) zero_le_one
      _ = 0.6 := one_mul _
  have htotal : ‖bachSum χ x‖ ≤ A * ((2 / 3) * (Real.log p + 5 / 3)) + (Real.log x + 1) + 0.6 := by
    rw [explicit_formula hprim hχ x hx]
    calc _ ≤ ‖(∑' ρ : {ρ : ℂ // Λc ρ = 0}, (analyticOrderNatAt Λc ρ : ℂ) * zeroTerm x ρ)
              + gammaPart χ x‖ + ‖(1 - 1 / (x : ℂ)) * (deriv (DirichletCharacter.LFunction χ) 2
                / DirichletCharacter.LFunction χ 2)‖ := norm_sub_le _ _
      _ ≤ (‖∑' ρ : {ρ : ℂ // Λc ρ = 0}, (analyticOrderNatAt Λc ρ : ℂ) * zeroTerm x ρ‖
              + ‖gammaPart χ x‖) + 0.6 := add_le_add (norm_add_le _ _) hlast
      _ ≤ _ := by linarith
  -- identify the right-hand side
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hsx : 0 < √(x : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hx32 : (x : ℝ) ^ (3 / 2 : ℝ) = x * √(x : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hRHS : bachC p x * √x * Real.log p
      = A * ((2 / 3) * (Real.log p + 5 / 3)) + (Real.log x + 2) := by
    simp only [bachC, A]
    rw [hx32]
    have hx0 : (x : ℝ) ≠ 0 := by positivity
    have hs0 : √(x : ℝ) ≠ 0 := hsx.ne'
    have hl0 : Real.log p ≠ 0 := hlogp.ne'
    field_simp
  rw [hRHS]
  linarith

end Erdos985.Analytic
