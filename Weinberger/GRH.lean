import Erdos985.Analytic.ExplicitFormula

/-!
# Bach's non-principal bound for any primitive character

`Erdos985.Analytic.bach_nonprincipal_of_GRH` is stated for characters mod a prime `p`. Its proof
only uses that the character is primitive and non-trivial, so the same steps (the explicit
formula `explicit_formula`, the GRH zero sum `zeroSum_le`, the Gamma part and `L'/L(2)`) give
the bound for a primitive character of any modulus `N`, with `log N` in place of `log p`.
-/

namespace Weinberger

open Complex ArithmeticFunction Erdos985 Erdos985.Analytic
open scoped Classical

theorem bach_primitive_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 1 ≤ x) :
    ‖bachSum χ x‖ ≤ (√(x : ℝ) + 2 + 3 / x) * ((2 / 3) * (Real.log N + 5 / 3))
      + (Real.log x + 1) + 0.6 := by
  set Λc := DirichletCharacter.completedLFunction χ
  set m : {ρ : ℂ // Λc ρ = 0} → ℝ := fun ρ => (analyticOrderNatAt Λc ρ : ℝ)
  set A : ℝ := √(x : ℝ) + 2 + 3 / x
  obtain ⟨hsum, hZ⟩ := zeroSum_le hGRH hprim hχ
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hA0 : 0 ≤ A := by positivity
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
      ≤ A * ((2 / 3) * (Real.log N + 5 / 3)) := by
    have hs : Summable fun ρ : {ρ : ℂ // Λc ρ = 0} =>
        ‖(analyticOrderNatAt Λc ρ : ℂ) * zeroTerm x ρ‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumA
    calc _ ≤ ∑' ρ : {ρ : ℂ // Λc ρ = 0}, ‖(analyticOrderNatAt Λc ρ : ℂ) * zeroTerm x ρ‖ :=
          norm_tsum_le_tsum_norm hs
      _ ≤ ∑' ρ : {ρ : ℂ // Λc ρ = 0}, A * (m ρ / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) :=
          hs.tsum_le_tsum hterm hsumA
      _ = A * ∑' ρ : {ρ : ℂ // Λc ρ = 0}, m ρ / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ := tsum_mul_left
      _ ≤ A * ((2 / 3) * (Real.log N + 5 / 3)) := mul_le_mul_of_nonneg_left hZ hA0
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
  rw [explicit_formula hprim hχ x hx]
  calc _ ≤ ‖(∑' ρ : {ρ : ℂ // Λc ρ = 0}, (analyticOrderNatAt Λc ρ : ℂ) * zeroTerm x ρ)
            + gammaPart χ x‖ + ‖(1 - 1 / (x : ℂ)) * (deriv (DirichletCharacter.LFunction χ) 2
              / DirichletCharacter.LFunction χ 2)‖ := norm_sub_le _ _
    _ ≤ (‖∑' ρ : {ρ : ℂ // Λc ρ = 0}, (analyticOrderNatAt Λc ρ : ℂ) * zeroTerm x ρ‖
            + ‖gammaPart χ x‖) + 0.6 := add_le_add (norm_add_le _ _) hlast
    _ ≤ _ := by linarith

end Weinberger
