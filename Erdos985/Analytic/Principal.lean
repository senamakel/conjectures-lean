import Erdos985.Analytic.Principal.Identity
import Erdos985.Analytic.Principal.Bounds

/-! # Assembly of Bach's principal bound -/

namespace Erdos985.Analytic

open Complex ArithmeticFunction

/-- MTT Lemma 1, principal part: the statement of `Erdos985.bach_principal`. -/
theorem bach_principal_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) (x : ℕ) (hx : 1 ≤ x) :
    |∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) - x / 2| ≤ √x / 20 + 3 := by
  set S : ℝ := ∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x)
  set Z : ℂ := ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℂ) * zeroTerm x ρ
  set Γp := gammaPart (1 : DirichletCharacter ℂ 1) x
  set L2 := deriv riemannZeta 2 / riemannZeta 2
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hid := explicit_formula_zeta x hx
  -- real parts
  have hre : S = Z.re + Γp.re + ((x : ℝ) / 2 + Real.log x - 7 / 2 + 3 / x)
      - (1 - 1 / (x : ℝ)) * L2.re := by
    have := congrArg Complex.re hid
    simp only [Complex.ofReal_re] at this
    refine this.trans ?_
    have hL2 : L2.im = 0 := (logDeriv_zeta_two_bound).1
    have e1 : (1 - 1 / (x : ℂ)) = ((1 - 1 / (x : ℝ) : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((x : ℂ) / 2 + (Real.log x : ℂ) - 7 / 2 + 3 / (x : ℂ))
        = (((x : ℝ) / 2 + Real.log x - 7 / 2 + 3 / x : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, Complex.sub_re, Complex.add_re, Complex.add_re, Complex.ofReal_re,
      Complex.re_ofReal_mul]
  -- zero part
  obtain ⟨hsum, hZ⟩ := zeroSum_zeta_le hGRH
  set A : ℝ := √(x : ℝ) + 2 + 3 / x
  have hA0 : 0 ≤ A := by positivity
  have hterm : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0},
      ‖(analyticOrderNatAt xiZeta ρ : ℂ) * zeroTerm x ρ‖
        ≤ A * ((analyticOrderNatAt xiZeta ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) := by
    intro ρ
    rw [norm_mul, Complex.norm_natCast]
    have h := norm_zeroTerm_le x hx (xiZeta_zero_re hGRH ρ.2)
    calc (analyticOrderNatAt xiZeta ρ : ℝ) * ‖zeroTerm x ρ‖
        ≤ (analyticOrderNatAt xiZeta ρ : ℝ) * (A / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring
  have hsumA := hsum.mul_left A
  have hs : Summable fun ρ : {ρ : ℂ // xiZeta ρ = 0} =>
      ‖(analyticOrderNatAt xiZeta ρ : ℂ) * zeroTerm x ρ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumA
  have hZn : ‖Z‖ ≤ A * (1 / 20) := by
    calc ‖Z‖ ≤ ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, ‖(analyticOrderNatAt xiZeta ρ : ℂ) * zeroTerm x ρ‖ :=
          norm_tsum_le_tsum_norm hs
      _ ≤ ∑' ρ : {ρ : ℂ // xiZeta ρ = 0},
            A * ((analyticOrderNatAt xiZeta ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) :=
          hs.tsum_le_tsum hterm hsumA
      _ = A * ∑' ρ : {ρ : ℂ // xiZeta ρ = 0},
            (analyticOrderNatAt xiZeta ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ := tsum_mul_left
      _ ≤ A * (1 / 20) := mul_le_mul_of_nonneg_left hZ hA0
  have hZre : |Z.re| ≤ A * (1 / 20) := (Complex.abs_re_le_norm Z).trans hZn
  -- the other terms
  obtain ⟨-, hg1, hg2⟩ := gammaPart_one_bound x hx
  obtain ⟨-, hl1, hl2⟩ := logDeriv_zeta_two_bound
  have hf0 : 0 ≤ 1 - 1 / (x : ℝ) := by
    have : 1 / (x : ℝ) ≤ 1 := by rw [div_le_one hx0]; exact hxR
    linarith
  have hf1 : 1 - 1 / (x : ℝ) ≤ 1 := by
    have : 0 < 1 / (x : ℝ) := by positivity
    linarith
  have h3x : 3 / (x : ℝ) ≤ 3 := by rw [div_le_iff₀ hx0]; linarith
  have h3x0 : 0 ≤ 3 / (x : ℝ) := by positivity
  have hfl1 : (1 - 1 / (x : ℝ)) * L2.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hf0 hl2
  have hfl2 : -0.6 ≤ (1 - 1 / (x : ℝ)) * L2.re := by nlinarith
  have hT1 : -(5 / 2) ≤ Γp.re + Real.log x - 7 / 2 + 3 / x - (1 - 1 / (x : ℝ)) * L2.re := by
    have : 3 / (2 * (x : ℝ)) ≤ 3 / x := by
      rw [div_le_div_iff₀ (by positivity) hx0]; nlinarith
    linarith
  have hT2 : Γp.re + Real.log x - 7 / 2 + 3 / x - (1 - 1 / (x : ℝ)) * L2.re ≤ 5 / 2 := by
    linarith
  have hkey : S - x / 2 = Z.re + (Γp.re + Real.log x - 7 / 2 + 3 / x
      - (1 - 1 / (x : ℝ)) * L2.re) := by rw [hre]; ring
  rw [hkey]
  have hA : A * (1 / 20) ≤ √x / 20 + 1 / 4 := by simp only [A]; linarith
  calc |Z.re + _| ≤ |Z.re| + |Γp.re + Real.log x - 7 / 2 + 3 / x - (1 - 1 / (x : ℝ)) * L2.re| :=
        abs_add_le _ _
    _ ≤ (√x / 20 + 1 / 4) + 5 / 2 := add_le_add (hZre.trans hA) (abs_le.2 ⟨hT1, hT2⟩)
    _ ≤ √x / 20 + 3 := by linarith

end Erdos985.Analytic
