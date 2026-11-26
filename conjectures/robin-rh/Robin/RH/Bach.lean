import Erdos985.Analytic.Principal
import Robin.RH.Psi1

/-!
# Bach's weighted explicit-formula bound under RH

The RH-only version of `Erdos985.Analytic.bach_principal_of_GRH`: for every natural `x ≥ 1`,
`|Σ_{n<x} Λ(n)(1 − n/x) − x/2| ≤ √x/20 + 3`.
The erdos-985 proof uses GRH only to place the zeros of `ξ` on the critical line; Mathlib's
`RiemannHypothesis` suffices for that.
-/

namespace Robin

open ArithmeticFunction

/-- The bound produced by the explicit formula; the hypothesis of the analytic part. -/
def BachBound : Prop :=
  ∀ x : ℕ, 1 ≤ x →
    |∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) - x / 2| ≤ √(x : ℝ) / 20 + 3

section RHAux

open Complex Erdos985.Analytic Erdos985.Analytic.PrincipalAux

/-- Under RH, `ξ` has no zeros with `Re s > 1/2`. -/
theorem xiZeta_ne_zero_of_half_lt_RH (hRH : RiemannHypothesis) {s : ℂ}
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
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hs
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have := hRH s hζ htriv hs1
  linarith

theorem xiZeta_zero_re_RH (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : xiZeta ρ = 0) :
    ρ.re = 1 / 2 := by
  have h1 : ¬ 1 / 2 < ρ.re := fun h => xiZeta_ne_zero_of_half_lt_RH hRH h hρ
  have h2 : ¬ 1 / 2 < (1 - ρ).re := fun h =>
    xiZeta_ne_zero_of_half_lt_RH hRH h (by rw [xiZeta_one_sub]; exact hρ)
  simp only [sub_re, one_re] at h2
  linarith

theorem zeroSum_zeta_le_RH (hRH : RiemannHypothesis) :
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
    have h := inv_norm_mul_le_re (xiZeta_zero_re_RH hRH ρ.2)
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

theorem bach_principal_of_RH (hRH : RiemannHypothesis) (x : ℕ) (hx : 1 ≤ x) :
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
  obtain ⟨hsum, hZ⟩ := zeroSum_zeta_le_RH hRH
  set A : ℝ := √(x : ℝ) + 2 + 3 / x
  have hA0 : 0 ≤ A := by positivity
  have hterm : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0},
      ‖(analyticOrderNatAt xiZeta ρ : ℂ) * zeroTerm x ρ‖
        ≤ A * ((analyticOrderNatAt xiZeta ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) := by
    intro ρ
    rw [norm_mul, Complex.norm_natCast]
    have h := norm_zeroTerm_le x hx (xiZeta_zero_re_RH hRH ρ.2)
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

end RHAux

theorem bachBound_of_RH (hRH : RiemannHypothesis) : BachBound :=
  fun x hx => bach_principal_of_RH hRH x hx

/-- `BachBound` multiplied by `m`: the bound for `Ψ₁` at integers. -/
theorem psi1NatBound_of_bachBound (hB : BachBound) : Psi1NatBound := by
  intro m hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hS := hB m hm
  set S := ∑ n ∈ Finset.range m, (Λ n : ℝ) * (1 - (n : ℝ) / m)
  have hpsi : psi1 m = m * S := by
    unfold psi1
    rw [Nat.floor_natCast, Finset.sum_range_succ, sub_self, mul_zero, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    field_simp
  have hpow : (m : ℝ) ^ ((3 : ℝ) / 2) = m * √(m : ℝ) := by
    rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
      Real.rpow_add hm0, Real.rpow_one]
  rw [hpsi, hpow, show (m : ℝ) * S - (m : ℝ) ^ 2 / 2 = m * (S - m / 2) by ring, abs_mul,
    abs_of_pos hm0]
  calc (m : ℝ) * |S - m / 2| ≤ m * (√(m : ℝ) / 20 + 3) := mul_le_mul_of_nonneg_left hS hm0.le
    _ = _ := by ring

theorem psi1NatBound_of_RH (hRH : RiemannHypothesis) : Psi1NatBound :=
  psi1NatBound_of_bachBound (bachBound_of_RH hRH)

end Robin
