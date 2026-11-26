import Cramer.Psi1
import Cramer.SecondDiff
import Cramer.ZeroSum

/-!
# The second difference of `Ψ₁` from erdos-985's explicit formula

Multiplying `explicit_formula_zeta` by `n` gives, for natural `n ≥ 1`,
`Ψ₁(n) = Re Σ_ρ m_ρ · n·zeroTerm(n, ρ) + F(n) + n²/2 − 7n/2 + 3 − (n − 1) Re ζ'/ζ(2)`
with `F(n) = n (Re gammaPart(n) + log n) ∈ [n − 3/2, n]`. In the second difference with step
`h` (points `a, a+h, a+2h`) the affine terms cancel, `n²/2` gives `h²`, `F` contributes at
least `−3`, and `n·zeroTerm(n, ρ)` contributes `−D_ρ` with
`D_ρ = g(a+2h) − 2g(a+h) + g(a)`, `g(t) = t^{ρ+1}/(ρ(ρ+1))` (`Cramer.SecondDiff`).
Under RH the zero part is bounded by `Cramer.weighted_zeroSum_le`.
-/

namespace Cramer

open Complex Erdos985.Analytic ArithmeticFunction

/-- `n · zeroTerm(n, ρ)`. -/
noncomputable def V (n : ℕ) (ρ : ℂ) : ℂ := (n : ℂ) * zeroTerm n ρ

lemma V_eq {n : ℕ} (hn : 1 ≤ n) {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ + 1 ≠ 0) :
    V n ρ = ((n : ℂ) - 1) / (2 - ρ) - gρ ρ (n : ℝ) + (n : ℂ) / ρ - 1 / (1 + ρ) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpow : (n : ℂ) * (n : ℂ) ^ ρ = (n : ℂ) ^ (ρ + 1) := by
    rw [cpow_add _ _ hn0, cpow_one, mul_comm]
  have hinv : (n : ℂ) ^ (-1 : ℂ) = (n : ℂ)⁻¹ := cpow_neg_one _
  simp only [V, zeroTerm, gρ, hinv]
  push_cast
  rw [← hpow]
  field_simp
  ring

/-- The second difference of `V` is `−D_ρ`. -/
lemma V_second_diff {a h : ℕ} (ha : 1 ≤ a) {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ + 1 ≠ 0) :
    V (a + 2 * h) ρ - 2 * V (a + h) ρ + V a ρ
      = -(gρ ρ ((a : ℝ) + 2 * h) - 2 * gρ ρ ((a : ℝ) + h) + gρ ρ a) := by
  rw [V_eq (by omega) hρ0 hρ1, V_eq (by omega) hρ0 hρ1, V_eq ha hρ0 hρ1]
  push_cast
  ring

/-- The explicit formula for `Ψ₁(n)`. -/
lemma psi1N_formula (n : ℕ) (hn : 1 ≤ n) :
    psi1N n = (∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℂ) * V n ρ).re
      + n * ((gammaPart (1 : DirichletCharacter ℂ 1) n).re + Real.log n)
      + (n : ℝ) ^ 2 / 2 - 7 * n / 2 + 3 - ((n : ℝ) - 1) * (deriv riemannZeta 2 / riemannZeta 2).re := by
  have hid := congrArg (fun z : ℂ => ((n : ℂ) * z).re) (explicit_formula_zeta n hn)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hL2 : (deriv riemannZeta 2 / riemannZeta 2).im = 0 := logDeriv_zeta_two_bound.1
  have hG : (gammaPart (1 : DirichletCharacter ℂ 1) n).im = 0 := (gammaPart_one_bound n hn).1
  have hZ : (∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℂ) * V n ρ)
      = (n : ℂ) * ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℂ) * zeroTerm n ρ := by
    rw [← tsum_mul_left]
    refine tsum_congr fun ρ => ?_
    simp only [V]; ring
  rw [psi1N_eq_mul n hn, hZ]
  rw [show ((n : ℂ) * ((((∑ k ∈ Finset.range n, (Λ k : ℝ) * (1 - (k : ℝ) / n) : ℝ)) : ℂ))).re
      = (n : ℝ) * ∑ k ∈ Finset.range n, (Λ k : ℝ) * (1 - (k : ℝ) / n) by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, ← ofReal_mul, ofReal_re]] at hid
  rw [hid]
  set Z := ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℂ) * zeroTerm n ρ
  set G := gammaPart (1 : DirichletCharacter ℂ 1) n
  set c := deriv riemannZeta 2 / riemannZeta 2
  have hc : (n : ℂ) * (Z + G + ((n : ℂ) / 2 + (Real.log n : ℂ) - 7 / 2 + 3 / (n : ℂ))
      - (1 - 1 / (n : ℂ)) * c)
      = ((n : ℝ) : ℂ) * Z + ((n : ℝ) : ℂ) * G
        + (((n : ℝ) ^ 2 / 2 + n * Real.log n - 7 * n / 2 + 3 : ℝ) : ℂ)
        - (((n : ℝ) - 1 : ℝ) : ℂ) * c := by
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    push_cast
    field_simp
  rw [hc]
  simp only [sub_re, add_re, ofReal_re, ofReal_im, mul_re, natCast_re, natCast_im, zero_mul,
    sub_zero]
  ring

/-- **The analytic step, for any bound on the zero sum.** Under RH, for `a, h ≥ 1`, if
`Σ_ρ m_ρ ‖D_ρ‖ ≤ Z` (`D_ρ = g(a+2h) − 2g(a+h) + g(a)`), then
`Ψ₁(a+2h) − 2Ψ₁(a+h) + Ψ₁(a) ≥ h² − Z − 3`. -/
theorem psi1N_second_diff_ge_of_zeroSum (hRH : RiemannHypothesis) {a h : ℕ} (ha : 1 ≤ a)
    (hh : 1 ≤ h) {Z : ℝ}
    (hsumD : Summable fun ρ : {ρ : ℂ // xiZeta ρ = 0} => (analyticOrderNatAt xiZeta ρ : ℝ) *
      ‖gρ ρ ((a : ℝ) + 2 * h) - 2 * gρ ρ ((a : ℝ) + h) + gρ ρ a‖)
    (hD : ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ) *
      ‖gρ ρ ((a : ℝ) + 2 * h) - 2 * gρ ρ ((a : ℝ) + h) + gρ ρ a‖ ≤ Z) :
    (h : ℝ) ^ 2 - Z - 3 ≤ psi1N (a + 2 * h) - 2 * psi1N (a + h) + psi1N a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hhR : (0 : ℝ) ≤ h := h.cast_nonneg
  set m : {ρ : ℂ // xiZeta ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt xiZeta ρ : ℂ)
  set D : {ρ : ℂ // xiZeta ρ = 0} → ℂ := fun ρ =>
    gρ ρ ((a : ℝ) + 2 * h) - 2 * gρ ρ ((a : ℝ) + h) + gρ ρ a
  have hcrit : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => xiZeta_zero_re_RH hRH ρ.2
  have hρ0 : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, (ρ : ℂ) ≠ 0 := fun ρ h => by
    have := hcrit ρ; rw [h] at this; norm_num at this
  have hρ1 : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, (ρ : ℂ) + 1 ≠ 0 := fun ρ h => by
    have := hcrit ρ
    have h2 : ((ρ : ℂ) + 1).re = 0 := by rw [h]; simp
    simp [this] at h2; norm_num at h2
  have hsumD' : Summable fun ρ : {ρ : ℂ // xiZeta ρ = 0} => ‖m ρ * D ρ‖ := by
    refine hsumD.congr fun ρ => ?_
    simp [m, D]
  -- summability of each zero series
  have hsq : Summable fun ρ : {ρ : ℂ // xiZeta ρ = 0} =>
      (analyticOrderNatAt xiZeta ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ := by
    have hs := (hadamard_logDeriv differentiable_xiZeta (by rw [xiZeta_zero]; exact one_ne_zero)
      xiZeta_growth).1 1 one_pos
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ρ => ?_) hs
    have hq := PrincipalAux.inv_norm_mul_le_re (hcrit ρ)
    have hn2 : ‖(ρ : ℂ)‖ ^ (1 + 1 : ℝ) = 1 / 4 + (ρ : ℂ).im ^ 2 := by
      rw [show (1 + 1 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, ← normSq_eq_norm_sq,
        normSq_apply, hcrit ρ]; ring
    have hre1 : (1 / (1 - (ρ : ℂ)) + 1 / (ρ : ℂ)).re = 1 / (1 / 4 + (ρ : ℂ).im ^ 2) := by
      have key : ∀ z : ℂ, z.re = 1 / 2 → (1 / (1 - z) + 1 / z).re = 1 / (1 / 4 + z.im ^ 2) := by
        rintro ⟨x, γ⟩ hx
        simp only at hx
        subst hx
        simp [normSq_apply]
        field_simp
        ring
      exact key _ (hcrit ρ)
    rw [hre1] at hq
    rw [hn2, div_eq_mul_one_div, div_eq_mul_one_div (analyticOrderNatAt xiZeta ρ : ℝ)]
    exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
  have hsumV : ∀ n : ℕ, 1 ≤ n → Summable fun ρ : {ρ : ℂ // xiZeta ρ = 0} => m ρ * V n ρ := by
    intro n hn
    refine Summable.of_norm_bounded ((hsq.mul_left ((n : ℝ) * (√(n : ℝ) + 2 + 3 / n)))) fun ρ => ?_
    rw [norm_mul, V, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    have := norm_zeroTerm_le n hn (hcrit ρ)
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    calc (analyticOrderNatAt xiZeta ρ : ℝ) * ((n : ℝ) * ‖zeroTerm n ρ‖)
        ≤ (analyticOrderNatAt xiZeta ρ : ℝ) *
            ((n : ℝ) * ((√(n : ℝ) + 2 + 3 / n) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖)) := by gcongr
      _ = _ := by ring
  -- the combined zero series
  have hcomb : (∑' ρ, m ρ * V (a + 2 * h) ρ) - 2 * (∑' ρ, m ρ * V (a + h) ρ) + ∑' ρ, m ρ * V a ρ
      = -∑' ρ, m ρ * D ρ := by
    rw [← tsum_mul_left, ← (hsumV _ (by omega)).tsum_sub ((hsumV _ (by omega)).mul_left 2),
      ← ((hsumV _ (by omega)).sub ((hsumV _ (by omega)).mul_left 2)).tsum_add (hsumV a ha),
      ← tsum_neg]
    refine tsum_congr fun ρ => ?_
    have := V_second_diff (h := h) ha (hρ0 ρ) (hρ1 ρ)
    simp only [D]
    linear_combination (m ρ) * this
  have hZ : -(∑' ρ, m ρ * D ρ).re ≥ -Z := by
    have h1 : (∑' ρ, m ρ * D ρ).re ≤ ‖∑' ρ, m ρ * D ρ‖ := re_le_norm _
    have h2 : ‖∑' ρ, m ρ * D ρ‖ ≤ ∑' ρ, ‖m ρ * D ρ‖ := norm_tsum_le_tsum_norm hsumD'
    have h3 : ∑' ρ, ‖m ρ * D ρ‖
        = ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ) * ‖D ρ‖ :=
      tsum_congr fun ρ => by simp [m]
    linarith
  -- assemble
  rw [psi1N_formula _ (by omega), psi1N_formula _ (by omega), psi1N_formula _ ha]
  have hre := congrArg Complex.re hcomb
  simp only [sub_re, add_re, mul_re, neg_re, re_ofNat, im_ofNat, zero_mul, sub_zero] at hre
  obtain ⟨-, g1, g2⟩ := gammaPart_one_bound (a + 2 * h) (by omega)
  obtain ⟨-, g3, g4⟩ := gammaPart_one_bound (a + h) (by omega)
  obtain ⟨-, g5, g6⟩ := gammaPart_one_bound a ha
  set G1 := (gammaPart (1 : DirichletCharacter ℂ 1) (a + 2 * h)).re + Real.log ((a + 2 * h : ℕ) : ℝ)
  set G2 := (gammaPart (1 : DirichletCharacter ℂ 1) (a + h)).re + Real.log ((a + h : ℕ) : ℝ)
  set G3 := (gammaPart (1 : DirichletCharacter ℂ 1) a).re + Real.log (a : ℝ)
  have hb1 : (1 : ℝ) ≤ ((a + 2 * h : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ a + 2 * h by omega)
  have hx1 : (1 : ℝ) ≤ ((a + h : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ a + h by omega)
  have hF1 : ((a + 2 * h : ℕ) : ℝ) - 3 / 2 ≤ ((a + 2 * h : ℕ) : ℝ) * G1 := by
    have := mul_le_mul_of_nonneg_left g1 (by linarith : (0 : ℝ) ≤ ((a + 2 * h : ℕ) : ℝ))
    have e : ((a + 2 * h : ℕ) : ℝ) * (3 / (2 * ((a + 2 * h : ℕ) : ℝ))) = 3 / 2 := by
      field_simp
    nlinarith
  have hF2 : ((a + h : ℕ) : ℝ) * G2 ≤ ((a + h : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_left g4 (by linarith : (0 : ℝ) ≤ ((a + h : ℕ) : ℝ))
    linarith
  have hF3 : (a : ℝ) - 3 / 2 ≤ (a : ℝ) * G3 := by
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have := mul_le_mul_of_nonneg_left g5 (by linarith : (0 : ℝ) ≤ (a : ℝ))
    have e : (a : ℝ) * (3 / (2 * (a : ℝ))) = 3 / 2 := by
      field_simp
    nlinarith
  push_cast at hF1 hF2 hF3 hre ⊢
  nlinarith

/-- **The analytic step.** Under RH, for `a, h ≥ 1` and any `σ > 3/2` with
`4(a+2h)^{3/2} ≤ (h² a^{−1/2}) σ²`:
`Ψ₁(a+2h) − 2Ψ₁(a+h) + Ψ₁(a) ≥ h² − 2 (h² a^{−1/2}) σ (L(1/2+σ) + 1/40) − 3`. -/
theorem psi1N_second_diff_ge (hRH : RiemannHypothesis) {a h : ℕ} (ha : 1 ≤ a) (hh : 1 ≤ h)
    {σ : ℝ} (hσ : 3 / 2 < σ)
    (hB : 4 * ((a : ℝ) + 2 * h) ^ (3 / 2 : ℝ) ≤ (h : ℝ) ^ 2 * (a : ℝ) ^ (-(1 / 2 : ℝ)) * σ ^ 2) :
    (h : ℝ) ^ 2 - 2 * ((h : ℝ) ^ 2 * (a : ℝ) ^ (-(1 / 2 : ℝ))) * σ * (Lup (1 / 2 + σ) + 1 / 40) - 3
      ≤ psi1N (a + 2 * h) - 2 * psi1N (a + h) + psi1N a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hhR : (0 : ℝ) ≤ h := h.cast_nonneg
  have hcrit : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => xiZeta_zero_re_RH hRH ρ.2
  obtain ⟨hsumD, hD⟩ := weighted_zeroSum_le hRH (σ := σ)
    (A := (h : ℝ) ^ 2 * (a : ℝ) ^ (-(1 / 2 : ℝ))) (B := 4 * ((a : ℝ) + 2 * h) ^ (3 / 2 : ℝ)) hσ
    (by positivity) (by positivity) hB
    (fun ρ => ‖gρ ρ ((a : ℝ) + 2 * h) - 2 * gρ ρ ((a : ℝ) + h) + gρ ρ a‖) (fun _ => norm_nonneg _)
    (fun ρ => norm_second_diff_gρ_le (hcrit ρ) haR hhR)
    (fun ρ => norm_second_diff_gρ_le' (hcrit ρ) haR hhR)
  have := psi1N_second_diff_ge_of_zeroSum hRH ha hh hsumD hD
  linarith

end Cramer
