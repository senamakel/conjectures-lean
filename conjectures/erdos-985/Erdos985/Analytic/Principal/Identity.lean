import Erdos985.Analytic.ExplicitFormula
import Erdos985.Analytic.XiGrowth
import Erdos985.Analytic.Principal.Identity.Zeros

/-!
# Bach's principal bound (RH) from Hadamard for `ξ`  — interfaces

`ξ = xiZeta = s(s−1)Λ(s)` with `Λ(s) = Γℝ(s) ζ(s)`; `ζ'/ζ = ξ'/ξ − 1/s − 1/(s−1) − G(s)`, with
`G = gammaLogDeriv` of the (even) character mod 1. Perron at `c = 2` plus Hadamard for `ξ`,
subtracting the value at `s = 2` (so the Hadamard constant cancels), and the residues
`w = ρ` (`perron_residue`), `w = 1` (gives `x/2 − 1 + 1/(2x)`) and `w = 0`
(`perron_residue_zero`, gives `log x − 1 + 1/x`) yield `explicit_formula_zeta`.

Bounds: `Σ_ρ m/|ρ(ρ+1)| ≤ Σ m/|ρ|² = 2 Σ Re(1/ρ) = 2 + γ − log 4π < 1/20` under RH
(the Hadamard constant of `ξ` is `ξ'/ξ(0) = ½ log 4π − 1 − γ/2`, computed from the
functional equation `ξ(s) = ξ(1−s)` and the Laurent expansion `ζ(s) = 1/(s−1) + γ + …`);
`gammaPart + log x ∈ [1 − 3/(2x), 1]`; `ζ'/ζ(2) ∈ [−0.6, 0]`.
Then `|S − x/2| ≤ (√x + 2 + 3/x)/20 + 5/2 ≤ √x/20 + 3`.
-/

namespace Erdos985.Analytic

open Complex ArithmeticFunction MeasureTheory IdentityAux

theorem xiZeta_zero_re_mem {ρ : ℂ} (hρ : xiZeta ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 :=
  PrincipalAux.xiZeta_zero_re_mem hρ

/-- The weighted explicit formula for `ζ`. -/
theorem explicit_formula_zeta (x : ℕ) (hx : 1 ≤ x) :
    (((∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ)) : ℂ)
      = (∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℂ) * zeroTerm x ρ)
        + gammaPart (1 : DirichletCharacter ℂ 1) x
        + ((x : ℂ) / 2 + (Real.log x : ℂ) - 7 / 2 + 3 / (x : ℂ))
        - (1 - 1 / (x : ℂ)) * (deriv riemannZeta 2 / riemannZeta 2) := by
  classical
  set G := gammaLogDeriv (1 : DirichletCharacter ℂ 1) with hG
  set D : ℂ → ℂ := fun z => deriv xiZeta z / xiZeta z with hD
  set m : {ρ : ℂ // xiZeta ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt xiZeta ρ : ℂ) with hm
  set c2 : ℂ := deriv riemannZeta 2 / riemannZeta 2 with hc2
  have := PrincipalAux.countable_xiZeta_zeros
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have hsre : ∀ t : ℝ, ((2 : ℂ) + t * I).re = 2 := fun t => by simp
  have hs_cont : Continuous fun t : ℝ => (2 : ℂ) + t * I :=
    continuous_const.add (continuous_ofReal.mul continuous_const)
  have hΛd : Differentiable ℂ xiZeta := differentiable_xiZeta
  have hΛne : ∀ z : ℂ, 1 ≤ z.re → xiZeta z ≠ 0 := fun z hz h => by
    linarith [(xiZeta_zero_re_mem h).2]
  /- Hadamard -/
  obtain ⟨hsum_ε, b, hb⟩ := hadamard_logDeriv hΛd (by rw [xiZeta_zero]; exact one_ne_zero)
    xiZeta_growth
  have hzre : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 :=
    fun ρ => xiZeta_zero_re_mem ρ.2
  /- The family of zero terms. -/
  let F : {ρ : ℂ // xiZeta ρ = 0} → ℝ → ℂ := fun ρ t => m ρ * pairTerm x ρ t
  have hF_int : ∀ ρ, Integrable (F ρ) := fun ρ =>
    (integrable_pairTerm hx0 (by linarith [hzre ρ])).const_mul _
  obtain ⟨C, hC0, hC⟩ := integral_norm_pairTerm_le
  have hF_sum : Summable fun ρ => ∫ t, ‖F ρ t‖ := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun ρ => ?_) ((hsum_ε (1 / 2) (by norm_num)).mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (hzre ρ).1.ne' (by simp [h])
    simp only [F, m, norm_mul, Complex.norm_natCast, integral_const_mul]
    calc (analyticOrderNatAt xiZeta ρ : ℝ) * ∫ t, ‖pairTerm x ρ t‖
        ≤ (analyticOrderNatAt xiZeta ρ : ℝ) *
            (C * (x : ℝ) ^ (2 : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hC x hx0 ρ (hzre ρ).2 hρ0) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hF_hasSum : ∀ t : ℝ, HasSum (fun ρ => F ρ t) ((D ((2 : ℂ) + t * I) - D 2) * kern x t) := by
    intro t
    obtain ⟨h1s, h1e⟩ := hb ((2 : ℂ) + t * I) (hΛne _ (by rw [hsre]; norm_num))
    obtain ⟨h2s, h2e⟩ := hb 2 (hΛne _ (by norm_num))
    have := (h1s.hasSum.sub h2s.hasSum).mul_right (kern x t)
    convert this using 1
    · funext ρ
      simp only [F, m, pairTerm]
      ring
    · simp only [hD]
      rw [h1e, h2e]
      ring
  have hD_cont : Continuous fun t : ℝ => D ((2 : ℂ) + t * I) := by
    have hcd : Continuous (deriv xiZeta) := (hΛd.contDiff (n := 1)).continuous_deriv le_rfl
    exact (hcd.comp hs_cont).div (hΛd.continuous.comp hs_cont)
      (fun t => hΛne _ (by simp))
  have hF1_int : Integrable fun t : ℝ => (D ((2 : ℂ) + t * I) - D 2) * kern x t :=
    integrable_of_hasSum
      ((hD_cont.sub continuous_const).aestronglyMeasurable.mul (integrable_kern hx0).1)
      hF_int hF_sum hF_hasSum
  have hF1_integral : ∫ t : ℝ, (D ((2 : ℂ) + t * I) - D 2) * kern x t
      = ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, m ρ * (-(2 * Real.pi) * zeroTerm x ρ) := by
    rw [show (fun t : ℝ => (D ((2 : ℂ) + t * I) - D 2) * kern x t)
        = fun t => ∑' ρ, F ρ t from funext fun t => (hF_hasSum t).tsum_eq.symm,
      ← integral_tsum_of_summable_integral_norm hF_int hF_sum]
    refine tsum_congr fun ρ => ?_
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (hzre ρ).1.ne' (by simp [h])
    have hρ1 : (ρ : ℂ) ≠ -1 := fun h => by
      have := (hzre ρ).1; rw [h] at this; norm_num at this
    simp only [F]
    rw [integral_const_mul, integral_pairTerm x hx (by linarith [hzre ρ]) hρ0 hρ1]
  /- Perron. -/
  set a : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) with ha
  have ha_sum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (2 : ℝ) := by
    have hs := (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
    refine hs.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, a]
  have hP := PerronKernel.perron_weighted a 2 two_pos ha_sum x hx
  simp only [ofReal_ofNat] at hP
  have hLS : ∀ z : ℂ, 1 < z.re → LSeries a z = -(D z - 1 / z - 1 / (z - 1) - G z) := fun z hz => by
    have h1 := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz
    change LSeries a z = _ at h1
    rw [h1, neg_div, PrincipalAux.logDeriv_riemannZeta_eq hz]
  have hc2' : c2 = D 2 - 1 / 2 - 1 / (2 - 1) - G 2 :=
    PrincipalAux.logDeriv_riemannZeta_eq (by norm_num)
  set H : ℝ → ℂ := fun t => LSeries a ((2 : ℂ) + t * I) * (x : ℂ) ^ ((2 : ℂ) + t * I)
    / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) with hH
  have hH_eq : ∀ t : ℝ, H t = LSeries a ((2 : ℂ) + t * I) * kern x t := fun t => by
    simp only [hH, kern, ofReal_natCast]
    ring
  have hH_int : Integrable H := by
    have hab : LSeries.abscissaOfAbsConv a < ((2 : ℝ) : EReal) := by
      refine lt_of_le_of_lt (LSeriesSummable.abscissaOfAbsConv_le
        (LSeriesSummable_vonMangoldt (s := (3 / 2 : ℂ)) (by norm_num))) ?_
      have : (3 / 2 : ℂ).re = 3 / 2 := by norm_num
      rw [this]
      exact EReal.coe_lt_coe_iff.2 (by norm_num)
    have hcont : Continuous fun t : ℝ => LSeries a ((2 : ℂ) + t * I) :=
      (LSeries_differentiableOn a).continuousOn.comp_continuous hs_cont
        (fun t => by simp only [Set.mem_ofPred_eq, hsre]; exact_mod_cast hab)
    set B := ∑' n, ‖LSeries.term a 2 n‖
    have hbd : ∀ t : ℝ, ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ B := fun t => by
      have hs2 := (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
      have heq : (fun n => ‖LSeries.term a ((2 : ℂ) + t * I) n‖)
          = fun n => ‖LSeries.term a 2 n‖ := by
        funext n; rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsre]; simp
      calc ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ ∑' n, ‖LSeries.term a ((2 : ℂ) + t * I) n‖ :=
            norm_tsum_le_tsum_norm (by rw [heq]; exact hs2)
        _ = B := by rw [heq]
    have : H = fun t : ℝ => LSeries a ((2 : ℂ) + t * I) * kern x t := funext hH_eq
    rw [this]
    refine Integrable.mono' ((integrable_kern hx0).norm.const_mul B)
      (hcont.aestronglyMeasurable.mul (integrable_kern hx0).1)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbd t) (norm_nonneg _)
  /- The poles at `0` and `1`. -/
  set P0 : ℝ → ℂ := fun t => ((x : ℝ) : ℂ) ^ ((2 : ℂ) + t * I) /
    (((2 : ℂ) + t * I - 0) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) with hP0
  have hP0_int : Integrable P0 := by
    have := perron_residue_integrable (x : ℝ) 2 hx0 two_pos 0 (by simp)
    simp only [ofReal_ofNat] at this
    exact this
  have hP0_integral : ∫ t, P0 t = 2 * Real.pi * ((Real.log x : ℂ) - 1 + (x : ℂ) ^ (-1 : ℂ)) := by
    have h := perron_residue_zero (x : ℝ) 2 hx1 two_pos 0 rfl
    simp only [ofReal_ofNat, ofReal_natCast] at h
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    simp [hP0]
  have hR1_int : Integrable (resKern x 1) := integrable_resKern hx0 (by norm_num)
  have hR1_integral : ∫ t, resKern x 1 t
      = 2 * Real.pi * ((x : ℂ) ^ (1 : ℂ) / (1 * (1 + 1)) - 1 / 1 + (x : ℂ) ^ (-1 : ℂ) / (1 + 1)) := by
    have h := perron_residue (x : ℝ) 2 hx1 two_pos 1 (by norm_num) one_ne_zero (by norm_num)
    simp only [ofReal_ofNat, ofReal_natCast] at h
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    simp [resKern]
  /- Decomposition of the gamma part. -/
  have hF2 : (fun t : ℝ => (G ((2 : ℂ) + t * I) - G 2) * (x : ℂ) ^ ((2 : ℂ) + t * I)
      / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))
      = fun t : ℝ => H t + (D ((2 : ℂ) + t * I) - D 2) * kern x t - P0 t - resKern x 1 t
          + (c2 + 3 / 2) * kern x t := by
    funext t
    have hz : 1 < ((2 : ℂ) + t * I).re := by rw [hsre]; norm_num
    have h0 := line_ne_zero' t
    have h1 := line_add_one_ne_zero' t
    have h2 := line_sub_ne_zero' (ρ := 1) (by norm_num) t
    rw [hH_eq, hLS _ hz, hc2']
    simp only [kern, resKern, hP0, ofReal_natCast, sub_zero]
    field_simp
    ring
  have hgamma : gammaPart (1 : DirichletCharacter ℂ 1) x = (1 / (2 * Real.pi) : ℂ) *
      ((∫ t, H t) + (∫ t : ℝ, (D ((2 : ℂ) + t * I) - D 2) * kern x t)
        - (∫ t, P0 t) - (∫ t, resKern x 1 t) + (c2 + 3 / 2) * ∫ t, kern x t) := by
    unfold gammaPart
    rw [← hG, hF2, integral_add _ ((integrable_kern hx0).const_mul _),
      integral_sub _ hR1_int, integral_sub _ hP0_int, integral_add hH_int hF1_int,
      integral_const_mul]
    · exact hH_int.add hF1_int
    · exact (hH_int.add hF1_int).sub hP0_int
    · exact ((hH_int.add hF1_int).sub hP0_int).sub hR1_int
  /- Assemble. -/
  have hbach : (((∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ)) : ℂ)
      = ∑ n ∈ Finset.Ioo 0 x, a n * (1 - (n : ℂ) / x) := by
    push_cast
    symm
    refine Finset.sum_subset (fun n hn => ?_) fun n hn hn' => ?_
    · rw [Finset.mem_Ioo] at hn; rw [Finset.mem_range]; omega
    · have : n = 0 := by rw [Finset.mem_Ioo] at hn'; rw [Finset.mem_range] at hn; omega
      subst this
      simp [a]
  have hbach' : (((∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ)) : ℂ)
      = (1 / (2 * Real.pi) : ℂ) * ∫ t, H t := by
    rw [hbach, hP]
  have hK := integral_kern hx1
  have htsum : ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, m ρ * (-(2 * Real.pi) * zeroTerm x ρ)
      = -(2 * Real.pi) * ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, m ρ * zeroTerm x ρ := by
    rw [← tsum_mul_left]
    exact tsum_congr fun ρ => by ring
  rw [hgamma, hbach', hF1_integral, htsum, hK, hP0_integral, hR1_integral]
  simp only [ofReal_natCast, cpow_one, cpow_neg_one]
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  field_simp
  ring

end Erdos985.Analytic
