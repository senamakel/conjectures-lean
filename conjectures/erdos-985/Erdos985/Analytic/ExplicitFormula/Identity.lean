import Erdos985.Analytic.ExplicitFormula.StepA
import Erdos985.Analytic.ExplicitFormula.Identity.Zeros
import Erdos985.Analytic.ExplicitFormula.Identity.Terms

namespace Erdos985.Analytic

open Complex ArithmeticFunction MeasureTheory IdentityAux
open scoped Classical

variable {N : ℕ} [NeZero N]

/-! ### Step B: the explicit formula (an exact identity) -/

/-- The weighted explicit formula, with the Hadamard constant eliminated. -/
theorem explicit_formula {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (x : ℕ) (hx : 1 ≤ x) :
    bachSum χ x
      = (∑' ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0},
            (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ) * zeroTerm x ρ)
        + gammaPart χ x
        - (1 - 1 / (x : ℂ)) * (deriv (DirichletCharacter.LFunction χ) 2
            / DirichletCharacter.LFunction χ 2) := by
  set Λf := DirichletCharacter.completedLFunction χ with hΛf
  set L := DirichletCharacter.LFunction χ with hL
  set G := gammaLogDeriv χ with hG
  set D : ℂ → ℂ := fun z => deriv Λf z / Λf z with hD
  set m : {ρ : ℂ // Λf ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt Λf ρ : ℂ) with hm
  set c2 : ℂ := deriv L 2 / L 2 with hc2
  have := countable_zeros hprim hχ
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have hsre : ∀ t : ℝ, ((2 : ℂ) + t * I).re = 2 := fun t => by simp
  have hs_cont : Continuous fun t : ℝ => (2 : ℂ) + t * I :=
    continuous_const.add (continuous_ofReal.mul continuous_const)
  have hΛd : Differentiable ℂ Λf := DirichletCharacter.differentiable_completedLFunction hχ
  have hLd : Differentiable ℂ L := DirichletCharacter.differentiable_LFunction hχ
  have hΛne : ∀ z : ℂ, 1 ≤ z.re → Λf z ≠ 0 := fun z hz =>
    DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hz
  have hLne : ∀ z : ℂ, 1 ≤ z.re → L z ≠ 0 := fun z hz =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hz
  /- Hadamard -/
  obtain ⟨hsum_ε, b, hb⟩ := hadamard_logDeriv hΛd (completedLFunction_zero_ne_zero χ hχ hprim)
    (completedLFunction_growth χ hχ)
  have hzre : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 :=
    fun ρ => zero_re_mem hprim hχ ρ.2
  /- The family of zero terms. -/
  let F : {ρ : ℂ // Λf ρ = 0} → ℝ → ℂ := fun ρ t => m ρ * pairTerm x ρ t
  have hF_int : ∀ ρ, Integrable (F ρ) := fun ρ =>
    (integrable_pairTerm hx0 (by linarith [hzre ρ])).const_mul _
  obtain ⟨C, hC0, hC⟩ := integral_norm_pairTerm_le
  have hF_sum : Summable fun ρ => ∫ t, ‖F ρ t‖ := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun ρ => ?_) ((hsum_ε (1 / 2) (by norm_num)).mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (hzre ρ).1.ne' (by simp [h])
    simp only [F, m, norm_mul, Complex.norm_natCast, integral_const_mul]
    calc (analyticOrderNatAt Λf ρ : ℝ) * ∫ t, ‖pairTerm x ρ t‖
        ≤ (analyticOrderNatAt Λf ρ : ℝ) * (C * (x : ℝ) ^ (2 : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)) :=
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
    have hcd : Continuous (deriv Λf) := (hΛd.contDiff (n := 1)).continuous_deriv le_rfl
    exact (hcd.comp hs_cont).div (hΛd.continuous.comp hs_cont)
      (fun t => hΛne _ (by simp))
  have hF1_int : Integrable fun t : ℝ => (D ((2 : ℂ) + t * I) - D 2) * kern x t :=
    integrable_of_hasSum
      ((hD_cont.sub continuous_const).aestronglyMeasurable.mul (integrable_kern hx0).1)
      hF_int hF_sum hF_hasSum
  have hF1_integral : ∫ t : ℝ, (D ((2 : ℂ) + t * I) - D 2) * kern x t
      = ∑' ρ : {ρ : ℂ // Λf ρ = 0}, m ρ * (-(2 * Real.pi) * zeroTerm x ρ) := by
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
  set a : ℕ → ℂ := fun n => (χ n : ℂ) * (Λ n : ℂ) with ha
  have ha_sum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (2 : ℝ) := by
    have hs := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (s := 2)
      (by norm_num)).norm
    refine hs.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, a]
  have hP := PerronKernel.perron_weighted a 2 two_pos ha_sum x hx
  simp only [ofReal_ofNat] at hP
  have hLS : ∀ z : ℂ, 1 < z.re → LSeries a z = -(D z - G z) := fun z hz => by
    have h1 := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hz
    have h2 := logDeriv_LFunction_eq hχ hz
    rw [← DirichletCharacter.LFunction_eq_LSeries χ hz,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hz] at h1
    change LSeries a z = _ at h1
    rw [h1, neg_div, h2]
  have hc2' : c2 = D 2 - G 2 := logDeriv_LFunction_eq hχ (by norm_num)
  set H : ℝ → ℂ := fun t => LSeries a ((2 : ℂ) + t * I) * (x : ℂ) ^ ((2 : ℂ) + t * I)
    / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) with hH
  have hH_eq : ∀ t : ℝ, H t = LSeries a ((2 : ℂ) + t * I) * kern x t := fun t => by
    simp only [hH, kern, ofReal_natCast]
    ring
  have hH_int : Integrable H := by
    have hcont : Continuous fun t : ℝ => LSeries a ((2 : ℂ) + t * I) := by
      have hcd : Continuous (deriv L) := (hLd.contDiff (n := 1)).continuous_deriv le_rfl
      have : (fun t : ℝ => LSeries a ((2 : ℂ) + t * I))
          = fun t : ℝ => -(deriv L ((2 : ℂ) + t * I) / L ((2 : ℂ) + t * I)) := by
        funext t
        have hz : 1 < ((2 : ℂ) + t * I).re := by rw [hsre]; norm_num
        rw [hLS _ hz, ← logDeriv_LFunction_eq hχ hz]
      rw [this]
      exact ((hcd.comp hs_cont).div (hLd.continuous.comp hs_cont)
        (fun t => hLne _ (by simp))).neg
    set B := ∑' n, ‖LSeries.term a 2 n‖
    have hbd : ∀ t : ℝ, ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ B := fun t => by
      have hs2 := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (s := 2)
        (by norm_num)).norm
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
  /- Decomposition of the gamma part. -/
  have hF2 : (fun t : ℝ => (G ((2 : ℂ) + t * I) - G 2) * (x : ℂ) ^ ((2 : ℂ) + t * I)
      / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))
      = fun t : ℝ => H t + (D ((2 : ℂ) + t * I) - D 2) * kern x t + c2 * kern x t := by
    funext t
    have hz : 1 < ((2 : ℂ) + t * I).re := by rw [hsre]; norm_num
    rw [hH_eq, hLS _ hz, hc2']
    simp only [kern, ofReal_natCast]
    ring
  have hgamma : gammaPart χ x = (1 / (2 * Real.pi) : ℂ) *
      ((∫ t, H t) + (∫ t : ℝ, (D ((2 : ℂ) + t * I) - D 2) * kern x t)
        + c2 * ∫ t, kern x t) := by
    unfold gammaPart
    rw [← hG, hF2, integral_add _ ((integrable_kern hx0).const_mul _),
      integral_add hH_int hF1_int, integral_const_mul]
    exact hH_int.add hF1_int
  /- Assemble. -/
  have hbach : bachSum χ x = ∑ n ∈ Finset.Ioo 0 x, a n * (1 - (n : ℂ) / x) := by
    unfold bachSum
    rw [show ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)
        = ∑ n ∈ Finset.range x, a n * (1 - (n : ℂ) / x) from
      Finset.sum_congr rfl fun n _ => by simp only [a]; ring]
    symm
    refine Finset.sum_subset (fun n hn => ?_) fun n hn hn' => ?_
    · rw [Finset.mem_Ioo] at hn; rw [Finset.mem_range]; omega
    · have : n = 0 := by rw [Finset.mem_Ioo] at hn'; rw [Finset.mem_range] at hn; omega
      subst this
      simp [a]
  have hbach' : bachSum χ x = (1 / (2 * Real.pi) : ℂ) * ∫ t, H t := by
    rw [hbach, hP]
  have hK := integral_kern hx1
  have htsum : ∑' ρ : {ρ : ℂ // Λf ρ = 0}, m ρ * (-(2 * Real.pi) * zeroTerm x ρ)
      = -(2 * Real.pi) * ∑' ρ : {ρ : ℂ // Λf ρ = 0}, m ρ * zeroTerm x ρ := by
    rw [← tsum_mul_left]
    exact tsum_congr fun ρ => by ring
  rw [hgamma, hbach', hF1_integral, htsum, hK]
  simp only [ofReal_natCast]
  field_simp
  ring

end Erdos985.Analytic
