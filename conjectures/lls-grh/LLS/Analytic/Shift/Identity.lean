import LLS.Analytic.Shift.Gamma

/-!
# The shifted Cesàro explicit formula (an exact identity, under GRH)

Perron's formula (`PerronKernel.perron_weighted`, line `Re s = 2`) for the coefficients
`a(n) = χ(n) Λ(n)/n`, whose `L`-series is `−L'/L(s + 1, χ)`. On the line,
`−L'/L(s+1) = −(D(s+1) − D(3)) + (G(s+1) − G(3)) − L'/L(3)`; Hadamard writes
`D(s+1) − D(3) = Σ_ρ m_ρ (1/(s − (ρ−1)) − 1/(2 − (ρ−1)))`, and each term integrates to
`−2π zeroTerm x (ρ − 1)` (`IdentityAux.integral_pairTerm` with the pole `w = ρ − 1`).

GRH is used only to make `Σ_ρ m_ρ/|ρ − 1|^{3/2}` summable (`|ρ − 1| = |ρ|` on the critical line).
-/

namespace LLS.ShiftAux

open Complex ArithmeticFunction MeasureTheory Erdos985 Erdos985.Analytic
open Erdos985.Analytic.IdentityAux
open scoped Classical

variable {N : ℕ} [NeZero N]

lemma norm_sub_one_eq {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ‖ρ - 1‖ = ‖ρ‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  simp only [Complex.normSq_apply, sub_re, one_re, sub_im, one_im, sub_zero, hρ]
  norm_num

lemma term_shift (χ : DirichletCharacter ℂ N) (z : ℂ) (n : ℕ) :
    LSeries.term (fun n : ℕ => (χ n : ℂ) * (Λ n : ℂ) / n) z n
      = LSeries.term (fun n : ℕ => (χ n : ℂ) * (Λ n : ℂ)) (z + 1) n := by
  rw [LSeries.term_def, LSeries.term_def]
  split_ifs with hn
  · rfl
  · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [cpow_add _ _ hn', cpow_one]
    have : (n : ℂ) ^ z ≠ 0 := by rw [cpow_ne_zero_iff]; left; exact hn'
    field_simp

lemma LSeries_shift (χ : DirichletCharacter ℂ N) (z : ℂ) :
    LSeries (fun n : ℕ => (χ n : ℂ) * (Λ n : ℂ) / n) z
      = LSeries (fun n : ℕ => (χ n : ℂ) * (Λ n : ℂ)) (z + 1) := by
  unfold LSeries
  exact tsum_congr fun n => term_shift χ z n

/-- The shifted Cesàro explicit formula (exact identity). -/
theorem shift_identity (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 1 ≤ x) :
    cesShift χ x
      = (∑' ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0},
            (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ)
              * zeroTerm x ((ρ : ℂ) - 1))
        + gammaPartS χ x
        - (1 - 1 / (x : ℂ)) * (deriv (DirichletCharacter.LFunction χ) 3
            / DirichletCharacter.LFunction χ 3) := by
  set Λf := DirichletCharacter.completedLFunction χ with hΛf
  set L := DirichletCharacter.LFunction χ with hL
  set G := gammaLogDeriv χ with hG
  set D : ℂ → ℂ := fun z => deriv Λf z / Λf z with hD
  set m : {ρ : ℂ // Λf ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt Λf ρ : ℂ) with hm
  set c3 : ℂ := deriv L 3 / L 3 with hc3
  have := countable_zeros hprim hχ
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hsre : ∀ t : ℝ, ((2 : ℂ) + t * I).re = 2 := fun t => by simp
  have hs_cont : Continuous fun t : ℝ => (2 : ℂ) + t * I :=
    continuous_const.add (continuous_ofReal.mul continuous_const)
  have hs1_cont : Continuous fun t : ℝ => (2 : ℂ) + t * I + 1 := hs_cont.add continuous_const
  have hΛd : Differentiable ℂ Λf := DirichletCharacter.differentiable_completedLFunction hχ
  have hLd : Differentiable ℂ L := DirichletCharacter.differentiable_LFunction hχ
  have hΛne : ∀ z : ℂ, 1 ≤ z.re → Λf z ≠ 0 := fun z hz =>
    DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hz
  have hLne : ∀ z : ℂ, 1 ≤ z.re → L z ≠ 0 := fun z hz =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hz
  obtain ⟨hsum_ε, b, hb⟩ := hadamard_logDeriv hΛd (completedLFunction_zero_ne_zero χ hχ hprim)
    (completedLFunction_growth χ hχ)
  have hzre : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 :=
    fun ρ => zero_re_mem hprim hχ ρ.2
  have hcrit : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => completedLFunction_zero_re hGRH hprim hχ ρ.2
  have hw2 : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, ((ρ : ℂ) - 1).re < 2 := fun ρ => by
    simp only [sub_re, one_re]; linarith [hzre ρ]
  have hw1 : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, ((ρ : ℂ) - 1).re < 1 := fun ρ => by
    simp only [sub_re, one_re]; linarith [hzre ρ]
  have hw0 : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, (ρ : ℂ) - 1 ≠ 0 := fun ρ h => by
    have := congrArg Complex.re h; simp at this; linarith [hzre ρ]
  have hwm1 : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, (ρ : ℂ) - 1 ≠ -1 := fun ρ h => by
    have := congrArg Complex.re h; simp at this; linarith [hzre ρ]
  /- The family of zero terms. -/
  let F : {ρ : ℂ // Λf ρ = 0} → ℝ → ℂ := fun ρ t => m ρ * pairTerm x ((ρ : ℂ) - 1) t
  have hF_int : ∀ ρ, Integrable (F ρ) := fun ρ =>
    (integrable_pairTerm hx0 (hw2 ρ)).const_mul _
  obtain ⟨C, hC0, hC⟩ := integral_norm_pairTerm_le
  have hF_sum : Summable fun ρ => ∫ t, ‖F ρ t‖ := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun ρ => ?_) ((hsum_ε (1 / 2) (by norm_num)).mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    simp only [F, m, norm_mul, Complex.norm_natCast, integral_const_mul]
    have h := hC x hx0 ((ρ : ℂ) - 1) (hw1 ρ) (hw0 ρ)
    rw [norm_sub_one_eq (hcrit ρ)] at h
    calc (analyticOrderNatAt Λf ρ : ℝ) * ∫ t, ‖pairTerm x ((ρ : ℂ) - 1) t‖
        ≤ (analyticOrderNatAt Λf ρ : ℝ) * (C * (x : ℝ) ^ (2 : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
      _ = _ := by ring
  have hF_hasSum : ∀ t : ℝ,
      HasSum (fun ρ => F ρ t) ((D ((2 : ℂ) + t * I + 1) - D 3) * kern x t) := by
    intro t
    obtain ⟨h1s, h1e⟩ := hb ((2 : ℂ) + t * I + 1) (hΛne _ (by norm_num))
    obtain ⟨h2s, h2e⟩ := hb 3 (hΛne _ (by norm_num))
    have := (h1s.hasSum.sub h2s.hasSum).mul_right (kern x t)
    convert this using 1
    · funext ρ
      simp only [F, m, pairTerm]
      have e1 : (2 : ℂ) + t * I - ((ρ : ℂ) - 1) = (2 : ℂ) + t * I + 1 - ρ := by ring
      have e2 : (2 : ℂ) - ((ρ : ℂ) - 1) = 3 - ρ := by ring
      rw [e1, e2]
      ring
    · simp only [hD]
      rw [h1e, h2e]
      ring
  have hD_cont : Continuous fun t : ℝ => D ((2 : ℂ) + t * I + 1) := by
    have hcd : Continuous (deriv Λf) := (hΛd.contDiff (n := 1)).continuous_deriv le_rfl
    exact (hcd.comp hs1_cont).div (hΛd.continuous.comp hs1_cont)
      (fun t => hΛne _ (by norm_num))
  have hF1_int : Integrable fun t : ℝ => (D ((2 : ℂ) + t * I + 1) - D 3) * kern x t :=
    integrable_of_hasSum
      ((hD_cont.sub continuous_const).aestronglyMeasurable.mul (integrable_kern hx0).1)
      hF_int hF_sum hF_hasSum
  have hF1_integral : ∫ t : ℝ, (D ((2 : ℂ) + t * I + 1) - D 3) * kern x t
      = ∑' ρ : {ρ : ℂ // Λf ρ = 0}, m ρ * (-(2 * Real.pi) * zeroTerm x ((ρ : ℂ) - 1)) := by
    rw [show (fun t : ℝ => (D ((2 : ℂ) + t * I + 1) - D 3) * kern x t)
        = fun t => ∑' ρ, F ρ t from funext fun t => (hF_hasSum t).tsum_eq.symm,
      ← integral_tsum_of_summable_integral_norm hF_int hF_sum]
    refine tsum_congr fun ρ => ?_
    simp only [F]
    rw [integral_const_mul, integral_pairTerm x hx (hw2 ρ) (hw0 ρ) (hwm1 ρ)]
  /- Perron. -/
  set a : ℕ → ℂ := fun n => (χ n : ℂ) * (Λ n : ℂ) / n with ha
  have ha_sum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (2 : ℝ) := by
    have hs := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (s := 3)
      (by norm_num)).norm
    refine hs.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [a]
    · have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
      simp only [hn, ↓reduceIte, a, norm_div, Complex.norm_natCast, re_ofNat]
      rw [show ((n : ℝ)) ^ (3 : ℝ) = (n : ℝ) ^ (2 : ℝ) * n by
        rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.rpow_add hn0, Real.rpow_one]]
      field_simp
      rfl
  have hP := PerronKernel.perron_weighted a 2 two_pos ha_sum x hx
  simp only [ofReal_ofNat] at hP
  have hLS : ∀ z : ℂ, 1 < z.re → LSeries a z = -(D (z + 1) - G (z + 1)) := fun z hz => by
    have hz1 : 1 < (z + 1).re := by simp only [add_re, one_re]; linarith
    have h1 := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hz1
    have h2 := logDeriv_LFunction_eq hχ hz1
    rw [← DirichletCharacter.LFunction_eq_LSeries χ hz1,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hz1] at h1
    rw [LSeries_shift]
    change LSeries (fun n => (χ n : ℂ) * (Λ n : ℂ)) (z + 1) = _
    simp only [Pi.mul_def] at h1
    rw [h1, neg_div, h2]
  have hc3' : c3 = D 3 - G 3 := logDeriv_LFunction_eq hχ (by norm_num)
  set H : ℝ → ℂ := fun t => LSeries a ((2 : ℂ) + t * I) * (x : ℂ) ^ ((2 : ℂ) + t * I)
    / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) with hH
  have hH_eq : ∀ t : ℝ, H t = LSeries a ((2 : ℂ) + t * I) * kern x t := fun t => by
    simp only [hH, kern, ofReal_natCast]
    ring
  have hH_int : Integrable H := by
    have hcont : Continuous fun t : ℝ => LSeries a ((2 : ℂ) + t * I) := by
      have hcd : Continuous (deriv L) := (hLd.contDiff (n := 1)).continuous_deriv le_rfl
      have : (fun t : ℝ => LSeries a ((2 : ℂ) + t * I))
          = fun t : ℝ => -(deriv L ((2 : ℂ) + t * I + 1) / L ((2 : ℂ) + t * I + 1)) := by
        funext t
        have hz : 1 < ((2 : ℂ) + t * I).re := by rw [hsre]; norm_num
        have hz1 : 1 < ((2 : ℂ) + t * I + 1).re := by simp
        rw [hLS _ hz, ← logDeriv_LFunction_eq hχ hz1]
      rw [this]
      exact ((hcd.comp hs1_cont).div (hLd.continuous.comp hs1_cont)
        (fun t => hLne _ (by norm_num))).neg
    set B := ∑' n, ‖LSeries.term a 2 n‖
    have hs2 : Summable fun n => ‖LSeries.term a 2 n‖ := by
      refine ha_sum.congr fun n => ?_
      rw [LSeries.norm_term_eq]
      rcases eq_or_ne n 0 with rfl | hn
      · simp [a]
      · simp [hn]
    have hbd : ∀ t : ℝ, ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ B := fun t => by
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
  have hF2 : (fun t : ℝ => (G ((2 : ℂ) + t * I + 1) - G 3) * (x : ℂ) ^ ((2 : ℂ) + t * I)
      / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))
      = fun t : ℝ => H t + (D ((2 : ℂ) + t * I + 1) - D 3) * kern x t + c3 * kern x t := by
    funext t
    have hz : 1 < ((2 : ℂ) + t * I).re := by rw [hsre]; norm_num
    rw [hH_eq, hLS _ hz, hc3']
    simp only [kern, ofReal_natCast]
    ring
  have hgamma : gammaPartS χ x = (1 / (2 * Real.pi) : ℂ) *
      ((∫ t, H t) + (∫ t : ℝ, (D ((2 : ℂ) + t * I + 1) - D 3) * kern x t)
        + c3 * ∫ t, kern x t) := by
    unfold gammaPartS
    rw [← hG, hF2, integral_add _ ((integrable_kern hx0).const_mul _),
      integral_add hH_int hF1_int, integral_const_mul]
    exact hH_int.add hF1_int
  /- Assemble. -/
  have hces : cesShift χ x = ∑ n ∈ Finset.Ioo 0 x, a n * (1 - (n : ℂ) / x) := by
    unfold cesShift
    rw [show ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n / n * (1 - (n : ℂ) / x)
        = ∑ n ∈ Finset.range x, a n * (1 - (n : ℂ) / x) from
      Finset.sum_congr rfl fun n _ => by simp only [a]; ring]
    symm
    refine Finset.sum_subset (fun n hn => ?_) fun n hn hn' => ?_
    · rw [Finset.mem_Ioo] at hn; rw [Finset.mem_range]; omega
    · have : n = 0 := by rw [Finset.mem_Ioo] at hn'; rw [Finset.mem_range] at hn; omega
      subst this
      simp [a]
  have hces' : cesShift χ x = (1 / (2 * Real.pi) : ℂ) * ∫ t, H t := by
    rw [hces, hP]
  have hK := integral_kern hx1
  have htsum : ∑' ρ : {ρ : ℂ // Λf ρ = 0}, m ρ * (-(2 * Real.pi) * zeroTerm x ((ρ : ℂ) - 1))
      = -(2 * Real.pi) * ∑' ρ : {ρ : ℂ // Λf ρ = 0}, m ρ * zeroTerm x ((ρ : ℂ) - 1) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun ρ => by ring
  rw [hgamma, hces', hF1_integral, htsum, hK]
  simp only [ofReal_natCast]
  field_simp
  ring

end LLS.ShiftAux
