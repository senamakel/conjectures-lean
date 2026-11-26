import LLS.Analytic.Log.Gamma

/-!
# The log-weighted explicit formula (an exact identity)

For `χ` primitive and non-trivial mod `N` and `x ≥ 1`:
`S(x, χ) = −Σ_ρ m_ρ (x^ρ − 1)/ρ² − D(0) log x + (Γ̃(x) + G(2) log x)`.

Proof (as erdos-985's `explicit_formula`, with the kernel `x^s/s²`): Perron on `Re s = 2`,
`−L'/L = −(D − D(2)) + (G − G(2)) − L'/L(2)`, Hadamard for `D − D(2)`, and term-by-term
integration with `perron_lres`; finally `Σ m(1/ρ + 1/(2−ρ)) = D(2) − b`, `b = D(0)`.
-/

namespace LLS.LogAux

open Complex ArithmeticFunction MeasureTheory Erdos985 Erdos985.Analytic
  Erdos985.Analytic.PerronAux Erdos985.Analytic.IdentityAux
open scoped Classical

/-- The paired Hadamard term times the log kernel. -/
noncomputable def lpair (x : ℝ) (ρ : ℂ) (t : ℝ) : ℂ :=
  (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * lkern x t

lemma lpair_eq (x : ℝ) (ρ : ℂ) (t : ℝ) :
    lpair x ρ t = pairTerm x ρ t * (((2 : ℂ) + t * I + 1) / ((2 : ℂ) + t * I)) := by
  unfold lpair pairTerm
  rw [lkern_eq]; ring

lemma lpair_eq' (x : ℝ) (ρ : ℂ) (hρ : ρ.re < 2) (t : ℝ) :
    lpair x ρ t = lres x ρ t - (1 / (2 - ρ)) * lkern x t := by
  unfold lpair lres lkern
  have h0 := line_ne_zero2 t
  have h2 := line_sub_ne_zero' hρ t
  field_simp

lemma integrable_lpair {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ : ρ.re < 2) : Integrable (lpair x ρ) := by
  rw [show lpair x ρ = fun t => lres x ρ t - (1 / (2 - ρ)) * lkern x t from
    funext (lpair_eq' x ρ hρ)]
  exact (integrable_lres hx hρ).sub ((integrable_lkern hx).const_mul _)

lemma integral_lpair {x : ℝ} (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re < 2) (hρ0 : ρ ≠ 0) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t, lpair x ρ t
      = (x : ℂ) ^ ρ / ρ ^ 2 - (Real.log x : ℂ) / ρ - 1 / ρ ^ 2 - (Real.log x : ℂ) / (2 - ρ) := by
  have hx0 : 0 < x := by linarith
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  rw [show lpair x ρ = fun t => lres x ρ t - (1 / (2 - ρ)) * lkern x t from
    funext (lpair_eq' x ρ hρ), integral_sub (integrable_lres hx0 hρ)
    ((integrable_lkern hx0).const_mul _), integral_const_mul, mul_sub, perron_lres x hx ρ hρ hρ0,
    integral_lkern hx]
  field_simp

theorem integral_norm_lpair_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ∀ ρ : ℂ, ρ.re < 1 → ρ ≠ 0 →
      ∫ t, ‖lpair x ρ t‖ ≤ C * x ^ (2 : ℝ) / ‖ρ‖ ^ (1 + 1 / 2 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := integral_norm_pairTerm_le
  refine ⟨3 / 2 * C, by positivity, fun x hx ρ hρ hρ0 => ?_⟩
  have hρ2 : ρ.re < 2 := by linarith
  have hpt : ∀ t, ‖lpair x ρ t‖ ≤ 3 / 2 * ‖pairTerm x ρ t‖ := fun t => by
    rw [lpair_eq, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_add_one_div_le t) (norm_nonneg _)
  calc ∫ t, ‖lpair x ρ t‖ ≤ ∫ t, 3 / 2 * ‖pairTerm x ρ t‖ :=
        integral_mono (integrable_lpair hx hρ2).norm
          ((integrable_pairTerm hx hρ2).norm.const_mul _) hpt
    _ = 3 / 2 * ∫ t, ‖pairTerm x ρ t‖ := integral_const_mul _ _
    _ ≤ 3 / 2 * (C * x ^ (2 : ℝ) / ‖ρ‖ ^ (1 + 1 / 2 : ℝ)) := by gcongr; exact hC x hx ρ hρ hρ0
    _ = _ := by ring

variable {N : ℕ} [NeZero N]

/-- The log-weighted explicit formula. -/
theorem log_explicit_formula {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (x : ℕ) (hx : 1 ≤ x) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0} =>
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ)
          * (((x : ℂ) ^ (ρ : ℂ) - 1) / (ρ : ℂ) ^ 2)) ∧
    logSum χ x
      = -(∑' ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0},
            (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ)
              * (((x : ℂ) ^ (ρ : ℂ) - 1) / (ρ : ℂ) ^ 2))
        - D χ 0 * (Real.log x : ℂ) + (lgammaPart χ x + gammaLogDeriv χ 2 * (Real.log x : ℂ)) := by
  set Λf := DirichletCharacter.completedLFunction χ with hΛf
  set L := DirichletCharacter.LFunction χ with hL
  set G := gammaLogDeriv χ with hG
  set Dz : ℂ → ℂ := fun z => deriv Λf z / Λf z with hD
  set m : {ρ : ℂ // Λf ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt Λf ρ : ℂ) with hm
  set c2 : ℂ := deriv L 2 / L 2 with hc2
  set lx : ℂ := (Real.log x : ℂ) with hlx
  have := countable_zeros hprim hχ
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have hsre : ∀ t : ℝ, ((2 : ℂ) + t * I).re = 2 := fun t => by simp
  have hs_cont : Continuous fun t : ℝ => (2 : ℂ) + t * I := continuous_line
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
  have hρ0 : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, (ρ : ℂ) ≠ 0 :=
    fun ρ h => (hzre ρ).1.ne' (by simp [h])
  /- the zero family -/
  let F : {ρ : ℂ // Λf ρ = 0} → ℝ → ℂ := fun ρ t => m ρ * lpair x ρ t
  have hF_int : ∀ ρ, Integrable (F ρ) := fun ρ =>
    (integrable_lpair hx0 (by linarith [hzre ρ])).const_mul _
  obtain ⟨C, hC0, hC⟩ := integral_norm_lpair_le
  have hF_sum : Summable fun ρ => ∫ t, ‖F ρ t‖ := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun ρ => ?_) ((hsum_ε (1 / 2) (by norm_num)).mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    simp only [F, m, norm_mul, Complex.norm_natCast, integral_const_mul]
    calc (analyticOrderNatAt Λf ρ : ℝ) * ∫ t, ‖lpair x ρ t‖
        ≤ (analyticOrderNatAt Λf ρ : ℝ) * (C * (x : ℝ) ^ (2 : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hC x hx0 ρ (hzre ρ).2 (hρ0 ρ)) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hF_hasSum : ∀ t : ℝ, HasSum (fun ρ => F ρ t) ((Dz ((2 : ℂ) + t * I) - Dz 2) * lkern x t) := by
    intro t
    obtain ⟨h1s, h1e⟩ := hb ((2 : ℂ) + t * I) (hΛne _ (by rw [hsre]; norm_num))
    obtain ⟨h2s, h2e⟩ := hb 2 (hΛne _ (by norm_num))
    have := (h1s.hasSum.sub h2s.hasSum).mul_right (lkern x t)
    convert this using 1
    · funext ρ
      simp only [F, m, lpair]
      ring
    · simp only [hD]
      rw [h1e, h2e]
      ring
  have hD_cont : Continuous fun t : ℝ => Dz ((2 : ℂ) + t * I) := by
    have hcd : Continuous (deriv Λf) := (hΛd.contDiff (n := 1)).continuous_deriv le_rfl
    exact (hcd.comp hs_cont).div (hΛd.continuous.comp hs_cont)
      (fun t => hΛne _ (by simp))
  have hF1_int : Integrable fun t : ℝ => (Dz ((2 : ℂ) + t * I) - Dz 2) * lkern x t :=
    integrable_of_hasSum
      ((hD_cont.sub continuous_const).aestronglyMeasurable.mul (integrable_lkern hx0).1)
      hF_int hF_sum hF_hasSum
  set Rρ : {ρ : ℂ // Λf ρ = 0} → ℂ := fun ρ => (x : ℂ) ^ (ρ : ℂ) / (ρ : ℂ) ^ 2
    - lx / ρ - 1 / (ρ : ℂ) ^ 2 - lx / (2 - ρ) with hRρ
  have hF1_integral : (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, (Dz ((2 : ℂ) + t * I) - Dz 2) * lkern x t = ∑' ρ, m ρ * Rρ ρ := by
    rw [show (fun t : ℝ => (Dz ((2 : ℂ) + t * I) - Dz 2) * lkern x t)
        = fun t => ∑' ρ, F ρ t from funext fun t => (hF_hasSum t).tsum_eq.symm,
      ← integral_tsum_of_summable_integral_norm hF_int hF_sum, ← tsum_mul_left]
    refine tsum_congr fun ρ => ?_
    simp only [F]
    rw [integral_const_mul, mul_left_comm,
      integral_lpair hx1 (by linarith [hzre ρ]) (hρ0 ρ)]
    simp only [hRρ, hlx, ofReal_natCast]
  /- Perron -/
  set a : ℕ → ℂ := fun n => (χ n : ℂ) * (Λ n : ℂ) with ha
  have ha_sum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (2 : ℝ) := by
    have hs := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (s := 2)
      (by norm_num)).norm
    refine hs.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, a]
  have hP := perron_log_weighted a ha_sum x hx
  have hLS : ∀ z : ℂ, 1 < z.re → LSeries a z = -(Dz z - G z) := fun z hz => by
    have h1 := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hz
    have h2 := logDeriv_LFunction_eq hχ hz
    rw [← DirichletCharacter.LFunction_eq_LSeries χ hz,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hz] at h1
    change LSeries a z = _ at h1
    rw [h1, neg_div, h2]
  have hc2' : c2 = Dz 2 - G 2 := logDeriv_LFunction_eq hχ (by norm_num)
  set H : ℝ → ℂ := fun t => LSeries a ((2 : ℂ) + t * I) * lkern x t with hH
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
    refine Integrable.mono' ((integrable_lkern hx0).norm.const_mul B)
      (hcont.aestronglyMeasurable.mul (integrable_lkern hx0).1)
      (Filter.Eventually.of_forall fun t => ?_)
    simp only [hH]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbd t) (norm_nonneg _)
  have hF2 : (fun t : ℝ => (G ((2 : ℂ) + t * I) - G 2) * lkern x t)
      = fun t : ℝ => H t + (Dz ((2 : ℂ) + t * I) - Dz 2) * lkern x t + c2 * lkern x t := by
    funext t
    have hz : 1 < ((2 : ℂ) + t * I).re := by rw [hsre]; norm_num
    simp only [hH]
    rw [hLS _ hz, hc2']
    ring
  have hgamma : lgammaPart χ x = (1 / (2 * Real.pi) : ℂ) *
      ((∫ t, H t) + (∫ t : ℝ, (Dz ((2 : ℂ) + t * I) - Dz 2) * lkern x t)
        + c2 * ∫ t, lkern x t) := by
    unfold lgammaPart
    have e : (fun t : ℝ => (gammaLogDeriv χ (2 + t * I) - gammaLogDeriv χ 2) * lkern x t)
        = fun t : ℝ => (G ((2 : ℂ) + t * I) - G 2) * lkern x t := rfl
    rw [e, hF2, integral_add _ ((integrable_lkern hx0).const_mul _),
      integral_add hH_int hF1_int, integral_const_mul]
    exact hH_int.add hF1_int
  have hlog : logSum χ x = (1 / (2 * Real.pi) : ℂ) * ∫ t, H t := by
    unfold logSum
    rw [show ∑ n ∈ Finset.range (x + 1), (Λ n : ℂ) * χ n * (Real.log ((x : ℝ) / n) : ℂ)
        = ∑ n ∈ Finset.range (x + 1), a n * (Real.log ((x : ℝ) / n) : ℂ) from
      Finset.sum_congr rfl fun n _ => by simp only [a]; ring, hP]
  have hK : (1 / (2 * Real.pi) : ℂ) * ∫ t, lkern x t = lx := by
    rw [integral_lkern hx1, ← mul_assoc, one_div_mul_cancel hpi, one_mul]
  -- the identity before splitting the zero sum
  have hmain : logSum χ x = lgammaPart χ x - ∑' ρ, m ρ * Rρ ρ - c2 * lx := by
    rw [hlog, hgamma, ← hF1_integral, ← hK]
    ring
  /- splitting the zero sum -/
  have hsq : Summable fun ρ : {ρ : ℂ // Λf ρ = 0} =>
      (analyticOrderNatAt Λf ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2 := by
    have := hsum_ε 1 one_pos
    refine this.congr fun ρ => ?_
    norm_num
  have hS1 : Summable fun ρ : {ρ : ℂ // Λf ρ = 0} => m ρ * (((x : ℂ) ^ (ρ : ℂ) - 1) / (ρ : ℂ) ^ 2) := by
    refine Summable.of_norm_bounded (hsq.mul_left ((x : ℝ) + 1)) fun ρ => ?_
    rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow]
    have h1 : ‖(x : ℂ) ^ (ρ : ℂ) - 1‖ ≤ (x : ℝ) + 1 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one]
      have : ‖(x : ℂ) ^ (ρ : ℂ)‖ = (x : ℝ) ^ (ρ : ℂ).re := by
        rw [show (x : ℂ) = ((x : ℝ) : ℂ) by simp, norm_cpow_eq_rpow_re_of_pos hx0]
      rw [this]
      have : (x : ℝ) ^ (ρ : ℂ).re ≤ (x : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (hzre ρ).2.le
      rw [Real.rpow_one] at this
      linarith
    have hρp : 0 < ‖(ρ : ℂ)‖ ^ 2 := by have := norm_pos_iff.2 (hρ0 ρ); positivity
    rw [mul_div_assoc', div_le_iff₀ hρp]
    calc (analyticOrderNatAt Λf ρ : ℝ) * ‖(x : ℂ) ^ (ρ : ℂ) - 1‖
        ≤ (analyticOrderNatAt Λf ρ : ℝ) * ((x : ℝ) + 1) := by gcongr
      _ = _ := by rw [mul_assoc, div_mul_cancel₀ _ hρp.ne']; ring
  obtain ⟨h2s, h2e⟩ := hb 2 (hΛne _ (by norm_num))
  obtain ⟨h0s, h0e⟩ := hb 0 (completedLFunction_zero_ne_zero χ hχ hprim)
  have h0e' : Dz 0 = b := by
    simp only [hD]
    rw [h0e]
    have : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, (analyticOrderNatAt Λf ρ : ℂ) * (1 / (0 - ρ) + 1 / ρ) = 0 :=
      fun ρ => by
        rw [zero_sub, one_div_neg_eq_neg_one_div, neg_add_cancel, mul_zero]
    simp [this]
  have hsplit : ∑' ρ, m ρ * Rρ ρ = ∑' ρ : {ρ : ℂ // Λf ρ = 0},
        m ρ * (((x : ℂ) ^ (ρ : ℂ) - 1) / (ρ : ℂ) ^ 2)
      - lx * ∑' ρ : {ρ : ℂ // Λf ρ = 0}, m ρ * (1 / (2 - ρ) + 1 / ρ) := by
    rw [← tsum_mul_left, ← hS1.tsum_sub (h2s.mul_left lx)]
    refine tsum_congr fun ρ => ?_
    simp only [hRρ, m]
    have := hρ0 ρ
    have h2 : (2 : ℂ) - ρ ≠ 0 := two_sub_ne_zero' (by linarith [hzre ρ])
    field_simp
    ring
  have hD2 : ∑' ρ : {ρ : ℂ // Λf ρ = 0}, m ρ * (1 / (2 - ρ) + 1 / ρ) = Dz 2 - Dz 0 := by
    rw [h0e']; simp only [hD]; rw [h2e]; ring
  refine ⟨hS1, ?_⟩
  rw [hmain, hsplit, hD2, hc2']
  simp only [LLS.D, hD, hlx, hG, m]
  ring

end LLS.LogAux
