import LLS.L1.ShiftAux.Deriv

/-!
# The log-weighted explicit formula with a real shift `σ > 1` (an exact identity)

With `a(n) = χ(n)Λ(n)n^{−σ}` (so `L_a(s) = −L'/L(s + σ)`), Perron on `Re s = 2` and the
decomposition `−L'/L(z) = −(D(z) − D(u)) + (G(z) − G(u)) − L'/L(u)`, `u = 2 + σ`, give
`Σ_{n≤x} a(n) log(x/n) = −Σ_ρ m_ρ R(ρ − σ) − Σ_k R(−(σ + m_k)) − L'/L(u) log x`
with `R(w) = x^w/w² − log x/w − 1/w² − log x/(2 − w)` (`LLS.LogAux.integral_lpair`).
-/

namespace LLS.ShiftLogAux

open Complex ArithmeticFunction MeasureTheory Erdos985 Erdos985.Analytic
  Erdos985.Analytic.PerronAux Erdos985.Analytic.IdentityAux Erdos985.Analytic.BoundsAux LLS.LogAux
open scoped Classical

/-- The value of one paired residue integral. -/
noncomputable def Rw (x : ℝ) (w : ℂ) : ℂ :=
  (x : ℂ) ^ w / w ^ 2 - (Real.log x : ℂ) / w - 1 / w ^ 2 - (Real.log x : ℂ) / (2 - w)

variable {N : ℕ} [NeZero N]

/-- The shifted identity. -/
theorem shifted_identity (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 1 ≤ x) (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0} =>
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ)
          * Rw x ((ρ : ℂ) - σ)) ∧
    Summable (fun k : ℕ => Rw x (-((σ : ℂ) + ((2 * k + parity χ : ℕ) : ℂ)))) ∧
    ∑ n ∈ Finset.range (x + 1),
        (Λ n : ℂ) * χ n * (n : ℂ) ^ (-(σ : ℂ)) * (Real.log ((x : ℝ) / n) : ℂ)
      = -(∑' ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0},
            (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ)
              * Rw x ((ρ : ℂ) - σ))
        - (∑' k : ℕ, Rw x (-((σ : ℂ) + ((2 * k + parity χ : ℕ) : ℂ))))
        - deriv (DirichletCharacter.LFunction χ) (2 + σ)
            / DirichletCharacter.LFunction χ (2 + σ) * (Real.log x : ℂ) := by
  set Λf := DirichletCharacter.completedLFunction χ with hΛf
  set L := DirichletCharacter.LFunction χ with hL
  set G := gammaLogDeriv χ with hG
  set Dz : ℂ → ℂ := fun z => deriv Λf z / Λf z with hD
  set m : {ρ : ℂ // Λf ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt Λf ρ : ℂ) with hm
  set u : ℂ := 2 + σ with hu
  set cu : ℂ := deriv L u / L u with hcu
  set lx : ℂ := (Real.log x : ℂ) with hlx
  set mk : ℕ → ℂ := fun k => ((2 * k + parity χ : ℕ) : ℂ) with hmk
  set w : {ρ : ℂ // Λf ρ = 0} → ℂ := fun ρ => (ρ : ℂ) - σ with hw
  set wk : ℕ → ℂ := fun k => -((σ : ℂ) + mk k) with hwk
  have := countable_zeros hprim hχ
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have hs_cont : Continuous fun t : ℝ => (2 : ℂ) + t * I := continuous_line
  have hz_cont : Continuous fun t : ℝ => (2 : ℂ) + t * I + σ := hs_cont.add continuous_const
  have hzre : ∀ t : ℝ, ((2 : ℂ) + t * I + σ).re = 2 + σ := fun t => by simp
  have hure : u.re = 2 + σ := by simp [hu]
  have hΛd : Differentiable ℂ Λf := DirichletCharacter.differentiable_completedLFunction hχ
  have hLd : Differentiable ℂ L := DirichletCharacter.differentiable_LFunction hχ
  have hΛne : ∀ z : ℂ, 1 ≤ z.re → Λf z ≠ 0 := fun z hz =>
    DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hz
  have hLne : ∀ z : ℂ, 1 ≤ z.re → L z ≠ 0 := fun z hz =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hz
  obtain ⟨hsum_ε, b, hb⟩ := hadamard_logDeriv hΛd (completedLFunction_zero_ne_zero χ hχ hprim)
    (completedLFunction_growth χ hχ)
  have hre : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => completedLFunction_zero_re hGRH hprim hχ ρ.2
  have hwre : ∀ ρ, (w ρ).re = 1 / 2 - σ := fun ρ => by simp [w, hre ρ]
  have hw0 : ∀ ρ, w ρ ≠ 0 := fun ρ h => by
    have := hwre ρ; rw [h] at this; simp at this; linarith
  have hwnorm : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, ‖(ρ : ℂ)‖ ≤ ‖w ρ‖ := fun ρ => by
    have := (norm_le_norm_sub (hre ρ) hσ).1
    rw [show w ρ = -((σ : ℂ) - ρ) by simp [w], norm_neg]; exact this
  have hρ0 : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, (ρ : ℂ) ≠ 0 := fun ρ h => by
    have := hre ρ; rw [h] at this; norm_num at this
  have hmkre : ∀ k : ℕ, (k : ℝ) ≤ (mk k).re := fun k => by
    simp only [mk, natCast_re]; push_cast; linarith [(Nat.cast_nonneg (parity χ) : (0 : ℝ) ≤ _)]
  have hwkre : ∀ k, (wk k).re = -(σ + (mk k).re) := fun k => by simp [wk]
  have hwknorm : ∀ k : ℕ, (k : ℝ) + 1 ≤ ‖wk k‖ := fun k => by
    have := Complex.abs_re_le_norm (wk k)
    rw [hwkre, abs_neg, abs_of_pos (by linarith [hmkre k])] at this
    linarith [hmkre k]
  have hwk0 : ∀ k, wk k ≠ 0 := fun k h => by
    have := hwknorm k; rw [h, norm_zero] at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  /- the zero family -/
  let F : {ρ : ℂ // Λf ρ = 0} → ℝ → ℂ := fun ρ t => m ρ * lpair x (w ρ) t
  have hF_int : ∀ ρ, Integrable (F ρ) := fun ρ =>
    (integrable_lpair hx0 (by rw [hwre]; linarith)).const_mul _
  obtain ⟨C, hC0, hC⟩ := integral_norm_lpair_le
  have hF_sum : Summable fun ρ => ∫ t, ‖F ρ t‖ := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun ρ => ?_) ((hsum_ε (1 / 2) (by norm_num)).mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    simp only [F, m, norm_mul, Complex.norm_natCast, integral_const_mul]
    have hpos : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.2 (hρ0 ρ)
    have h1 := hC x hx0 (w ρ) (by rw [hwre]; linarith) (hw0 ρ)
    have h2 : C * (x : ℝ) ^ (2 : ℝ) / ‖w ρ‖ ^ (1 + 1 / 2 : ℝ)
        ≤ C * (x : ℝ) ^ (2 : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact Real.rpow_le_rpow hpos.le (hwnorm ρ) (by norm_num)
    calc (analyticOrderNatAt Λf ρ : ℝ) * ∫ t, ‖lpair x (w ρ) t‖
        ≤ (analyticOrderNatAt Λf ρ : ℝ) * (C * (x : ℝ) ^ (2 : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hF_hasSum : ∀ t : ℝ, HasSum (fun ρ => F ρ t)
      ((Dz ((2 : ℂ) + t * I + σ) - Dz u) * lkern x t) := by
    intro t
    obtain ⟨h1s, h1e⟩ := hb ((2 : ℂ) + t * I + σ) (hΛne _ (by rw [hzre]; linarith))
    obtain ⟨h2s, h2e⟩ := hb u (hΛne _ (by rw [hure]; linarith))
    have := (h1s.hasSum.sub h2s.hasSum).mul_right (lkern x t)
    convert this using 1
    · funext ρ
      simp only [F, m, lpair, w, hu]
      have e1 : (2 : ℂ) + t * I - ((ρ : ℂ) - σ) = (2 : ℂ) + t * I + σ - ρ := by ring
      have e2 : (2 : ℂ) - ((ρ : ℂ) - σ) = 2 + σ - ρ := by ring
      rw [e1, e2]
      ring
    · simp only [hD]
      rw [h1e, h2e]
      ring
  have hD_cont : Continuous fun t : ℝ => Dz ((2 : ℂ) + t * I + σ) := by
    have hcd : Continuous (deriv Λf) := (hΛd.contDiff (n := 1)).continuous_deriv le_rfl
    exact (hcd.comp hz_cont).div (hΛd.continuous.comp hz_cont)
      (fun t => hΛne _ (by rw [hzre]; linarith))
  have hF1_int : Integrable fun t : ℝ => (Dz ((2 : ℂ) + t * I + σ) - Dz u) * lkern x t :=
    integrable_of_hasSum
      ((hD_cont.sub continuous_const).aestronglyMeasurable.mul (integrable_lkern hx0).1)
      hF_int hF_sum hF_hasSum
  have hF1_integral : (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, (Dz ((2 : ℂ) + t * I + σ) - Dz u) * lkern x t = ∑' ρ, m ρ * Rw x (w ρ) := by
    rw [show (fun t : ℝ => (Dz ((2 : ℂ) + t * I + σ) - Dz u) * lkern x t)
        = fun t => ∑' ρ, F ρ t from funext fun t => (hF_hasSum t).tsum_eq.symm,
      ← integral_tsum_of_summable_integral_norm hF_int hF_sum, ← tsum_mul_left]
    refine tsum_congr fun ρ => ?_
    simp only [F]
    rw [integral_const_mul, mul_left_comm,
      integral_lpair hx1 (by rw [hwre]; linarith) (hw0 ρ)]
    rfl
  /- the gamma family -/
  let Gk : ℕ → ℝ → ℂ := fun k t => lpair x (wk k) t
  have hGk_int : ∀ k, Integrable (Gk k) := fun k =>
    integrable_lpair hx0 (by rw [hwkre]; linarith [hmkre k])
  have hGk_sum : Summable fun k => ∫ t, ‖Gk k t‖ := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun k => ?_) (summable_rpow32.mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    have h1 := hC x hx0 (wk k) (by rw [hwkre]; linarith [hmkre k]) (hwk0 k)
    refine h1.trans ?_
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hb1 : 1 / ‖wk k‖ ^ (1 + 1 / 2 : ℝ) ≤ ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.rpow_neg hk.le, ← one_div, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact Real.rpow_le_rpow hk.le (hwknorm k) (by norm_num)
    calc C * (x : ℝ) ^ (2 : ℝ) / ‖wk k‖ ^ (1 + 1 / 2 : ℝ)
        = C * (x : ℝ) ^ (2 : ℝ) * (1 / ‖wk k‖ ^ (1 + 1 / 2 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb1 (by positivity)
  have hGk_hasSum : ∀ t : ℝ, HasSum (fun k => Gk k t)
      (-(G ((2 : ℂ) + t * I + σ) - G u) * lkern x t) := by
    intro t
    have h1 := hasSum_gammaLogDeriv χ (s := (2 : ℂ) + t * I + σ) (by rw [hzre]; linarith)
    have h2 := hasSum_gammaLogDeriv χ (s := u) (by rw [hure]; linarith)
    have := ((h2.sub h1).mul_right (lkern x t))
    convert this using 1
    · funext k
      simp only [Gk, lpair, wk, mk]
      ring
    · simp only [hG]; ring
  /- Perron -/
  set a : ℕ → ℂ := fun n => (χ n : ℂ) * (Λ n : ℂ) * (n : ℂ) ^ (-(σ : ℂ)) with ha
  set a0 : ℕ → ℂ := fun n => (χ n : ℂ) * (Λ n : ℂ) with ha0
  have hterm : ∀ (z : ℂ) (n : ℕ), LSeries.term a z n = LSeries.term a0 (z + σ) n := by
    intro z n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
      have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      simp only [a, a0]
      rw [cpow_add _ _ hnc, cpow_neg]
      field_simp
  have hLa : ∀ z : ℂ, LSeries a z = LSeries a0 (z + σ) := fun z => by
    unfold LSeries; exact tsum_congr (hterm z)
  have ha_sum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (2 : ℝ) := by
    have hs := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (s := 2 + σ)
      (by simp; linarith)).norm
    refine hs.congr fun n => ?_
    have e := hterm 2 n
    rw [show (2 : ℂ) + σ = 2 + (σ : ℂ) from rfl] at e
    change ‖LSeries.term a0 (2 + σ) n‖ = _
    rw [← e, LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [a]
    · simp only [hn, ↓reduceIte]
      norm_num
  have hP := perron_log_weighted a ha_sum x hx
  have hLS : ∀ z : ℂ, 1 < z.re → LSeries a0 z = -(Dz z - G z) := fun z hz => by
    have h1 := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hz
    have h2 := logDeriv_LFunction_eq hχ hz
    rw [← DirichletCharacter.LFunction_eq_LSeries χ hz,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hz] at h1
    change LSeries a0 z = _ at h1
    rw [h1, neg_div, h2]
  have hcu' : cu = Dz u - G u := logDeriv_LFunction_eq hχ (by rw [hure]; linarith)
  set H : ℝ → ℂ := fun t => LSeries a ((2 : ℂ) + t * I) * lkern x t with hH
  have hH_eq : ∀ t, H t = -(Dz ((2 : ℂ) + t * I + σ) - G ((2 : ℂ) + t * I + σ)) * lkern x t :=
    fun t => by simp only [hH]; rw [hLa, hLS _ (by rw [hzre]; linarith)]
  have hH_int : Integrable H := by
    have hcont : Continuous fun t : ℝ => LSeries a ((2 : ℂ) + t * I) := by
      have hcd : Continuous (deriv L) := (hLd.contDiff (n := 1)).continuous_deriv le_rfl
      have : (fun t : ℝ => LSeries a ((2 : ℂ) + t * I))
          = fun t : ℝ => -(deriv L ((2 : ℂ) + t * I + σ) / L ((2 : ℂ) + t * I + σ)) := by
        funext t
        have hz : 1 < ((2 : ℂ) + t * I + σ).re := by rw [hzre]; linarith
        rw [hLa, hLS _ hz, ← logDeriv_LFunction_eq hχ hz]
      rw [this]
      exact ((hcd.comp hz_cont).div (hLd.continuous.comp hz_cont)
        (fun t => hLne _ (by rw [hzre]; linarith))).neg
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
        funext n; rw [LSeries.norm_term_eq, LSeries.norm_term_eq]; simp
      calc ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ ∑' n, ‖LSeries.term a ((2 : ℂ) + t * I) n‖ :=
            norm_tsum_le_tsum_norm (by rw [heq]; exact hs2)
        _ = B := by rw [heq]
    refine Integrable.mono' ((integrable_lkern hx0).norm.const_mul B)
      (hcont.aestronglyMeasurable.mul (integrable_lkern hx0).1)
      (Filter.Eventually.of_forall fun t => ?_)
    simp only [hH]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbd t) (norm_nonneg _)
  /- the gamma family is integrable, as a combination of the others -/
  have hGsum_fun : (fun t : ℝ => ∑' k, Gk k t)
      = fun t => -H t - (Dz ((2 : ℂ) + t * I + σ) - Dz u) * lkern x t - cu * lkern x t := by
    funext t
    rw [(hGk_hasSum t).tsum_eq, hH_eq, hcu']
    ring
  have hGsum_int : Integrable fun t : ℝ => ∑' k, Gk k t := by
    rw [hGsum_fun]
    exact (hH_int.neg.sub hF1_int).sub ((integrable_lkern hx0).const_mul _)
  have hG_integral : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, ∑' k, Gk k t = ∑' k, Rw x (wk k) := by
    rw [← integral_tsum_of_summable_integral_norm hGk_int hGk_sum, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    simp only [Gk]
    rw [integral_lpair hx1 (by rw [hwkre]; linarith [hmkre k]) (hwk0 k)]
    rfl
  have hK : (1 / (2 * Real.pi) : ℂ) * ∫ t, lkern x t = lx := by
    rw [integral_lkern hx1, ← mul_assoc, one_div_mul_cancel hpi, one_mul]
  /- assemble -/
  have hHsplit : H = fun t : ℝ => -((Dz ((2 : ℂ) + t * I + σ) - Dz u) * lkern x t)
      - (∑' k, Gk k t) - cu * lkern x t := by
    funext t
    have h := congrFun hGsum_fun t
    rw [h]; ring
  have hint : ∫ t, H t = -(∫ t : ℝ, (Dz ((2 : ℂ) + t * I + σ) - Dz u) * lkern x t)
      - (∫ t : ℝ, ∑' k, Gk k t) - cu * ∫ t, lkern x t := by
    have i1 := integral_sub (hF1_int.neg.sub hGsum_int) ((integrable_lkern hx0).const_mul cu)
    have i2 := integral_sub hF1_int.neg hGsum_int
    simp only [Pi.neg_apply, Pi.sub_apply] at i1 i2
    rw [hHsplit]
    simp only
    rw [i1, i2, integral_neg, integral_const_mul]
  have hSsum : Summable (fun ρ => m ρ * Rw x (w ρ)) := by
    have hs : Summable fun ρ => (1 / (2 * Real.pi) : ℂ) * ∫ t, F ρ t := by
      refine Summable.of_norm_bounded (hF_sum.mul_left (1 / (2 * Real.pi))) fun ρ => ?_
      rw [norm_mul]
      have : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
        rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        simp
      rw [this]
      gcongr
      exact norm_integral_le_integral_norm _
    refine hs.congr fun ρ => ?_
    simp only [F]
    rw [integral_const_mul, mul_left_comm, integral_lpair hx1 (by rw [hwre]; linarith) (hw0 ρ)]
    rfl
  have hGsumm : Summable (fun k => Rw x (wk k)) := by
    have hs : Summable fun k => (1 / (2 * Real.pi) : ℂ) * ∫ t, Gk k t := by
      refine Summable.of_norm_bounded (hGk_sum.mul_left (1 / (2 * Real.pi))) fun k => ?_
      rw [norm_mul]
      have : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
        rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        simp
      rw [this]
      gcongr
      exact norm_integral_le_integral_norm _
    refine hs.congr fun k => ?_
    simp only [Gk]
    rw [integral_lpair hx1 (by rw [hwkre]; linarith [hmkre k]) (hwk0 k)]
    rfl
  refine ⟨hSsum, hGsumm, ?_⟩
  have hlhs : ∑ n ∈ Finset.range (x + 1),
        (Λ n : ℂ) * χ n * (n : ℂ) ^ (-(σ : ℂ)) * (Real.log ((x : ℝ) / n) : ℂ)
      = ∑ n ∈ Finset.range (x + 1), a n * (Real.log ((x : ℝ) / n) : ℂ) :=
    Finset.sum_congr rfl fun n _ => by simp only [a]; ring
  rw [hlhs, hP]
  change (1 / (2 * Real.pi) : ℂ) * ∫ t, H t = _
  rw [hint]
  have e : (1 / (2 * Real.pi) : ℂ) * (-(∫ t : ℝ, (Dz ((2 : ℂ) + t * I + σ) - Dz u) * lkern x t)
      - (∫ t : ℝ, ∑' k, Gk k t) - cu * ∫ t, lkern x t)
      = -((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (Dz ((2 : ℂ) + t * I + σ) - Dz u) * lkern x t)
        - (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, ∑' k, Gk k t)
        - cu * ((1 / (2 * Real.pi) : ℂ) * ∫ t, lkern x t) := by ring
  rw [e, hF1_integral, hG_integral, hK]

end LLS.ShiftLogAux
