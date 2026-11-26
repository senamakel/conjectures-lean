import Littlewood.Integrate

/-!
# Step 9: `log |ζ(σ₀ + it)|` from the integrated explicit formula

`key_bound` (RH): for `t ≥ 1`, `x > 1`, `1/2 < σ₀ ≤ 2` with `(σ₀ - 1/2) log x ≥ 1`,

    log x · (log |ζ(σ₀+it)| - log |ζ(2+it)|) ≤ 2 (x+1)(log x)² + 2 (x+1+S) + Re ξ'/ξ(2+it),

`S = Σ 1/(k+1)²`. The zero sum is integrated term by term (`integral_zeroSum_le`) and each zero
contributes at most `m Re 1/(2+it-ρ)` (`integral_zero_term_le`); these add up to `Re ξ'/ξ(2+it)`
(`hasSum_re_logDeriv_xi`).
-/

open Complex MeasureTheory ArithmeticFunction intervalIntegral Set

namespace Littlewood

open Erdos985.Analytic

/-- The zero term as a function of `σ`. -/
noncomputable def zeroTerm (x t : ℝ) (ρ : XiZero) (σ : ℝ) : ℂ :=
  mult ρ * (((x : ℂ) ^ ((ρ : ℂ) - ((σ : ℂ) + t * I)) - 1) / ((ρ : ℂ) - ((σ : ℂ) + t * I)) ^ 2)

lemma continuousOn_zeroTerm (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) (t : ℝ) (ρ : XiZero) :
    ContinuousOn (zeroTerm x t ρ) (Ioi (1 / 2)) := by
  have hρ : (ρ : ℂ).re = 1 / 2 := Lindelof.xiZeta_zero_re_of_RH hRH ρ.2
  have hcl : Continuous fun σ : ℝ => (ρ : ℂ) - ((σ : ℂ) + t * I) :=
    continuous_const.sub (continuous_ofReal.add continuous_const)
  have hcp : Continuous fun σ : ℝ => (x : ℂ) ^ ((ρ : ℂ) - ((σ : ℂ) + t * I)) :=
    hcl.const_cpow (Or.inl (by exact_mod_cast hx.ne'))
  refine continuousOn_const.mul (ContinuousOn.div (f := fun σ : ℝ => (x : ℂ) ^ ((ρ : ℂ) -
    ((σ : ℂ) + t * I)) - 1) (g := fun σ : ℝ => ((ρ : ℂ) - ((σ : ℂ) + t * I)) ^ 2)
    (hcp.sub continuous_const).continuousOn (hcl.pow 2).continuousOn fun σ hσ => ?_)
  exact pow_ne_zero 2 (sub_line_ne_zero hρ hσ t)

lemma norm_zeroTerm_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) (t : ℝ) (ρ : XiZero)
    {σ₀ σ : ℝ} (h0 : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) :
    ‖zeroTerm x t ρ σ‖ ≤ 2 * ((analyticOrderNatAt xiZeta ρ : ℝ) /
      normSq ((ρ : ℂ) - ((σ₀ : ℂ) + t * I))) := by
  have hρ : (ρ : ℂ).re = 1 / 2 := Lindelof.xiZeta_zero_re_of_RH hRH ρ.2
  have hx0 : 0 < x := by linarith
  have hpos : 0 < normSq ((ρ : ℂ) - ((σ₀ : ℂ) + t * I)) := normSq_pos.2 (sub_line_ne_zero hρ h0 t)
  have hmono := normSq_sub_line_mono hρ h0.le hσ t
  unfold zeroTerm
  rw [norm_mul, show ‖mult ρ‖ = (analyticOrderNatAt xiZeta ρ : ℝ) by simp [mult], norm_div,
    norm_pow, ← Complex.normSq_eq_norm_sq]
  have hnum : ‖(x : ℂ) ^ ((ρ : ℂ) - ((σ : ℂ) + t * I)) - 1‖ ≤ 2 := by
    calc _ ≤ ‖(x : ℂ) ^ ((ρ : ℂ) - ((σ : ℂ) + t * I))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
          rw [norm_cpow_eq_rpow_re_of_pos hx0, norm_one]
          gcongr
          exact Real.rpow_le_one_of_one_le_of_nonpos hx (by simp [hρ]; linarith)
      _ = 2 := by norm_num
  have hm : 0 ≤ (analyticOrderNatAt xiZeta ρ : ℝ) := Nat.cast_nonneg _
  calc (analyticOrderNatAt xiZeta ρ : ℝ) * (‖(x : ℂ) ^ ((ρ : ℂ) - ((σ : ℂ) + t * I)) - 1‖ /
        normSq ((ρ : ℂ) - ((σ : ℂ) + t * I)))
      ≤ (analyticOrderNatAt xiZeta ρ : ℝ) * (2 / normSq ((ρ : ℂ) - ((σ₀ : ℂ) + t * I))) := by
        gcongr
    _ = _ := by ring

/-- The integrated zero sum is at most `Re ξ'/ξ(2 + it)` (RH). -/
theorem integral_zeroSum_le (hRH : RiemannHypothesis) {t x σ₀ : ℝ} (hx : 1 < x)
    (h0 : 1 / 2 < σ₀) (h2 : σ₀ ≤ 2) (hηL : 1 ≤ (σ₀ - 1 / 2) * Real.log x) :
    IntervalIntegrable (fun σ : ℝ => (zeroSum ((σ : ℂ) + t * I) x).re) volume σ₀ 2 ∧
    ∫ σ in σ₀..2, (zeroSum ((σ : ℂ) + t * I) x).re
      ≤ (deriv xiZeta ((2 : ℂ) + t * I) / xiZeta ((2 : ℂ) + t * I)).re := by
  have := countable_xiZero
  have hx1 : 1 ≤ x := hx.le
  have hx0 : 0 < x := by linarith
  set s₀ : ℂ := (σ₀ : ℂ) + t * I with hs₀
  have hs₀re : 1 / 2 < s₀.re := by simp [hs₀]; linarith
  set u : XiZero → ℝ := fun ρ => 2 * ((analyticOrderNatAt xiZeta ρ : ℝ) / normSq ((ρ : ℂ) - s₀))
  have hu : Summable u := (summable_mult_div_normSq hRH hs₀re).mul_left 2
  have hIcc : Icc σ₀ 2 ⊆ Ioi (1 / 2) := fun σ hσ => lt_of_lt_of_le h0 hσ.1
  have hbd : ∀ ρ, ∀ σ ∈ Icc σ₀ 2, ‖zeroTerm x t ρ σ‖ ≤ u ρ := fun ρ σ hσ =>
    norm_zeroTerm_le hRH hx1 t ρ h0 hσ.1
  have hsum_at : ∀ σ ∈ Icc σ₀ 2, Summable fun ρ => zeroTerm x t ρ σ := fun σ hσ =>
    Summable.of_norm_bounded hu (fun ρ => hbd ρ σ hσ)
  have hzeq : ∀ σ ∈ Icc σ₀ 2, (zeroSum ((σ : ℂ) + t * I) x).re = ∑' ρ, (zeroTerm x t ρ σ).re := by
    intro σ hσ
    have := re_tsum (hsum_at σ hσ)
    exact this
  -- continuity on `[σ₀, 2]`
  have hcont : ContinuousOn (fun σ : ℝ => ∑' ρ, zeroTerm x t ρ σ) (Icc σ₀ 2) :=
    continuousOn_tsum (fun ρ => (continuousOn_zeroTerm hRH hx0 t ρ).mono hIcc) hu
      (fun ρ σ hσ => hbd ρ σ hσ)
  have hcontRe : ContinuousOn (fun σ : ℝ => (zeroSum ((σ : ℂ) + t * I) x).re) (Icc σ₀ 2) := by
    refine (continuous_re.comp_continuousOn hcont).congr fun σ hσ => ?_
    simp only [Function.comp, zeroSum]
    rfl
  have hII : IntervalIntegrable (fun σ : ℝ => (zeroSum ((σ : ℂ) + t * I) x).re) volume σ₀ 2 :=
    (hcontRe.mono (by rw [uIcc_of_le h2])).intervalIntegrable |>.mono_set (by rw [uIcc_of_le h2])
  refine ⟨by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le h2]; exact hcontRe, ?_⟩
  -- term by term on `Ioc σ₀ 2`
  set μ := volume.restrict (Ioc σ₀ 2)
  set F : XiZero → ℝ → ℝ := fun ρ σ => (zeroTerm x t ρ σ).re
  have hFint : ∀ ρ, Integrable (F ρ) μ := by
    intro ρ
    have : IntegrableOn (F ρ) (Icc σ₀ 2) :=
      (continuous_re.comp_continuousOn ((continuousOn_zeroTerm hRH hx0 t ρ).mono hIcc)).integrableOn_compact
        isCompact_Icc
    exact this.mono_set Ioc_subset_Icc_self
  have hFnorm : ∀ ρ, ∫ σ, ‖F ρ σ‖ ∂μ ≤ (2 - σ₀) * u ρ := by
    intro ρ
    have hle : ∀ σ ∈ Ioc σ₀ 2, ‖F ρ σ‖ ≤ u ρ := fun σ hσ =>
      (abs_re_le_norm _).trans (hbd ρ σ (Ioc_subset_Icc_self hσ))
    calc ∫ σ, ‖F ρ σ‖ ∂μ ≤ ∫ σ in Ioc σ₀ 2, u ρ :=
          setIntegral_mono_on (hFint ρ).norm (integrableOn_const (by simp) (by simp))
            measurableSet_Ioc hle
      _ = (2 - σ₀) * u ρ := by
          rw [setIntegral_const, Real.volume_real_Ioc_of_le h2, smul_eq_mul]
  have hFsum : Summable fun ρ => ∫ σ, ‖F ρ σ‖ ∂μ :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hFnorm
      (hu.mul_left _)
  have hswap := integral_tsum_of_summable_integral_norm hFint hFsum
  -- each zero
  have hper : ∀ ρ : XiZero, ∫ σ, F ρ σ ∂μ ≤
      (mult ρ * (1 / ((2 : ℂ) + t * I - ρ))).re := by
    intro ρ
    have hρ : (ρ : ℂ).re = 1 / 2 := Lindelof.xiZeta_zero_re_of_RH hRH ρ.2
    have hm : (mult ρ * (1 / ((2 : ℂ) + t * I - ρ))).re =
        (analyticOrderNatAt xiZeta ρ : ℝ) * (1 / ((2 : ℂ) + t * I - ρ)).re := by
      simp [mult]
    have hF : ∀ σ, F ρ σ = (analyticOrderNatAt xiZeta ρ : ℝ) *
        ((((x : ℂ) ^ ((ρ : ℂ) - ((σ : ℂ) + t * I)) - 1) / ((ρ : ℂ) - ((σ : ℂ) + t * I)) ^ 2)).re := by
      intro σ; simp [F, zeroTerm, mult]
    rw [hm]
    simp_rw [hF]
    rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le h2]
    exact mul_le_mul_of_nonneg_left (integral_zero_term_le hρ t hx h0 h2 hηL) (Nat.cast_nonneg _)
  -- assemble
  have hs₂ : 1 / 2 < ((2 : ℂ) + t * I).re := by simp; norm_num
  have hR := hasSum_re_logDeriv_xi hRH hs₂
  have hR' : HasSum (fun ρ : XiZero => (mult ρ * (1 / ((2 : ℂ) + t * I - ρ))).re)
      (deriv xiZeta ((2 : ℂ) + t * I) / xiZeta ((2 : ℂ) + t * I)).re := hR
  rw [intervalIntegral.integral_of_le h2]
  calc ∫ σ in Ioc σ₀ 2, (zeroSum ((σ : ℂ) + t * I) x).re
      = ∫ σ, ∑' ρ, F ρ σ ∂μ := by
        refine setIntegral_congr_fun measurableSet_Ioc fun σ hσ => ?_
        exact hzeq σ (Ioc_subset_Icc_self hσ)
    _ = ∑' ρ, ∫ σ, F ρ σ ∂μ := hswap.symm
    _ ≤ ∑' ρ : XiZero, (mult ρ * (1 / ((2 : ℂ) + t * I - ρ))).re :=
        Summable.tsum_le_tsum hper (hFsum.of_norm_bounded fun ρ =>
          (MeasureTheory.norm_integral_le_integral_norm _)) hR'.summable
    _ = _ := hR'.tsum_eq

/-- **The key bound** (RH). -/
theorem key_bound (hRH : RiemannHypothesis) {t x σ₀ : ℝ} (ht : 1 ≤ t) (hx : 1 < x)
    (h0 : 1 / 2 < σ₀) (h2 : σ₀ ≤ 2) (hηL : 1 ≤ (σ₀ - 1 / 2) * Real.log x) :
    Real.log x * (Real.log ‖riemannZeta (σ₀ + t * I)‖ - Real.log ‖riemannZeta (2 + t * I)‖)
      ≤ 2 * ((x + 1) * Real.log x ^ 2 + (x + 1 + ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2)) +
        (deriv xiZeta ((2 : ℂ) + t * I) / xiZeta ((2 : ℂ) + t * I)).re := by
  have hx1 : 1 ≤ x := hx.le
  set L := Real.log x with hLdef
  set S := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  have hL0 : 0 ≤ L := Real.log_nonneg hx1
  set C := (x + 1) * L ^ 2 + (x + 1 + S) with hC
  have hC0 : 0 ≤ C := by positivity
  rw [log_norm_zeta_sub_eq hRH ht h0 h2, ← intervalIntegral.integral_const_mul]
  obtain ⟨hZi, hZ⟩ := integral_zeroSum_le hRH (t := t) hx h0 h2 hηL
  have hg : IntervalIntegrable (fun σ : ℝ => L * (-(deriv riemannZeta (σ + t * I) /
      riemannZeta (σ + t * I))).re) volume σ₀ 2 := by
    refine ContinuousOn.intervalIntegrable ?_
    have := continuousOn_re_logDeriv_zeta hRH ht h0 h2
    simp only [neg_re]
    exact continuousOn_const.mul this.neg
  have hpt : ∀ σ ∈ Set.Icc σ₀ 2, L * (-(deriv riemannZeta (σ + t * I) /
      riemannZeta (σ + t * I))).re ≤ C + (zeroSum ((σ : ℂ) + t * I) x).re := by
    intro σ hσ
    have hσ0 : 1 / 2 < ((σ : ℂ) + t * I).re := by simp; linarith [hσ.1]
    have hne1 : (σ : ℂ) + t * I ≠ 1 := fun h => by
      have := congrArg im h; simp at this; linarith
    have hE := explicit_formula hRH hσ0 hne1 hx1
    have hre := congrArg re hE
    rw [re_ofReal_mul, sub_re, add_re] at hre
    rw [hre]
    have hD := (re_le_norm _).trans (norm_dirPoly_le (s := (σ : ℂ) + t * I)
      (by simp; linarith [hσ.1]) hx1)
    have hER := (neg_re _ ▸ (re_le_norm (-(ER ((σ : ℂ) + t * I) x)))).trans
      ((norm_neg _).le.trans (norm_ER_le (s := (σ : ℂ) + t * I) (by simp; linarith [hσ.1])
        (by simpa [abs_of_pos (by linarith : (0 : ℝ) < t)] using ht) hx1))
    linarith
  calc ∫ σ in σ₀..2, L * (-(deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I))).re
      ≤ ∫ σ in σ₀..2, (C + (zeroSum ((σ : ℂ) + t * I) x).re) :=
        intervalIntegral.integral_mono_on h2 hg (intervalIntegrable_const.add hZi) hpt
    _ = (2 - σ₀) * C + ∫ σ in σ₀..2, (zeroSum ((σ : ℂ) + t * I) x).re := by
        rw [intervalIntegral.integral_add intervalIntegrable_const hZi,
          intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ 2 * C + (deriv xiZeta ((2 : ℂ) + t * I) / xiZeta ((2 : ℂ) + t * I)).re := by
        have : (2 - σ₀) * C ≤ 2 * C := mul_le_mul_of_nonneg_right (by linarith) hC0
        linarith

end Littlewood
