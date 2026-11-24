import Littlewood.Bound
import Littlewood.Main
import Mertens.InvZeta

/-!
# A lower bound for `log |ζ(σ₀ + it)|` near the half line (RH), for `t ≥ 1`

This is littlewood-rh's integrated explicit formula (`Littlewood.key_bound`) read in the other
direction. Write `L = log x`, `η = σ₀ - 1/2`, `s₀ = σ₀ + it`, `W = Re ξ'/ξ(s₀) = Σ m η/|s₀-ρ|²`.

1. `integral_zero_term_ge`: one zero, integrated over `[σ₀, 2]`, contributes at least
   `-2 η/|s₀-ρ|²` once `η L ≥ 1`; so the integrated zero sum is `≥ -2W` (`integral_zeroSum_ge`).
2. `re_logDeriv_xi_le` (Selberg's device): the explicit formula *at* `s₀` gives
   `L ‖ζ'/ζ(s₀)‖ ≤ C + 2W/η`, and `W ≤ ‖ζ'/ζ(s₀)‖ + ‖R(s₀)‖`; once `η L ≥ 4` this gives
   `W ≤ 2C/L + 2‖R(s₀)‖`, i.e. `W ≪ log t` with no loss in `1/η`.
3. `norm_inv_zeta_le_large`: `L (log|ζ(s₀)| - log|ζ(2+it)|) ≥ -2C - 2W`, hence
   `1/|ζ(s₀)| ≤ exp(A + (4C + 4 log(3+t) + 20)/L)` with `C = (x+1)L² + x + 1 + S`.
-/

open Complex MeasureTheory intervalIntegral Set

namespace Mertens

open Littlewood Erdos985.Analytic

/-- **One zero, integrated, from below.** -/
theorem integral_zero_term_ge {ρ : ℂ} (hρ : ρ.re = 1 / 2) (t : ℝ) {x σ₀ : ℝ} (hx : 1 < x)
    (h0 : 1 / 2 < σ₀) (h2 : σ₀ ≤ 2) (hηL : 1 ≤ (σ₀ - 1 / 2) * Real.log x) :
    -(2 * ((σ₀ - 1 / 2) / normSq (ρ - ((σ₀ : ℂ) + t * I)))) ≤
      ∫ σ in σ₀..2, ((((x : ℂ) ^ (ρ - ((σ : ℂ) + t * I)) - 1) / (ρ - ((σ : ℂ) + t * I)) ^ 2)).re := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  set c : ℂ := ρ - t * I with hc
  have hb : ∀ σ : ℝ, ρ - ((σ : ℂ) + t * I) = c - σ := fun σ => by rw [hc]; ring
  have hne : ∀ σ : ℝ, 1 / 2 < σ → c - σ ≠ 0 := fun σ hσ => by
    rw [← hb]; exact sub_line_ne_zero hρ hσ t
  have hsub : Set.uIcc σ₀ 2 ⊆ Set.Ioi (1 / 2) := by
    intro σ hσ; rw [Set.uIcc_of_le h2] at hσ; exact lt_of_lt_of_le h0 hσ.1
  have hcl : Continuous fun σ : ℝ => c - (σ : ℂ) := continuous_const.sub continuous_ofReal
  have hcl2 : Continuous fun σ : ℝ => (c - (σ : ℂ)) ^ 2 := hcl.pow 2
  have hcp : Continuous fun σ : ℝ => (x : ℂ) ^ (c - (σ : ℂ)) :=
    hcl.const_cpow (Or.inl (by exact_mod_cast hx0.ne'))
  have hcont1 : ContinuousOn (fun σ : ℝ => (1 / (c - σ) ^ 2 : ℂ)) (Set.uIcc σ₀ 2) :=
    ContinuousOn.div (f := fun _ => (1 : ℂ)) (g := fun σ : ℝ => (c - (σ : ℂ)) ^ 2)
      continuousOn_const hcl2.continuousOn fun σ hσ => pow_ne_zero 2 (hne σ (hsub hσ))
  have hcont2 : ContinuousOn (fun σ : ℝ => ((x : ℂ) ^ (c - σ) / (c - σ) ^ 2 : ℂ)) (Set.uIcc σ₀ 2) :=
    ContinuousOn.div (f := fun σ : ℝ => (x : ℂ) ^ (c - (σ : ℂ)))
      (g := fun σ : ℝ => (c - (σ : ℂ)) ^ 2) hcp.continuousOn hcl2.continuousOn
      fun σ hσ => pow_ne_zero 2 (hne σ (hsub hσ))
  have hsplit : ∀ σ : ℝ, ((((x : ℂ) ^ (ρ - ((σ : ℂ) + t * I)) - 1) / (ρ - ((σ : ℂ) + t * I)) ^ 2)).re
      = ((x : ℂ) ^ (c - σ) / (c - σ) ^ 2).re - (1 / (c - σ) ^ 2 : ℂ).re := by
    intro σ; rw [hb, sub_div, sub_re, one_div]
  simp_rw [hsplit]
  have hi1 : IntervalIntegrable (fun σ : ℝ => (1 / (c - σ) ^ 2 : ℂ).re) volume σ₀ 2 :=
    (continuous_re.comp_continuousOn hcont1).intervalIntegrable
  have hi2 : IntervalIntegrable (fun σ : ℝ => ((x : ℂ) ^ (c - σ) / (c - σ) ^ 2).re) volume σ₀ 2 :=
    (continuous_re.comp_continuousOn hcont2).intervalIntegrable
  rw [integral_sub hi2 hi1]
  have hexact : ∫ σ in σ₀..2, (1 / (c - σ) ^ 2 : ℂ).re
      = (1 / (c - 2)).re - (1 / (c - σ₀)).re := by
    refine integral_eq_sub_of_hasDerivAt (f := fun σ : ℝ => (1 / (c - σ)).re) (fun σ hσ => ?_) hi1
    have hz : c - (σ : ℂ) ≠ 0 := hne σ (hsub hσ)
    have hd : HasDerivAt (fun z : ℂ => 1 / (c - z)) (1 / (c - σ) ^ 2) (σ : ℂ) := by
      have := ((hasDerivAt_id (σ : ℂ)).const_sub c).inv hz
      convert this using 1
      · funext z; simp
      · simp
    exact hd.real_of_complex
  rw [hexact]
  set d0 := normSq (ρ - ((σ₀ : ℂ) + t * I)) with hd0
  have hd0pos : 0 < d0 := normSq_pos.2 (sub_line_ne_zero hρ h0 t)
  have hbound : ∀ σ ∈ Set.Icc σ₀ 2,
      -(x ^ (1 / 2 - σ) / d0) ≤ ((x : ℂ) ^ (c - σ) / (c - σ) ^ 2).re := by
    intro σ hσ
    have h1 := abs_re_le_norm ((x : ℂ) ^ (c - σ) / (c - σ) ^ 2)
    have h2 := neg_abs_le (((x : ℂ) ^ (c - σ) / (c - σ) ^ 2).re)
    have h3 : ‖(x : ℂ) ^ (c - σ) / (c - σ) ^ 2‖ ≤ x ^ (1 / 2 - σ) / d0 := by
      rw [norm_div, norm_pow, norm_cpow_eq_rpow_re_of_pos hx0]
      have hre : (c - σ).re = 1 / 2 - σ := by simp [hc, hρ]
      rw [hre, ← hb σ, ← Complex.normSq_eq_norm_sq]
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) hd0pos
        (normSq_sub_line_mono hρ h0.le hσ.1 t)
    linarith
  have hint2 : -(1 / Real.log x / d0) ≤ ∫ σ in σ₀..2, ((x : ℂ) ^ (c - σ) / (c - σ) ^ 2).re := by
    have hcr : Continuous fun σ : ℝ => x ^ (1 / 2 - σ) :=
      continuous_const.rpow (continuous_const.sub continuous_id) fun _ => Or.inl hx0.ne'
    calc -(1 / Real.log x / d0) ≤ -((∫ σ in σ₀..2, x ^ (1 / 2 - σ)) / d0) := by
          rw [neg_le_neg_iff]
          gcongr; exact integral_rpow_le hx h0.le h2
      _ = ∫ σ in σ₀..2, -(x ^ (1 / 2 - σ) / d0) := by
          rw [intervalIntegral.integral_neg, intervalIntegral.integral_div]
      _ ≤ ∫ σ in σ₀..2, ((x : ℂ) ^ (c - σ) / (c - σ) ^ 2).re :=
          integral_mono_on h2 ((hcr.div_const _).neg.intervalIntegrable _ _) hi2 hbound
  have hre0 : (1 / (c - σ₀)).re = -((σ₀ - 1 / 2) / d0) := by
    rw [← hb σ₀, one_div, inv_re]
    simp [hρ, hd0]
    ring
  have hre2 : (1 / (c - 2)).re = -(1 / ((2 : ℂ) + t * I - ρ)).re := by
    rw [show c - 2 = -((2 : ℂ) + t * I - ρ) by rw [hc]; ring, one_div, one_div, inv_neg, neg_re]
  have hpos2 : 0 ≤ (1 / ((2 : ℂ) + t * I - ρ)).re := by
    rw [one_div, inv_re]
    apply div_nonneg _ (normSq_nonneg _)
    simp [hρ]; norm_num
  rw [hre0, hre2]
  have key : 1 / Real.log x / d0 ≤ (σ₀ - 1 / 2) / d0 := by
    gcongr
    rw [div_le_iff₀ hL]; linarith
  linarith

lemma normSq_sub_comm (a b : ℂ) : normSq (a - b) = normSq (b - a) := by
  rw [← normSq_neg, neg_sub]

/-- The integrated zero sum is at least `-2 Re ξ'/ξ(σ₀ + it)` (RH). -/
theorem integral_zeroSum_ge (hRH : RiemannHypothesis) {t x σ₀ : ℝ} (hx : 1 < x)
    (h0 : 1 / 2 < σ₀) (h2 : σ₀ ≤ 2) (hηL : 1 ≤ (σ₀ - 1 / 2) * Real.log x) :
    IntervalIntegrable (fun σ : ℝ => (zeroSum ((σ : ℂ) + t * I) x).re) volume σ₀ 2 ∧
    -(2 * (deriv xiZeta ((σ₀ : ℂ) + t * I) / xiZeta ((σ₀ : ℂ) + t * I)).re) ≤
      ∫ σ in σ₀..2, (zeroSum ((σ : ℂ) + t * I) x).re := by
  have := countable_xiZero
  have hx1 : 1 ≤ x := hx.le
  have hx0 : 0 < x := by linarith
  set s₀ : ℂ := (σ₀ : ℂ) + t * I with hs₀
  have hs₀re : 1 / 2 < s₀.re := by simp [hs₀]; linarith
  set u : XiZero → ℝ := fun ρ => 2 * ((analyticOrderNatAt xiZeta ρ : ℝ) / normSq ((ρ : ℂ) - s₀))
  have hu : Summable u := (summable_mult_div_normSq hRH hs₀re).mul_left 2
  have hIcc : Icc σ₀ 2 ⊆ Ioi (1 / 2) := fun σ hσ => lt_of_lt_of_le h0 hσ.1
  have hbd : ∀ ρ, ∀ σ ∈ Icc σ₀ 2, ‖Littlewood.zeroTerm x t ρ σ‖ ≤ u ρ := fun ρ σ hσ =>
    norm_zeroTerm_le hRH hx1 t ρ h0 hσ.1
  have hsum_at : ∀ σ ∈ Icc σ₀ 2, Summable fun ρ => Littlewood.zeroTerm x t ρ σ := fun σ hσ =>
    Summable.of_norm_bounded hu (fun ρ => hbd ρ σ hσ)
  have hzeq : ∀ σ ∈ Icc σ₀ 2, (zeroSum ((σ : ℂ) + t * I) x).re = ∑' ρ, (Littlewood.zeroTerm x t ρ σ).re := by
    intro σ hσ
    exact re_tsum (hsum_at σ hσ)
  have hcont : ContinuousOn (fun σ : ℝ => ∑' ρ, Littlewood.zeroTerm x t ρ σ) (Icc σ₀ 2) :=
    continuousOn_tsum (fun ρ => (continuousOn_zeroTerm hRH hx0 t ρ).mono hIcc) hu
      (fun ρ σ hσ => hbd ρ σ hσ)
  have hcontRe : ContinuousOn (fun σ : ℝ => (zeroSum ((σ : ℂ) + t * I) x).re) (Icc σ₀ 2) := by
    refine (continuous_re.comp_continuousOn hcont).congr fun σ hσ => ?_
    simp only [Function.comp, zeroSum]
    rfl
  refine ⟨by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le h2]; exact hcontRe, ?_⟩
  set μ := volume.restrict (Ioc σ₀ 2)
  set F : XiZero → ℝ → ℝ := fun ρ σ => (Littlewood.zeroTerm x t ρ σ).re
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
  have hper : ∀ ρ : XiZero, -(2 * (mult ρ * (1 / (s₀ - ρ))).re) ≤ ∫ σ, F ρ σ ∂μ := by
    intro ρ
    have hρ : (ρ : ℂ).re = 1 / 2 := Lindelof.xiZeta_zero_re_of_RH hRH ρ.2
    have hm : (mult ρ * (1 / (s₀ - ρ))).re = (analyticOrderNatAt xiZeta ρ : ℝ) *
        ((σ₀ - 1 / 2) / normSq ((ρ : ℂ) - ((σ₀ : ℂ) + t * I))) := by
      rw [re_mult_div hRH s₀ ρ, normSq_sub_comm]
      simp [hs₀]
    have hF : ∀ σ, F ρ σ = (analyticOrderNatAt xiZeta ρ : ℝ) *
        ((((x : ℂ) ^ ((ρ : ℂ) - ((σ : ℂ) + t * I)) - 1) / ((ρ : ℂ) - ((σ : ℂ) + t * I)) ^ 2)).re := by
      intro σ; simp [F, Littlewood.zeroTerm, mult]
    rw [hm]
    simp_rw [hF]
    rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le h2]
    have h := mul_le_mul_of_nonneg_left (integral_zero_term_ge hρ t hx h0 h2 hηL)
      (Nat.cast_nonneg (analyticOrderNatAt xiZeta ρ))
    linarith
  have hR := hasSum_re_logDeriv_xi hRH hs₀re
  have hR2 := hR.mul_left (-2)
  rw [intervalIntegral.integral_of_le h2]
  calc -(2 * (deriv xiZeta s₀ / xiZeta s₀).re)
      = ∑' ρ : XiZero, -2 * (mult ρ * (1 / (s₀ - ρ))).re := by rw [hR2.tsum_eq]; ring
    _ ≤ ∑' ρ, ∫ σ, F ρ σ ∂μ :=
        Summable.tsum_le_tsum (fun ρ => by linarith [hper ρ]) hR2.summable
          (hFsum.of_norm_bounded fun ρ => (MeasureTheory.norm_integral_le_integral_norm _))
    _ = ∫ σ, ∑' ρ, F ρ σ ∂μ := hswap
    _ = ∫ σ in Ioc σ₀ 2, (zeroSum ((σ : ℂ) + t * I) x).re := by
        refine setIntegral_congr_fun measurableSet_Ioc fun σ hσ => ?_
        exact (hzeq σ (Ioc_subset_Icc_self hσ)).symm

/-- `‖R(s)‖ ≤ log (3 + |t|) + 5` for `0 ≤ σ ≤ 2`, `|t| ≥ 1`. -/
theorem norm_archR_le {s : ℂ} (h0 : 0 ≤ s.re) (h2 : s.re ≤ 2) (ht : 1 ≤ |s.im|) :
    ‖archR s‖ ≤ Real.log (3 + |s.im|) + 5 := by
  have h1 : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one₀]
    · exact ht.trans (le_trans (by simp) (abs_im_le_norm _))
    · exact lt_of_lt_of_le one_pos (ht.trans (le_trans (by simp) (abs_im_le_norm _)))
  have hpi : Real.log Real.pi ≤ 3 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_d2]
  have hpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  set A : ℂ := 1 / (s - 1)
  set B : ℂ := -(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)
  set C : ℂ := (1 / 2 : ℂ) * digamma (1 + s / 2)
  have h2' : ‖B‖ ≤ 3 / 2 := by
    simp only [B]
    rw [norm_mul, norm_neg, norm_real, Real.norm_of_nonneg hpi0]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this]; linarith
  have hw : 0 ≤ (s / 2).re := by simp; linarith
  have h3 := norm_digamma_one_add_le hw
  have hn : ‖s / 2‖ ≤ 1 + |s.im| := by
    rw [norm_div]
    have h := norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg h0] at h
    simp only [Complex.norm_ofNat]
    linarith [abs_nonneg s.im]
  have hlog : Real.log (2 + ‖s / 2‖) ≤ Real.log (3 + |s.im|) :=
    Real.log_le_log (by positivity) (by linarith)
  have hC : ‖C‖ ≤ (1 / 2) * (2 * Real.log (3 + |s.im|) + 3) := by
    simp only [C]
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    linarith
  have heq : archR s = A + B + C := by
    simp only [archR, A, B, C]; ring
  rw [heq]
  have := norm_add₃_le (a := A) (b := B) (c := C)
  linarith

/-- **Selberg's device** (RH): for `t ≥ 1` and `(σ₀ - 1/2) log x ≥ 4`,
`Re ξ'/ξ(σ₀+it) ≤ 2C/log x + 2‖R(σ₀+it)‖`, `C = (x+1)(log x)² + x + 1 + S`. -/
theorem re_logDeriv_xi_le (hRH : RiemannHypothesis) {t x σ₀ : ℝ} (ht : 1 ≤ t) (hx : 1 < x)
    (h0 : 1 / 2 < σ₀) (h2 : σ₀ ≤ 2) (h4 : 4 ≤ (σ₀ - 1 / 2) * Real.log x) :
    (deriv xiZeta ((σ₀ : ℂ) + t * I) / xiZeta ((σ₀ : ℂ) + t * I)).re ≤
      2 * ((x + 1) * Real.log x ^ 2 + (x + 1 + ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2)) / Real.log x +
        2 * ‖archR ((σ₀ : ℂ) + t * I)‖ := by
  have := countable_xiZero
  have hx1 : 1 ≤ x := hx.le
  set L := Real.log x with hLdef
  have hL : 0 < L := Real.log_pos hx
  set S := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 with hS
  set C := (x + 1) * L ^ 2 + (x + 1 + S) with hC
  set s₀ : ℂ := (σ₀ : ℂ) + t * I with hs₀
  set η := σ₀ - 1 / 2 with hη
  have hη0 : 0 < η := by linarith
  have hs₀re : 1 / 2 < s₀.re := by simp [hs₀]; linarith
  have hne1 : s₀ ≠ 1 := fun h => by have := congrArg im h; simp [hs₀] at this; linarith
  have hζ : riemannZeta s₀ ≠ 0 := Lindelof.riemannZeta_ne_zero_of_RH hRH hs₀re hne1
  set W := (deriv xiZeta s₀ / xiZeta s₀).re with hW
  have hR := hasSum_re_logDeriv_xi hRH hs₀re
  have hterm : ∀ ρ : XiZero, (mult ρ * (1 / (s₀ - ρ))).re =
      η * ((analyticOrderNatAt xiZeta ρ : ℝ) / normSq ((ρ : ℂ) - s₀)) := by
    intro ρ
    rw [re_mult_div hRH s₀ ρ, normSq_sub_comm]
    simp [hs₀, hη]
    ring
  simp_rw [hterm] at hR
  have hW0 : 0 ≤ W := hR.nonneg fun ρ =>
    mul_nonneg hη0.le (div_nonneg (Nat.cast_nonneg _) (normSq_nonneg _))
  have hsumm := summable_mult_div_normSq hRH hs₀re
  have hsig : ∑' ρ : XiZero, (analyticOrderNatAt xiZeta ρ : ℝ) / normSq ((ρ : ℂ) - s₀) = W / η := by
    rw [hW, ← hR.tsum_eq, tsum_mul_left]; field_simp
  -- the zero sum at `s₀`
  have hZ : ‖zeroSum s₀ x‖ ≤ 2 * (W / η) := by
    set u : XiZero → ℝ := fun ρ => 2 * ((analyticOrderNatAt xiZeta ρ : ℝ) / normSq ((ρ : ℂ) - s₀))
    have hu : Summable u := hsumm.mul_left 2
    have hb : ∀ ρ, ‖Littlewood.zeroTerm x t ρ σ₀‖ ≤ u ρ := fun ρ => norm_zeroTerm_le hRH hx1 t ρ h0 le_rfl
    have hsn : Summable fun ρ => ‖Littlewood.zeroTerm x t ρ σ₀‖ :=
      hu.of_nonneg_of_le (fun _ => norm_nonneg _) hb
    have heq : zeroSum s₀ x = ∑' ρ, Littlewood.zeroTerm x t ρ σ₀ := rfl
    rw [heq]
    calc ‖∑' ρ, Littlewood.zeroTerm x t ρ σ₀‖ ≤ ∑' ρ, ‖Littlewood.zeroTerm x t ρ σ₀‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' ρ, u ρ := hsn.tsum_le_tsum hb hu
      _ = 2 * (W / η) := by rw [tsum_mul_left, hsig]
  -- the explicit formula at `s₀`
  have hE := explicit_formula hRH hs₀re hne1 hx1
  have hD := norm_dirPoly_le (s := s₀) (by simp [hs₀]; linarith) hx1
  have hER := norm_ER_le (s := s₀) (by simp [hs₀]; linarith)
    (by simpa [hs₀, abs_of_pos (by linarith : (0 : ℝ) < t)] using ht) hx1
  have hlog : L * ‖deriv riemannZeta s₀ / riemannZeta s₀‖ ≤ C + 2 * (W / η) := by
    have h := congrArg norm hE
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hL.le] at h
    rw [h]
    calc ‖dirPoly s₀ x + zeroSum s₀ x - ER s₀ x‖
        ≤ ‖dirPoly s₀ x‖ + ‖zeroSum s₀ x‖ + ‖ER s₀ x‖ := by
          refine (norm_sub_le _ _).trans ?_
          linarith [norm_add_le (dirPoly s₀ x) (zeroSum s₀ x)]
      _ ≤ C + 2 * (W / η) := by rw [hC]; linarith
  have hxi : deriv xiZeta s₀ / xiZeta s₀ = deriv riemannZeta s₀ / riemannZeta s₀ + archR s₀ := by
    rw [logDeriv_riemannZeta_eq_archR (by linarith) hne1 hζ]; ring
  have hWle : W ≤ ‖deriv riemannZeta s₀ / riemannZeta s₀‖ + ‖archR s₀‖ := by
    rw [hW, hxi, add_re]
    linarith [re_le_norm (deriv riemannZeta s₀ / riemannZeta s₀), re_le_norm (archR s₀)]
  -- `2W/η ≤ L W / 2`
  have hk : 2 * (W / η) ≤ L * W / 2 := by
    rw [div_eq_mul_inv]
    have : 2 * η⁻¹ ≤ L / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hη0]; nlinarith
    nlinarith
  have hmain : L * W ≤ 2 * C + 2 * L * ‖archR s₀‖ := by nlinarith
  rw [div_add' _ _ _ hL.ne', le_div_iff₀ hL]
  nlinarith

/-- `log |ζ(2 + it)| ≥ -A₀` for all `t`. -/
lemma log_norm_zeta_two_ge : ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ t : ℝ,
    -A₀ ≤ Real.log ‖riemannZeta (2 + t * I)‖ := by
  obtain ⟨C₂, hC₂⟩ := norm_inv_zeta_le_of_two_le
  refine ⟨Real.log (max C₂ 1), Real.log_nonneg (le_max_right _ _), fun t => ?_⟩
  have hζ : riemannZeta (2 + t * I) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
  have hpos : 0 < ‖(riemannZeta (2 + t * I))⁻¹‖ := norm_pos_iff.2 (inv_ne_zero hζ)
  have h1 := hC₂ (2 + t * I) (by simp)
  have h2 : Real.log ‖(riemannZeta (2 + t * I))⁻¹‖ ≤ Real.log (max C₂ 1) :=
    Real.log_le_log hpos (h1.trans (le_max_left _ _))
  rw [norm_inv, Real.log_inv] at h2
  linarith

/-- **The lower bound for large `t`** (RH): for `t ≥ 1`, `x ≥ e²`, `σ₀ ≤ 2` and
`(σ₀ - 1/2) log x ≥ 4`, `1/|ζ(σ₀+it)| ≤ exp(A + (4C + 4 log(3+t) + 20)/log x)`. -/
theorem norm_inv_zeta_le_large (hRH : RiemannHypothesis) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ t x σ₀ : ℝ, 1 ≤ t → Real.exp 2 ≤ x → 1 / 2 < σ₀ → σ₀ ≤ 2 →
      4 ≤ (σ₀ - 1 / 2) * Real.log x →
      ‖(riemannZeta ((σ₀ : ℂ) + t * I))⁻¹‖ ≤ Real.exp (A +
        (4 * ((x + 1) * Real.log x ^ 2 + (x + 1 + ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2)) +
          4 * Real.log (3 + t) + 20) / Real.log x) := by
  obtain ⟨A₀, hA₀, hA₀t⟩ := log_norm_zeta_two_ge
  refine ⟨A₀, hA₀, fun t x σ₀ ht hx h0 h2 h4 => ?_⟩
  have hx1 : 1 < x := lt_of_lt_of_le (by have := Real.add_one_le_exp (2 : ℝ); linarith) hx
  have hL2 : 2 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hx
  set L := Real.log x with hLdef
  have hL : 0 < L := by linarith
  set S := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  set C := (x + 1) * L ^ 2 + (x + 1 + S) with hC
  have hC0 : 0 ≤ C := by positivity
  have hηL : 1 ≤ (σ₀ - 1 / 2) * L := by linarith
  set s₀ : ℂ := (σ₀ : ℂ) + t * I with hs₀
  set W := (deriv xiZeta s₀ / xiZeta s₀).re with hW
  have hWb := re_logDeriv_xi_le hRH ht hx1 h0 h2 h4
  have hR := norm_archR_le (s := s₀) (by simp [hs₀]; linarith) (by simp [hs₀]; exact h2)
    (by simpa [hs₀, abs_of_pos (by linarith : (0 : ℝ) < t)] using ht)
  have him : s₀.im = t := by simp [hs₀]
  rw [him, abs_of_pos (by linarith : (0 : ℝ) < t)] at hR
  -- the integrated lower bound
  have hint : -(2 * C) - 2 * W ≤
      L * (Real.log ‖riemannZeta (σ₀ + t * I)‖ - Real.log ‖riemannZeta (2 + t * I)‖) := by
    rw [log_norm_zeta_sub_eq hRH ht h0 h2, ← intervalIntegral.integral_const_mul]
    obtain ⟨hZi, hZ⟩ := integral_zeroSum_ge hRH (t := t) hx1 h0 h2 hηL
    have hg : IntervalIntegrable (fun σ : ℝ => L * (-(deriv riemannZeta (σ + t * I) /
        riemannZeta (σ + t * I))).re) volume σ₀ 2 := by
      refine ContinuousOn.intervalIntegrable ?_
      have := continuousOn_re_logDeriv_zeta hRH ht h0 h2
      simp only [neg_re]
      exact continuousOn_const.mul this.neg
    have hpt : ∀ σ ∈ Set.Icc σ₀ 2, -C + (zeroSum ((σ : ℂ) + t * I) x).re ≤
        L * (-(deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I))).re := by
      intro σ hσ
      have hσ0 : 1 / 2 < ((σ : ℂ) + t * I).re := by simp; linarith [hσ.1]
      have hne1 : (σ : ℂ) + t * I ≠ 1 := fun h => by
        have := congrArg im h; simp at this; linarith
      have hE := explicit_formula hRH hσ0 hne1 hx1.le
      have hre := congrArg re hE
      rw [re_ofReal_mul, sub_re, add_re] at hre
      rw [hre]
      have hD := (neg_le_of_abs_le (abs_re_le_norm _)).trans' (neg_le_neg (norm_dirPoly_le
        (s := (σ : ℂ) + t * I) (by simp; linarith [hσ.1]) hx1.le))
      have hER := (re_le_norm (ER ((σ : ℂ) + t * I) x)).trans
        (norm_ER_le (s := (σ : ℂ) + t * I) (by simp; linarith [hσ.1])
          (by simpa [abs_of_pos (by linarith : (0 : ℝ) < t)] using ht) hx1.le)
      have : -((x + 1) * L ^ 2) ≤ (dirPoly ((σ : ℂ) + t * I) x).re := hD
      rw [hC]; linarith
    calc -(2 * C) - 2 * W ≤ (2 - σ₀) * (-C) + -(2 * W) := by
          have : (2 - σ₀) * C ≤ 2 * C := mul_le_mul_of_nonneg_right (by linarith) hC0
          linarith
      _ ≤ (2 - σ₀) * (-C) + ∫ σ in σ₀..2, (zeroSum ((σ : ℂ) + t * I) x).re := by linarith
      _ = ∫ σ in σ₀..2, (-C + (zeroSum ((σ : ℂ) + t * I) x).re) := by
          rw [intervalIntegral.integral_add intervalIntegrable_const hZi,
            intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ ∫ σ in σ₀..2, L * (-(deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I))).re :=
          intervalIntegral.integral_mono_on h2 (intervalIntegrable_const.add hZi) hg hpt
  -- assemble
  have h2t := hA₀t t
  have hne1 : s₀ ≠ 1 := fun h => by have := congrArg im h; simp [hs₀] at this; linarith
  have hζ : riemannZeta s₀ ≠ 0 :=
    Lindelof.riemannZeta_ne_zero_of_RH hRH (by simp [hs₀]; linarith) hne1
  have hWC : 2 * W ≤ 4 * C / L + 4 * ‖archR s₀‖ := by
    have : 2 * (2 * C / L + 2 * ‖archR s₀‖) = 4 * C / L + 4 * ‖archR s₀‖ := by ring
    linarith
  have h4C : 4 * C / L ≤ 2 * C := by
    rw [div_le_iff₀ hL]; nlinarith
  have hlow : -(A₀ + (4 * C + 4 * Real.log (3 + t) + 20) / L) ≤ Real.log ‖riemannZeta s₀‖ := by
    have e : (4 * C + 4 * Real.log (3 + t) + 20) / L =
        (4 * C + 4 * (Real.log (3 + t) + 5)) / L := by ring_nf
    rw [e]
    have hint' : -(2 * C) - (4 * C / L + 4 * ‖archR s₀‖) ≤
        L * (Real.log ‖riemannZeta s₀‖ - Real.log ‖riemannZeta (2 + t * I)‖) := by
      have := hint; simp only [hs₀] at this ⊢; linarith
    have hfin : -(4 * C + 4 * (Real.log (3 + t) + 5)) ≤
        L * (Real.log ‖riemannZeta s₀‖ - Real.log ‖riemannZeta (2 + t * I)‖) := by nlinarith
    have hdiv : -(4 * C + 4 * (Real.log (3 + t) + 5)) / L ≤
        Real.log ‖riemannZeta s₀‖ - Real.log ‖riemannZeta (2 + t * I)‖ := by
      rw [div_le_iff₀ hL]; linarith
    rw [neg_div] at hdiv
    linarith
  have hpos : 0 < ‖(riemannZeta s₀)⁻¹‖ := norm_pos_iff.2 (inv_ne_zero hζ)
  rw [← Real.exp_log hpos, norm_inv, Real.log_inv]
  exact Real.exp_le_exp.2 (by linarith)

end Mertens
