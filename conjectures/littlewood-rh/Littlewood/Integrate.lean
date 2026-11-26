import Littlewood.Explicit
import Littlewood.ZeroIntegral

/-!
# Step 8: integrating the explicit formula over `σ ∈ [σ₀, 2]`

Fix `t ≥ 1`, `x > 1`, `1/2 < σ₀ ≤ 2` with `(σ₀ - 1/2) log x ≥ 1`, and write
`f(σ) = log |ζ(σ + it)|`. Under RH `f' = Re ζ'/ζ`, so `f(σ₀) - f(2) = ∫_{σ₀}^{2} Re(-ζ'/ζ)`.
Integrating `explicit_formula` and using `integral_zero_term_le` for every zero:

    log x · (f(σ₀) - f(2)) ≤ 2 (x+1) (log x)² + 2 (x + 1 + Σ 1/(k+1)²) + Re ξ'/ξ(2 + it).
-/

open Complex MeasureTheory ArithmeticFunction intervalIntegral

namespace Littlewood

open Erdos985.Analytic

/-- `log ‖h‖` has derivative `Re (h'/h)` where `h ≠ 0`. -/
lemma hasDerivAt_log_norm {F : ℝ → ℂ} {F' : ℂ} {σ : ℝ} (hF : HasDerivAt F F' σ) (h0 : F σ ≠ 0) :
    HasDerivAt (fun σ => Real.log ‖F σ‖) (F' / F σ).re σ := by
  have hn : HasDerivAt (fun σ => ‖F σ‖ ^ 2) (2 * inner ℝ (F σ) F') σ := hF.norm_sq
  have hpos : 0 < ‖F σ‖ ^ 2 := by positivity
  have hlog := hn.log hpos.ne'
  have heq : (fun σ => Real.log ‖F σ‖) = fun σ => Real.log (‖F σ‖ ^ 2) / 2 := by
    funext σ; rw [Real.log_pow]; push_cast; ring
  rw [heq]
  convert hlog.div_const 2 using 1
  rw [Complex.inner, div_re]
  have : ‖F σ‖ ^ 2 = normSq (F σ) := (Complex.normSq_eq_norm_sq _).symm
  rw [this]
  simp only [mul_re, conj_re, conj_im]
  field_simp
  ring

/-- Continuity of `Re ζ'/ζ(σ + it)` on `[σ₀, 2]` under RH. -/
theorem continuousOn_re_logDeriv_zeta (hRH : RiemannHypothesis) {t σ₀ : ℝ} (ht : 1 ≤ t)
    (h0 : 1 / 2 < σ₀) (h2 : σ₀ ≤ 2) :
    ContinuousOn (fun σ : ℝ => (deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)).re)
      (Set.uIcc σ₀ 2) := by
  have hne1 : ∀ σ : ℝ, (σ : ℂ) + t * I ≠ 1 := fun σ h => by
    have := congrArg im h; simp at this; linarith
  have hsub : Set.uIcc σ₀ 2 ⊆ Set.Ioi (1 / 2) := by
    intro σ hσ; rw [Set.uIcc_of_le h2] at hσ; exact lt_of_lt_of_le h0 hσ.1
  have hζ : ∀ σ ∈ Set.uIcc σ₀ 2, riemannZeta (σ + t * I) ≠ 0 := fun σ hσ =>
    Lindelof.riemannZeta_ne_zero_of_RH hRH (by simpa using hsub hσ) (hne1 σ)
  have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
  have hdiff : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hderiv_cont : ContinuousOn (deriv riemannZeta) {z : ℂ | z ≠ 1} :=
    (hdiff.deriv hopen).continuousOn
  have hc : Continuous fun σ : ℝ => (σ : ℂ) + t * I := continuous_ofReal.add continuous_const
  refine continuous_re.comp_continuousOn (ContinuousOn.div ?_ ?_ hζ)
  · exact hderiv_cont.comp_continuous hc (fun σ => hne1 σ) |>.continuousOn
  · exact (hdiff.continuousOn.comp_continuous hc (fun σ => hne1 σ)).continuousOn

/-- FTC for `log |ζ(σ + it)|` under RH. -/
theorem log_norm_zeta_sub_eq (hRH : RiemannHypothesis) {t σ₀ : ℝ} (ht : 1 ≤ t) (h0 : 1 / 2 < σ₀)
    (h2 : σ₀ ≤ 2) :
    Real.log ‖riemannZeta (σ₀ + t * I)‖ - Real.log ‖riemannZeta (2 + t * I)‖
      = ∫ σ in σ₀..2, (-(deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I))).re := by
  have hne1 : ∀ σ : ℝ, (σ : ℂ) + t * I ≠ 1 := fun σ h => by
    have := congrArg im h; simp at this; linarith
  have hsub : Set.uIcc σ₀ 2 ⊆ Set.Ioi (1 / 2) := by
    intro σ hσ; rw [Set.uIcc_of_le h2] at hσ; exact lt_of_lt_of_le h0 hσ.1
  have hζ : ∀ σ ∈ Set.uIcc σ₀ 2, riemannZeta (σ + t * I) ≠ 0 := fun σ hσ =>
    Lindelof.riemannZeta_ne_zero_of_RH hRH (by simpa using hsub hσ) (hne1 σ)
  have hd : ∀ σ ∈ Set.uIcc σ₀ 2, HasDerivAt (fun σ : ℝ => Real.log ‖riemannZeta (σ + t * I)‖)
      (deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)).re σ := by
    intro σ hσ
    have hF : HasDerivAt (fun σ : ℝ => riemannZeta (σ + t * I)) (deriv riemannZeta (σ + t * I)) σ :=
      HasDerivAt.comp_ofReal (e := fun z => riemannZeta (z + t * I))
        ((differentiableAt_riemannZeta (hne1 σ)).hasDerivAt.comp_add_const)
    exact hasDerivAt_log_norm hF (hζ σ hσ)
  have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
  have hdiff : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hderiv_cont : ContinuousOn (deriv riemannZeta) {z : ℂ | z ≠ 1} :=
    (hdiff.deriv hopen).continuousOn
  have hc : Continuous fun σ : ℝ => (σ : ℂ) + t * I := continuous_ofReal.add continuous_const
  have hcont : ContinuousOn (fun σ : ℝ => (deriv riemannZeta (σ + t * I) /
      riemannZeta (σ + t * I)).re) (Set.uIcc σ₀ 2) := by
    refine continuous_re.comp_continuousOn (ContinuousOn.div ?_ ?_ hζ)
    · exact hderiv_cont.comp_continuous hc (fun σ => hne1 σ) |>.continuousOn
    · exact (hdiff.continuousOn.comp_continuous hc (fun σ => hne1 σ)).continuousOn
  have h := integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
  simp only [neg_re, intervalIntegral.integral_neg]
  push_cast at h ⊢
  linarith

/-! ### Bounds for the pieces -/

/-- Under RH, `Σ_ρ m / |ρ - s|²` converges for `Re s > 1/2`. -/
theorem summable_mult_div_normSq (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable fun ρ : XiZero => (analyticOrderNatAt xiZeta ρ : ℝ) / normSq ((ρ : ℂ) - s) := by
  have hW := summable_zero_weight hRH hs
  have hη : 0 < s.re - 1 / 2 := by linarith
  refine Summable.of_nonneg_of_le (fun ρ => div_nonneg (Nat.cast_nonneg _) (normSq_nonneg _))
    (fun ρ => ?_) (hW.mul_left (1 / (s.re - 1 / 2) + 1))
  have hρ : (ρ : ℂ).re = 1 / 2 := Lindelof.xiZeta_zero_re_of_RH hRH ρ.2
  set d := ‖(ρ : ℂ) - s‖ with hd
  have hdη : s.re - 1 / 2 ≤ d := by
    have := abs_re_le_norm ((ρ : ℂ) - s)
    rw [sub_re, hρ, abs_of_neg (by linarith)] at this
    linarith
  have hd0 : 0 < d := by linarith
  rw [Complex.normSq_eq_norm_sq, ← hd, norm_neg,
    show ‖mult ρ‖ = (analyticOrderNatAt xiZeta ρ : ℝ) by simp [mult]]
  set mm := (analyticOrderNatAt xiZeta ρ : ℝ)
  have hmm : 0 ≤ mm := Nat.cast_nonneg _
  have h1 : 1 / d ≤ (1 / (s.re - 1 / 2) + 1) * (1 + d) ^ (-(1 / 2 : ℝ)) := by
    have e1 : 1 / d ≤ (1 / (s.re - 1 / 2) + 1) / (1 + d) := by
      rw [div_le_div_iff₀ hd0 (by linarith)]
      have : 1 ≤ d / (s.re - 1 / 2) := by rw [le_div_iff₀ hη]; linarith
      have e : (1 / (s.re - 1 / 2) + 1) * d = d / (s.re - 1 / 2) + d := by field_simp
      rw [e]; linarith
    have e2 : (1 + d)⁻¹ ≤ (1 + d) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    calc 1 / d ≤ (1 / (s.re - 1 / 2) + 1) / (1 + d) := e1
      _ = (1 / (s.re - 1 / 2) + 1) * (1 + d)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left e2 (by positivity)
  calc mm / d ^ 2 = mm / d * (1 / d) := by field_simp
    _ ≤ mm / d * ((1 / (s.re - 1 / 2) + 1) * (1 + d) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (1 / (s.re - 1 / 2) + 1) * (mm / d * (1 + d) ^ (-(1 / 2 : ℝ))) := by ring

/-- `‖D(s, x)‖ ≤ (x + 1) (log x)²` for `Re s ≥ 0`, `x ≥ 1`. -/
theorem norm_dirPoly_le {s : ℂ} (hs : 0 ≤ s.re) {x : ℝ} (hx : 1 ≤ x) :
    ‖dirPoly s x‖ ≤ (x + 1) * Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hterm : ∀ n ∈ Finset.range (⌊x⌋₊ + 1),
      ‖(Λ n : ℂ) * (n : ℂ) ^ (-s) * (Real.log (x / n) : ℂ)‖ ≤ Real.log x ^ 2 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp; positivity
    rw [Finset.mem_range] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 (Nat.lt_succ_iff.1 hn)).trans (Nat.floor_le hx0.le)
    rw [norm_mul, norm_mul, norm_real, norm_real, Real.norm_of_nonneg vonMangoldt_nonneg,
      norm_natCast_cpow_of_pos hn0]
    have h1 : Λ n ≤ Real.log x :=
      vonMangoldt_le_log.trans (Real.log_le_log (by linarith) hnx)
    have h2 : (n : ℝ) ^ (-s).re ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1 (by simp; linarith)
    have h3 : ‖Real.log (x / n)‖ ≤ Real.log x := by
      rw [Real.norm_of_nonneg (Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)),
        Real.log_div hx0.ne' (by linarith)]
      linarith [Real.log_nonneg hn1]
    have h0 : 0 ≤ (n : ℝ) ^ (-s).re := Real.rpow_nonneg (by linarith) _
    calc Λ n * (n : ℝ) ^ (-s).re * ‖Real.log (x / n)‖
        ≤ Real.log x * 1 * Real.log x := by
          gcongr
      _ = Real.log x ^ 2 := by ring
  calc ‖dirPoly s x‖ ≤ ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        ‖(Λ n : ℂ) * (n : ℂ) ^ (-s) * (Real.log (x / n) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Real.log x ^ 2 := Finset.sum_le_sum hterm
    _ = (⌊x⌋₊ + 1) * Real.log x ^ 2 := by simp
    _ ≤ (x + 1) * Real.log x ^ 2 := by gcongr; exact Nat.floor_le hx0.le

end Littlewood
