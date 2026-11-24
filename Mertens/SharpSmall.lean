import Littlewood.Main
import Mertens.InvZeta

/-!
# `1/ζ` near the half line for `|t| ≤ 1` (RH)

The explicit formula of littlewood-rh needs `|t| ≥ 1` (the pole of `ζ` at `1`). For `|t| ≤ 1` a
crude bound polynomial in `1/(σ - 1/2)` suffices, and it follows from the Hadamard expansion
alone. Under RH every term of `Re ξ'/ξ(σ+it) = Σ m (σ-1/2)/|σ+it-ρ|²` is at most
`3/(2(σ-1/2))` times the corresponding term at `σ = 2` (`re_logDeriv_xi_le_two`), so
`σ ↦ log|ξ(σ+it)| - (3/2) Re ξ'/ξ(2+it) · log(σ - 1/2)` is antitone on `(1/2, 2]`, and

    |ξ(σ+it)| ≥ |ξ(2+it)| · ((σ - 1/2)/(3/2))^{(3/2) Re ξ'/ξ(2+it)}.

Compactness of `[1/2, 2] × [-1, 1]` bounds `Γ_ℝ` and `|ξ(2+it)|⁻¹`.
-/

open Complex Set

namespace Mertens

open Littlewood Erdos985.Analytic

/-- Under RH, `Re ξ'/ξ(σ+it) ≤ 3/(2(σ-1/2)) · Re ξ'/ξ(2+it)` for `1/2 < σ ≤ 2`. -/
theorem re_logDeriv_xi_le_two (hRH : RiemannHypothesis) {σ : ℝ} (h0 : 1 / 2 < σ) (h2 : σ ≤ 2)
    (t : ℝ) :
    (deriv xiZeta ((σ : ℂ) + t * I) / xiZeta ((σ : ℂ) + t * I)).re ≤
      3 / (2 * (σ - 1 / 2)) * (deriv xiZeta ((2 : ℂ) + t * I) / xiZeta ((2 : ℂ) + t * I)).re := by
  have := countable_xiZero
  have hs : 1 / 2 < ((σ : ℂ) + t * I).re := by simp; linarith
  have h2' : 1 / 2 < ((2 : ℂ) + t * I).re := by simp; norm_num
  have hA := hasSum_re_logDeriv_xi hRH hs
  have hB := (hasSum_re_logDeriv_xi hRH h2').mul_left (3 / (2 * (σ - 1 / 2)))
  refine hasSum_le (fun ρ => ?_) hA hB
  have hρ : (ρ : ℂ).re = 1 / 2 := Lindelof.xiZeta_zero_re_of_RH hRH ρ.2
  rw [re_mult_div hRH, re_mult_div hRH]
  set a := σ - 1 / 2 with ha
  have ha0 : 0 < a := by linarith
  have ha2 : a ≤ 3 / 2 := by linarith
  set u := t - (ρ : ℂ).im
  have hn1 : normSq ((σ : ℂ) + t * I - ρ) = a ^ 2 + u ^ 2 := by
    simp [normSq_apply, hρ, ha, u]; ring
  have hn2 : normSq ((2 : ℂ) + t * I - ρ) = 9 / 4 + u ^ 2 := by
    simp [normSq_apply, hρ, u]; ring
  have hre1 : ((σ : ℂ) + t * I).re - 1 / 2 = a := by simp [ha]
  have hre2 : ((2 : ℂ) + t * I).re - 1 / 2 = 3 / 2 := by simp; norm_num
  rw [hn1, hn2, hre1, hre2]
  set m := (analyticOrderNatAt xiZeta (ρ : ℂ) : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have key : a / (a ^ 2 + u ^ 2) ≤ 3 / (2 * a) * (3 / 2 / (9 / 4 + u ^ 2)) := by
    rw [show 3 / (2 * a) * (3 / 2 / (9 / 4 + u ^ 2)) = 9 / (4 * a * (9 / 4 + u ^ 2)) by
      field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) (sub_nonneg.2 (pow_le_pow_left₀ ha0.le ha2 2))]
  calc m * (a / (a ^ 2 + u ^ 2)) ≤ m * (3 / (2 * a) * (3 / 2 / (9 / 4 + u ^ 2))) :=
        mul_le_mul_of_nonneg_left key hm
    _ = 3 / (2 * a) * (m * (3 / 2 / (9 / 4 + u ^ 2))) := by ring

/-- `Re ξ'/ξ(2 + it) ≤ B + log (3 + |t|) + 5` for all `t`. -/
theorem re_logDeriv_xi_two_le_abs {B : ℝ}
    (hB : ∀ t : ℝ, ‖deriv riemannZeta ((2 : ℂ) + t * I) / riemannZeta ((2 : ℂ) + t * I)‖ ≤ B)
    (t : ℝ) :
    (deriv xiZeta ((2 : ℂ) + t * I) / xiZeta ((2 : ℂ) + t * I)).re ≤
      B + Real.log (3 + |t|) + 5 := by
  have hs : 0 < ((2 : ℂ) + t * I).re := by simp
  have hs1 : (2 : ℂ) + t * I ≠ 1 := fun h => by have := congrArg re h; simp at this
  have hζ : riemannZeta ((2 : ℂ) + t * I) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
  have h := logDeriv_riemannZeta_eq_archR hs hs1 hζ
  have hxi : deriv xiZeta ((2 : ℂ) + t * I) / xiZeta ((2 : ℂ) + t * I) =
      deriv riemannZeta ((2 : ℂ) + t * I) / riemannZeta ((2 : ℂ) + t * I) +
        archR ((2 : ℂ) + t * I) := by
    rw [h]; ring
  rw [hxi, add_re]
  have h1 := (re_le_norm _).trans (hB t)
  have h2 := (re_le_norm _).trans (norm_archR_two_le t)
  linarith

/-- Under RH, for `1/2 < σ₀ ≤ 2`:
`log |ξ(2+it)| - log |ξ(σ₀+it)| ≤ (3/2) Re ξ'/ξ(2+it) · (log (3/2) - log (σ₀ - 1/2))`. -/
theorem log_norm_xi_ge (hRH : RiemannHypothesis) {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h2 : σ₀ ≤ 2)
    (t : ℝ) :
    Real.log ‖xiZeta (2 + t * I)‖ - Real.log ‖xiZeta (σ₀ + t * I)‖ ≤
      3 / 2 * (deriv xiZeta ((2 : ℂ) + t * I) / xiZeta ((2 : ℂ) + t * I)).re *
        (Real.log (3 / 2) - Real.log (σ₀ - 1 / 2)) := by
  set K := 3 / 2 * (deriv xiZeta ((2 : ℂ) + t * I) / xiZeta ((2 : ℂ) + t * I)).re with hK
  set h : ℝ → ℝ := fun σ => Real.log ‖xiZeta (σ + t * I)‖ - K * Real.log (σ - 1 / 2) with hh
  have hne : ∀ σ : ℝ, 1 / 2 < σ → xiZeta (σ + t * I) ≠ 0 := fun σ hσ =>
    Lindelof.xiZeta_ne_zero_of_RH hRH (by simpa using hσ)
  have hd : ∀ σ : ℝ, 1 / 2 < σ → HasDerivAt h
      ((deriv xiZeta (σ + t * I) / xiZeta (σ + t * I)).re - K * (1 / (σ - 1 / 2))) σ := by
    intro σ hσ
    have hF : HasDerivAt (fun σ : ℝ => xiZeta (σ + t * I)) (deriv xiZeta (σ + t * I)) σ :=
      HasDerivAt.comp_ofReal (e := fun z => xiZeta (z + t * I))
        ((differentiable_xiZeta _).hasDerivAt.comp_add_const)
    have h1 := hasDerivAt_log_norm hF (hne σ hσ)
    have h2 : HasDerivAt (fun σ : ℝ => Real.log (σ - 1 / 2)) (1 / (σ - 1 / 2)) σ := by
      have := ((hasDerivAt_id σ).sub_const (1 / 2 : ℝ)).log (by simp; linarith)
      simpa using this
    exact h1.sub (h2.const_mul K)
  have hanti : AntitoneOn h (Icc σ₀ 2) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc σ₀ 2)
      (f' := fun σ => (deriv xiZeta (σ + t * I) / xiZeta (σ + t * I)).re - K * (1 / (σ - 1 / 2)))
      (fun σ hσ => (hd σ (lt_of_lt_of_le h0 hσ.1)).continuousAt.continuousWithinAt)
      (fun σ hσ => ?_) (fun σ hσ => ?_)
    · rw [interior_Icc] at hσ
      exact (hd σ (lt_trans h0 hσ.1)).hasDerivWithinAt
    · rw [interior_Icc] at hσ
      have hσ0 : 1 / 2 < σ := lt_trans h0 hσ.1
      have := re_logDeriv_xi_le_two hRH hσ0 hσ.2.le t
      have e : K * (1 / (σ - 1 / 2)) = 3 / (2 * (σ - 1 / 2)) *
          (deriv xiZeta ((2 : ℂ) + t * I) / xiZeta ((2 : ℂ) + t * I)).re := by
        rw [hK]; field_simp
      push_cast at this
      linarith
  have := hanti ⟨le_rfl, h2⟩ ⟨h2, le_rfl⟩ h2
  simp only [hh] at this
  norm_num at this ⊢
  linarith

/-- **`1/ζ` for `|t| ≤ 1`** (RH): `‖invZ s‖ ≤ K₁ (3/(2(σ-1/2)))^{K₂}` on `1/2 < σ ≤ 2`,
`|t| ≤ 1`. -/
theorem norm_invZ_le_small (hRH : RiemannHypothesis) : ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 ≤ K₂ ∧
    ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 → |s.im| ≤ 1 →
      ‖invZ s‖ ≤ K₁ * (3 / (2 * (s.re - 1 / 2))) ^ K₂ := by
  obtain ⟨B, hB⟩ := norm_logDeriv_zeta_two_le
  -- `Γ_ℝ` on the compact box
  set Q : Set ℂ := Icc (1 / 2 : ℝ) 2 ×ℂ Icc (-1 : ℝ) 1 with hQ
  have hQc : IsCompact Q := isCompact_Icc.reProdIm isCompact_Icc
  have hQne : Q.Nonempty := ⟨1, by simp [hQ, mem_reProdIm]; norm_num⟩
  obtain ⟨z₁, hz₁Q, hz₁⟩ := hQc.exists_isMinOn hQne
    (differentiable_Gammaℝ_inv.continuous.norm.continuousOn)
  set m₁ := ‖(Gammaℝ z₁)⁻¹‖ with hm₁
  have hm₁0 : 0 < m₁ := by
    have hre : 0 < z₁.re := by
      have := (mem_reProdIm.1 hz₁Q).1; linarith [this.1]
    exact norm_pos_iff.2 (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hre))
  -- `ξ(2 + it)` on `|t| ≤ 1`
  have hcξ : Continuous fun t : ℝ => ‖xiZeta (2 + t * I)‖ :=
    (differentiable_xiZeta.continuous.comp
      (continuous_const.add (continuous_ofReal.mul continuous_const))).norm
  obtain ⟨t₁, ht₁, ht₁min⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_isMinOn
    ⟨0, by norm_num⟩ hcξ.continuousOn
  set c := ‖xiZeta (2 + t₁ * I)‖ with hc
  have hc0 : 0 < c := norm_pos_iff.2 (xiZeta_ne_zero_of_one_lt (by simp))
  set K₂ := 3 / 2 * (B + Real.log 4 + 5) with hK₂
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hK₂0 : 0 ≤ K₂ := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); positivity
  refine ⟨6 / (m₁ * c), K₂, by positivity, hK₂0, fun s h0 h2 ht => ?_⟩
  by_cases hs1 : s = 1
  · subst hs1; simp only [invZ, sub_self, zero_div, norm_zero]; positivity
  have hs0 : s ≠ 0 := fun h => by rw [h] at h0; simp at h0; linarith
  have hsQ : s ∈ Q := by
    rw [hQ, mem_reProdIm]
    exact ⟨⟨h0.le, h2⟩, abs_le.1 ht⟩
  set σ := s.re
  set t := s.im
  set η := σ - 1 / 2 with hη
  have hη0 : 0 < η := by linarith
  have hsd : (σ : ℂ) + t * I = s := re_add_im s
  -- `‖ζ(s)⁻¹‖ ≤ 6 / (m₁ ‖ξ(s)‖)`
  have hΓ : ‖Gammaℝ s‖ ≤ 1 / m₁ := by
    have h1 := hz₁ hsQ
    simp only [mem_ofPred_eq] at h1
    have hΓ0 : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    rw [le_div_iff₀ hm₁0]
    calc ‖Gammaℝ s‖ * m₁ ≤ ‖Gammaℝ s‖ * ‖(Gammaℝ s)⁻¹‖ :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = 1 := by rw [← norm_mul, mul_inv_cancel₀ hΓ0, norm_one]
  have hξne : xiZeta s ≠ 0 := Lindelof.xiZeta_ne_zero_of_RH hRH h0
  have hζ : (riemannZeta s)⁻¹ = s * (s - 1) * Gammaℝ s / xiZeta s := by
    have hΓ0 : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    have hΛ : completedRiemannZeta s ≠ 0 := by
      intro h; apply hξne; rw [xiZeta_eq hs0 hs1, h, mul_zero]
    rw [riemannZeta_def_of_ne_zero hs0, xiZeta_eq hs0 hs1]
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
    field_simp
  have hnorm_s : ‖s‖ ≤ 3 := by
    have := norm_le_abs_re_add_abs_im s
    rw [abs_of_pos (by linarith : (0 : ℝ) < s.re)] at this; linarith
  have hnorm_s1 : ‖s - 1‖ ≤ 2 := by
    have := norm_le_abs_re_add_abs_im (s - 1)
    simp only [sub_re, one_re, sub_im, one_im, sub_zero] at this
    have : |s.re - 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  -- the lower bound for `‖ξ(s)‖`
  have hl := log_norm_xi_ge hRH h0 h2 t
  rw [hsd] at hl
  have hW := re_logDeriv_xi_two_le_abs hB t
  have hWnn : 0 ≤ (deriv xiZeta ((2 : ℂ) + t * I) / xiZeta ((2 : ℂ) + t * I)).re := by
    have := countable_xiZero
    refine (hasSum_re_logDeriv_xi hRH (show 1 / 2 < ((2 : ℂ) + t * I).re by simp; norm_num)).nonneg
      fun ρ => ?_
    rw [re_mult_div hRH]
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by simp; norm_num) (normSq_nonneg _))
  have hlog3 : Real.log (3 + |t|) ≤ Real.log 4 :=
    Real.log_le_log (by positivity) (by linarith)
  set Lη := Real.log (3 / 2) - Real.log η with hLη
  have hLη0 : 0 ≤ Lη := by
    rw [hLη, sub_nonneg]; exact Real.log_le_log hη0 (by linarith)
  have hKW : 3 / 2 * (deriv xiZeta ((2 : ℂ) + t * I) / xiZeta ((2 : ℂ) + t * I)).re * Lη ≤
      K₂ * Lη := by
    apply mul_le_mul_of_nonneg_right _ hLη0
    rw [hK₂]; linarith
  have hct := ht₁min (show t ∈ Icc (-1 : ℝ) 1 from abs_le.1 ht)
  simp only [mem_ofPred_eq] at hct
  have hξ2 : 0 < ‖xiZeta (2 + t * I)‖ := lt_of_lt_of_le hc0 hct
  have hξs : 0 < ‖xiZeta s‖ := norm_pos_iff.2 hξne
  have hlogc : Real.log c ≤ Real.log ‖xiZeta (2 + t * I)‖ := Real.log_le_log hc0 hct
  have hfinal : Real.log c - K₂ * Lη ≤ Real.log ‖xiZeta s‖ := by linarith
  have hpow : (3 / (2 * η)) ^ K₂ = Real.exp (K₂ * Lη) := by
    rw [Real.rpow_def_of_pos (by positivity), hLη, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hη0.ne', Real.log_div (by norm_num) (by norm_num)]
    congr 1; ring
  have hξlow : c * Real.exp (-(K₂ * Lη)) ≤ ‖xiZeta s‖ := by
    rw [← Real.exp_log hξs, ← Real.exp_log hc0, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  rw [← invZ_eq hs1] at hζ
  rw [hζ, norm_div, norm_mul, norm_mul, hpow]
  have hnum : ‖s‖ * ‖s - 1‖ * ‖Gammaℝ s‖ ≤ 6 / m₁ := by
    calc ‖s‖ * ‖s - 1‖ * ‖Gammaℝ s‖ ≤ 3 * 2 * (1 / m₁) := by gcongr
      _ = 6 / m₁ := by ring
  have hden : c * Real.exp (-(K₂ * Lη)) > 0 := by positivity
  calc ‖s‖ * ‖s - 1‖ * ‖Gammaℝ s‖ / ‖xiZeta s‖ ≤ (6 / m₁) / (c * Real.exp (-(K₂ * Lη))) :=
        div_le_div₀ (by positivity) hnum hden hξlow
    _ = 6 / (m₁ * c) * Real.exp (K₂ * Lη) := by
        rw [Real.exp_neg]; field_simp
end Mertens
