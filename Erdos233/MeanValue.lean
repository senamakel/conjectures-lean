import Erdos233.Density

/-!
# Step 5. Mean value of a zero wave over a window of length 2

With the Gaussian `w(u) = e · exp(−(u − U − 1)²) ≥ 1` on `[U, U+2]`,
`∫ w |Σ a_ρ e^{iγu}|² = Σ_{ρ,ρ'} a_ρ ā_ρ' ŵ(γ − γ')`, `|ŵ(τ)| = e√π e^{−τ²/4} ≤ 2e√π/(1+τ²)`,
`|a a'| ≤ (|a|² + |a'|²)/2`, and `zero_density` bounds `Σ_ρ' m_ρ'/(1 + (γ−γ')²)`.
-/

namespace Erdos233

open Complex Erdos985.Analytic MeasureTheory

private instance : Countable Zeros := PrincipalAux.countable_xiZeta_zeros

private lemma norm_wave_term (c : Zeros → ℂ) (ρ : Zeros) (u : ℝ) :
    ‖(mult ρ : ℂ) * c ρ * exp ((((ρ : ℂ).im * u : ℝ) : ℂ) * I)‖ = (mult ρ : ℝ) * ‖c ρ‖ := by
  rw [norm_mul, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_natCast]

theorem continuous_zeroWave {c : Zeros → ℂ} (hc : Summable fun ρ => (mult ρ : ℝ) * ‖c ρ‖) :
    Continuous (zeroWave c) :=
  continuous_tsum (fun ρ => by fun_prop) hc (fun ρ u => (norm_wave_term c ρ u).le)

/-- `(1 + t²) e^{-t²/4} ≤ 2`, in the form `e^{1 - t²/4} ≤ 2e/(1+t²)`. -/
private lemma exp_gauss_le (τ : ℝ) :
    Real.exp (1 - τ ^ 2 / 4) ≤ 2 * Real.exp 1 / (1 + τ ^ 2) := by
  have hD : 0 < 1 + τ ^ 2 := by positivity
  have hx : 0 ≤ τ ^ 2 / 4 := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have h2 : 1 + τ ^ 2 ≤ 2 * Real.exp (τ ^ 2 / 4) := by nlinarith [sq_nonneg (τ ^ 2 / 4 - 1)]
  rw [le_div_iff₀ hD, Real.exp_sub]
  have hpos := Real.exp_pos (τ ^ 2 / 4)
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  nlinarith [Real.exp_pos 1]

private lemma gauss_bound (s τ : ℝ) :
    ‖∫ u : ℝ, cexp (-1 * (u : ℂ) ^ 2 + (2 * s + τ * I) * u + (1 - s ^ 2))‖ ≤
      2 * Real.exp 1 * Real.pi ^ (1 / 2 : ℝ) / (1 + τ ^ 2) := by
  rw [integral_cexp_quadratic (by simp)]
  have h1 : (Real.pi : ℂ) / -(-1) = ((Real.pi : ℝ) : ℂ) := by simp
  have h2 : ((1 : ℂ) - s ^ 2) - (2 * s + τ * I) ^ 2 / (4 * -1) =
      ((1 - τ ^ 2 / 4 : ℝ) : ℂ) + ((s * τ : ℝ) : ℂ) * I := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [h1, h2, norm_mul, norm_cpow_eq_rpow_re_of_pos Real.pi_pos, norm_exp]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero]
  have : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  rw [this, mul_comm (2 * Real.exp 1), mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (by simpa [mul_div_assoc] using exp_gauss_le τ)
    (by positivity)

private lemma wave_identity (s γ γ' u : ℝ) :
    ((Real.exp 1 * Real.exp (-(u - s) ^ 2) : ℝ) : ℂ) *
        (exp (((γ * u : ℝ) : ℂ) * I) * (starRingEnd ℂ) (exp (((γ' * u : ℝ) : ℂ) * I))) =
      cexp (-1 * (u : ℂ) ^ 2 + (2 * s + ((γ - γ' : ℝ) : ℂ) * I) * u + (1 - s ^ 2)) := by
  rw [← exp_conj]
  push_cast
  simp only [map_mul, conj_ofReal, conj_I]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

theorem mean_value : ∃ C : ℝ, 0 < C ∧ ∀ c : Zeros → ℂ,
    Summable (fun ρ => (mult ρ : ℝ) * ‖c ρ‖) →
    Summable (fun ρ => (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)) →
    ∀ U : ℝ, ∫ u in U..U + 2, ‖zeroWave c u‖ ^ 2 ≤
      C * ∑' ρ, (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2) := by
  obtain ⟨Cd, hCd, hd⟩ := zero_density
  set B : ℝ := 2 * Real.exp 1 * Real.pi ^ (1 / 2 : ℝ) with hBdef
  have hB : 0 < B := by positivity
  refine ⟨B * Cd, by positivity, ?_⟩
  intro c hc hc2 U
  set s : ℝ := U + 1 with hs
  set W : ℝ → ℝ := fun u => Real.exp 1 * Real.exp (-(u - s) ^ 2) with hW
  set f := zeroWave c with hf
  set A : Zeros → ℝ := fun ρ => (mult ρ : ℝ) * ‖c ρ‖ with hA
  have hA0 : ∀ ρ, 0 ≤ A ρ := fun ρ => by positivity
  set S : ℝ := ∑' ρ, A ρ
  have hfb : ∀ u, ‖f u‖ ≤ S := fun u =>
    tsum_of_norm_bounded hc.hasSum (fun ρ => (norm_wave_term c ρ u).le)
  have hfc : Continuous f := continuous_zeroWave hc
  have hWc : Continuous W := by fun_prop
  have hW0 : ∀ u, 0 ≤ W u := fun u => by positivity
  have hWint : Integrable W := by
    have := ((integrable_exp_neg_mul_sq one_pos).comp_sub_right s).const_mul (Real.exp 1)
    simpa [hW] using this
  have hWf : Integrable (fun u => W u * ‖f u‖ ^ 2) := by
    refine (hWint.mul_const (S ^ 2)).mono' (by fun_prop) (ae_of_all _ fun u => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hfb u) 2) (hW0 u)
  -- Step 1: the window is dominated by the Gaussian weight.
  have step1 : ∫ u in U..U + 2, ‖f u‖ ^ 2 ≤ ∫ u, W u * ‖f u‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    calc ∫ u in Set.Ioc U (U + 2), ‖f u‖ ^ 2
        ≤ ∫ u in Set.Ioc U (U + 2), W u * ‖f u‖ ^ 2 := by
          refine setIntegral_mono_on ?_ hWf.integrableOn measurableSet_Ioc fun u hu => ?_
          · exact ((hfc.norm.pow 2).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
          · have h1 : 1 ≤ W u := by
              simp only [hW, ← Real.exp_add]
              apply Real.one_le_exp
              nlinarith [hu.1, hu.2]
            nlinarith [sq_nonneg ‖f u‖]
      _ ≤ ∫ u, W u * ‖f u‖ ^ 2 :=
          setIntegral_le_integral hWf (ae_of_all _ fun u => by positivity)
  -- Step 2: expand `W |f|²` as a double series.
  set G : Zeros × Zeros → ℝ → ℂ := fun p u =>
    ((mult p.1 : ℂ) * c p.1 * (starRingEnd ℂ) ((mult p.2 : ℂ) * c p.2)) *
      (((W u : ℝ) : ℂ) * (exp ((((p.1 : ℂ).im * u : ℝ) : ℂ) * I) *
        (starRingEnd ℂ) (exp ((((p.2 : ℂ).im * u : ℝ) : ℂ) * I)))) with hG
  clear_value G
  have hGq : ∀ p u, G p u = ((mult p.1 : ℂ) * c p.1 * (starRingEnd ℂ) ((mult p.2 : ℂ) * c p.2)) *
      cexp (-1 * (u : ℂ) ^ 2 + (2 * s + (((p.1 : ℂ).im - (p.2 : ℂ).im : ℝ) : ℂ) * I) * u
        + (1 - s ^ 2)) := fun p u => by
    simp only [hG, hW]; rw [wave_identity]
  have hGnorm : ∀ p u, ‖G p u‖ = A p.1 * A p.2 * W u := fun p u => by
    simp only [hG, hA, norm_mul, RCLike.norm_conj, norm_exp_ofReal_mul_I, Complex.norm_natCast,
      Complex.norm_real, Real.norm_of_nonneg (hW0 u)]
    ring
  have hpt : ∀ u, (((W u * ‖f u‖ ^ 2 : ℝ)) : ℂ) = ∑' p, G p u := fun u => by
    have hn : ∀ u ρ, ‖(mult ρ : ℂ) * c ρ * exp ((((ρ : ℂ).im * u : ℝ) : ℂ) * I)‖ = A ρ :=
      fun u ρ => norm_wave_term c ρ u
    have hn' : ∀ u ρ, ‖(starRingEnd ℂ) ((mult ρ : ℂ) * c ρ * exp ((((ρ : ℂ).im * u : ℝ) : ℂ) * I))‖
        = A ρ := fun u ρ => by rw [RCLike.norm_conj, hn]
    have hsq : (((‖f u‖ ^ 2 : ℝ)) : ℂ) = f u * (starRingEnd ℂ) (f u) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [ofReal_mul, hsq, hf, zeroWave, conj_tsum,
      tsum_mul_tsum_of_summable_norm (by simpa only [hn u] using hc)
        (by simpa only [hn' u] using hc), ← tsum_mul_left]
    congr 1
    funext p
    simp only [hG, map_mul]
    ring
  -- Step 3: integrate termwise.
  have hGint : ∀ p, Integrable (G p) := fun p => by
    have := (integrable_cexp_quadratic (b := 1) (by simp)
      (2 * s + (((p.1 : ℂ).im - (p.2 : ℂ).im : ℝ) : ℂ) * I) (1 - s ^ 2)).const_mul
      ((mult p.1 : ℂ) * c p.1 * (starRingEnd ℂ) ((mult p.2 : ℂ) * c p.2))
    refine this.congr (ae_of_all _ fun u => ?_)
    simp only [hGq]
  have hGsum : Summable fun p => ∫ u, ‖G p u‖ := by
    simp only [hGnorm]
    simp only [integral_const_mul]
    exact (hc.mul_of_nonneg hc (fun ρ => hA0 ρ) (fun ρ => hA0 ρ)).mul_right _
  set bnd : Zeros × Zeros → ℝ := fun p =>
    B * (A p.1 * A p.2) / (1 + ((p.1 : ℂ).im - (p.2 : ℂ).im) ^ 2) with hbnd
  clear_value bnd
  have hGbound : ∀ p, ‖∫ u, G p u‖ ≤ bnd p := fun p => by
    simp only [hGq]
    rw [integral_const_mul, norm_mul]
    have hn : ‖(mult p.1 : ℂ) * c p.1 * (starRingEnd ℂ) ((mult p.2 : ℂ) * c p.2)‖ =
        A p.1 * A p.2 := by
      simp only [hA, norm_mul, RCLike.norm_conj, Complex.norm_natCast]
    rw [hn]
    calc A p.1 * A p.2 * ‖_‖ ≤ A p.1 * A p.2 * (B / (1 + ((p.1 : ℂ).im - (p.2 : ℂ).im) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hA0 _) (hA0 _))
          rw [hBdef]; exact gauss_bound s _
      _ = bnd p := by simp only [hbnd]; ring
  -- Step 4: real double series.
  set h : Zeros × Zeros → ℝ := fun p =>
    ((mult p.1 : ℝ) * ‖c p.1‖ ^ 2) *
      ((mult p.2 : ℝ) / (1 + ((p.1 : ℂ).im - (p.2 : ℂ).im) ^ 2)) with hh
  clear_value h
  have hh0 : 0 ≤ h := fun p => by simp only [hh]; positivity
  have hinner : ∀ x : Zeros, Summable fun y => h (x, y) := fun x => by
    simp only [hh]
    exact (hd (x : ℂ).im).1.mul_left _
  have houter_le : ∀ x : Zeros, ∑' y, h (x, y) ≤
      Cd * ((mult x : ℝ) * ‖c x‖ ^ 2 * Real.log (|(x : ℂ).im| + 2)) := fun x => by
    simp only [hh]
    rw [tsum_mul_left]
    have := mul_le_mul_of_nonneg_left (hd (x : ℂ).im).2
      (by positivity : (0 : ℝ) ≤ (mult x : ℝ) * ‖c x‖ ^ 2)
    linarith
  have hhs : Summable h := by
    refine (summable_prod_of_nonneg hh0).2 ⟨hinner, ?_⟩
    exact Summable.of_nonneg_of_le (fun x => tsum_nonneg fun y => hh0 _) houter_le
      (hc2.mul_left Cd)
  have hhs' : Summable fun p : Zeros × Zeros => h p.swap := hhs.prod_symm
  have hbnd_le : ∀ p, bnd p ≤ B / 2 * (h p + h p.swap) := fun p => by
    obtain ⟨x, y⟩ := p
    simp only [hbnd, hh, hA, Prod.swap]
    have hD : 0 < 1 + ((x : ℂ).im - (y : ℂ).im) ^ 2 := by positivity
    have hsym : ((y : ℂ).im - (x : ℂ).im) ^ 2 = ((x : ℂ).im - (y : ℂ).im) ^ 2 := by ring
    rw [hsym]
    have hm : 0 ≤ (mult x : ℝ) * (mult y : ℝ) := by positivity
    have key : (mult x : ℝ) * ‖c x‖ * ((mult y : ℝ) * ‖c y‖) ≤
        ((mult x : ℝ) * ‖c x‖ ^ 2 * (mult y : ℝ) + (mult y : ℝ) * ‖c y‖ ^ 2 * (mult x : ℝ)) / 2 := by
      nlinarith [mul_nonneg hm (sq_nonneg (‖c x‖ - ‖c y‖))]
    calc B * ((mult x : ℝ) * ‖c x‖ * ((mult y : ℝ) * ‖c y‖)) / (1 + ((x : ℂ).im - (y : ℂ).im) ^ 2)
        ≤ B * (((mult x : ℝ) * ‖c x‖ ^ 2 * (mult y : ℝ) + (mult y : ℝ) * ‖c y‖ ^ 2 * (mult x : ℝ))
            / 2) / (1 + ((x : ℂ).im - (y : ℂ).im) ^ 2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left key hB.le) hD.le
      _ = _ := by field_simp
  have hbnd_s : Summable bnd :=
    Summable.of_nonneg_of_le (fun p => by simp only [hbnd]; have := hA0 p.1; have := hA0 p.2; positivity)
      hbnd_le ((hhs.add hhs').mul_left _)
  have hsum_le : ∑' p, bnd p ≤ B * ∑' p, h p := by
    calc ∑' p, bnd p ≤ ∑' p : Zeros × Zeros, B / 2 * (h p + h p.swap) :=
          hbnd_s.tsum_le_tsum hbnd_le ((hhs.add hhs').mul_left _)
      _ = B / 2 * (∑' p, h p + ∑' p : Zeros × Zeros, h p.swap) := by rw [tsum_mul_left, hhs.tsum_add hhs']
      _ = B * ∑' p, h p := by
          rw [show (∑' p : Zeros × Zeros, h p.swap) = ∑' p, h p from (Equiv.prodComm _ _).tsum_eq h]
          ring
  have hh_le : ∑' p, h p ≤ Cd * ∑' ρ, (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2) := by
    rw [hhs.tsum_prod' hinner, ← tsum_mul_left]
    exact (hhs.prod).tsum_le_tsum houter_le (hc2.mul_left Cd)
  -- Assemble.
  have hint0 : 0 ≤ ∫ u, W u * ‖f u‖ ^ 2 := integral_nonneg fun u => by positivity
  have step4 : ∫ u, W u * ‖f u‖ ^ 2 ≤ ∑' p, bnd p := by
    have e1 : ∫ u, W u * ‖f u‖ ^ 2 = ‖((∫ u, W u * ‖f u‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hint0]
    rw [e1, ← integral_complex_ofReal]
    simp only [hpt]
    rw [← integral_tsum_of_summable_integral_norm hGint hGsum]
    exact tsum_of_norm_bounded hbnd_s.hasSum hGbound
  calc ∫ u in U..U + 2, ‖zeroWave c u‖ ^ 2 ≤ ∫ u, W u * ‖f u‖ ^ 2 := step1
    _ ≤ ∑' p, bnd p := step4
    _ ≤ B * ∑' p, h p := hsum_le
    _ ≤ B * (Cd * ∑' ρ, (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)) :=
        mul_le_mul_of_nonneg_left hh_le hB.le
    _ = _ := by ring

end Erdos233
