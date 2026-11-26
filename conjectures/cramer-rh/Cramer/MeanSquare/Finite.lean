import Cramer.MeanSquare.Approx

/-!
# Asymptotic, step 2: finite trigonometric sums, coefficient limits, tails

* `finite_mean`: for a finite family with distinct frequencies `γ_ρ`,
  `|∫_a^{a+T} |Σ_ρ b_ρ e^{iγ_ρ u}|² du − T Σ_ρ |b_ρ|²| ≤ Σ_{ρ ≠ ρ'} 2|b_ρ||b_ρ'|/|γ_ρ − γ_ρ'|`,
  a bound independent of `T` (each off-diagonal integral is `(e^{iτb} − e^{iτa})/(iτ)`).
* `acoef_tendsto`: `acoef δ ρ → 1/ρ` as `δ → 0⁺` (the slope of `(1+t)^{ρ+1}` at `0`).
-/

namespace Cramer.MeanSq

open Complex Erdos985.Analytic Erdos233 Erdos233.CoeffAux MeasureTheory intervalIntegral
  Filter Topology

/-- `e^{iτu}`. -/
noncomputable def ex (τ u : ℝ) : ℂ := exp (((τ * u : ℝ) : ℂ) * I)

lemma norm_ex (τ u : ℝ) : ‖ex τ u‖ = 1 := norm_exp_ofReal_mul_I _

lemma continuous_ex (τ : ℝ) : Continuous (ex τ) := by unfold ex; fun_prop

lemma ex_mul_conj (γ γ' u : ℝ) : ex γ u * (starRingEnd ℂ) (ex γ' u) = ex (γ - γ') u := by
  unfold ex
  rw [← exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I]
  push_cast
  ring

lemma integral_ex_zero (a b : ℝ) : ∫ u in a..b, ex 0 u = b - a := by
  simp [ex]

lemma norm_integral_ex_le {τ : ℝ} (hτ : τ ≠ 0) (a b : ℝ) :
    ‖∫ u in a..b, ex τ u‖ ≤ 2 / |τ| := by
  have hc : (τ : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 hτ) I_ne_zero
  have e : (fun u : ℝ => ex τ u) = fun u : ℝ => cexp (((τ : ℂ) * I) * u) := by
    funext u; unfold ex; push_cast; ring_nf
  rw [e, integral_exp_mul_complex hc, norm_div]
  have h1 : ‖cexp ((τ : ℂ) * I * b) - cexp ((τ : ℂ) * I * a)‖ ≤ 2 := by
    have hb : ‖cexp ((τ : ℂ) * I * b)‖ = 1 := by
      rw [show (τ : ℂ) * I * b = ((τ * b : ℝ) : ℂ) * I by push_cast; ring]
      exact norm_exp_ofReal_mul_I _
    have ha : ‖cexp ((τ : ℂ) * I * a)‖ = 1 := by
      rw [show (τ : ℂ) * I * a = ((τ * a : ℝ) : ℂ) * I by push_cast; ring]
      exact norm_exp_ofReal_mul_I _
    calc _ ≤ ‖cexp ((τ : ℂ) * I * b)‖ + ‖cexp ((τ : ℂ) * I * a)‖ := norm_sub_le _ _
      _ = 2 := by rw [hb, ha]; norm_num
  have h2 : ‖(τ : ℂ) * I‖ = |τ| := by rw [norm_mul, norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]
  rw [h2]
  exact div_le_div_of_nonneg_right h1 (abs_nonneg _)

/-- `Σ_{ρ ∈ S} b_ρ e^{iγ_ρ u}`. -/
noncomputable def wave (S : Finset Zeros) (b : Zeros → ℂ) (u : ℝ) : ℂ :=
  ∑ ρ ∈ S, b ρ * ex (ρ : ℂ).im u

lemma continuous_wave (S : Finset Zeros) (b : Zeros → ℂ) : Continuous (wave S b) := by
  unfold wave
  exact continuous_finsetSum _ fun ρ _ => continuous_const.mul (continuous_ex _)

/-- The off-diagonal constant of `finite_mean`. -/
noncomputable def offDiag (S : Finset Zeros) (b : Zeros → ℂ) : ℝ :=
  ∑ ρ ∈ S, ∑ ρ' ∈ S.erase ρ, ‖b ρ‖ * ‖b ρ'‖ * (2 / |(ρ : ℂ).im - (ρ' : ℂ).im|)

theorem finite_mean (S : Finset Zeros) (b : Zeros → ℂ)
    (hinj : ∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → (ρ : ℂ).im ≠ (ρ' : ℂ).im) (a c : ℝ) :
    |(∫ u in a..c, ‖wave S b u‖ ^ 2) - (c - a) * ∑ ρ ∈ S, ‖b ρ‖ ^ 2| ≤ offDiag S b := by
  classical
  set T : Zeros → Zeros → ℝ → ℂ := fun ρ ρ' u =>
    b ρ * (starRingEnd ℂ) (b ρ') * ex ((ρ : ℂ).im - (ρ' : ℂ).im) u with hT
  have hpt : ∀ u, (((‖wave S b u‖ ^ 2 : ℝ)) : ℂ) = ∑ ρ ∈ S, ∑ ρ' ∈ S, T ρ ρ' u := by
    intro u
    have hsq : (((‖wave S b u‖ ^ 2 : ℝ)) : ℂ) = wave S b u * (starRingEnd ℂ) (wave S b u) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hsq, wave, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_
    simp only [hT, map_mul]
    rw [← ex_mul_conj]
    ring
  have hTc : ∀ ρ ρ', Continuous (T ρ ρ') := fun ρ ρ' => by
    simp only [hT]; exact continuous_const.mul (continuous_ex _)
  have hInt : ((∫ u in a..c, ‖wave S b u‖ ^ 2 : ℝ) : ℂ)
      = ∑ ρ ∈ S, ∑ ρ' ∈ S, ∫ u in a..c, T ρ ρ' u := by
    rw [← intervalIntegral.integral_ofReal]
    simp only [hpt]
    rw [integral_finsetSum fun ρ _ => (continuous_finsetSum _ fun ρ' _ =>
      hTc ρ ρ').intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    exact integral_finsetSum fun ρ' _ => (hTc ρ ρ').intervalIntegrable _ _
  have hdiag : ∀ ρ, ∫ u in a..c, T ρ ρ u = ((c - a : ℝ) : ℂ) * ((‖b ρ‖ ^ 2 : ℝ) : ℂ) := by
    intro ρ
    simp only [hT, sub_self]
    rw [intervalIntegral.integral_const_mul, integral_ex_zero, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  have hoff : ∀ ρ ∈ S, ∀ ρ' ∈ S.erase ρ, ‖∫ u in a..c, T ρ ρ' u‖
      ≤ ‖b ρ‖ * ‖b ρ'‖ * (2 / |(ρ : ℂ).im - (ρ' : ℂ).im|) := by
    intro ρ hρ ρ' hρ'
    have hne : ρ' ≠ ρ := Finset.ne_of_mem_erase hρ'
    have hτ : (ρ : ℂ).im - (ρ' : ℂ).im ≠ 0 :=
      sub_ne_zero.2 (hinj ρ hρ ρ' (Finset.mem_of_mem_erase hρ') hne.symm)
    simp only [hT]
    rw [intervalIntegral.integral_const_mul, norm_mul, norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_left (norm_integral_ex_le hτ a c) (by positivity)
  have hsplit : ∑ ρ ∈ S, ∑ ρ' ∈ S, ∫ u in a..c, T ρ ρ' u
      = ((c - a : ℝ) : ℂ) * ((∑ ρ ∈ S, ‖b ρ‖ ^ 2 : ℝ) : ℂ)
        + ∑ ρ ∈ S, ∑ ρ' ∈ S.erase ρ, ∫ u in a..c, T ρ ρ' u := by
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [← Finset.add_sum_erase S _ hρ, hdiag ρ]
    push_cast; ring
  have key : (((∫ u in a..c, ‖wave S b u‖ ^ 2) - (c - a) * ∑ ρ ∈ S, ‖b ρ‖ ^ 2 : ℝ) : ℂ)
      = ∑ ρ ∈ S, ∑ ρ' ∈ S.erase ρ, ∫ u in a..c, T ρ ρ' u := by
    rw [ofReal_sub, hInt, hsplit, ofReal_mul]; ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, key]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ' hρ' => hoff ρ hρ ρ' hρ')

/-- `acoef δ ρ → 1/ρ` as `δ → 0⁺`. -/
theorem acoef_tendsto {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    Tendsto (fun δ => acoef δ ρ) (𝓝[>] 0) (𝓝 (1 / ρ)) := by
  have hρ0 := rho_ne_zero hre
  have hρ1 := rho_add_one_ne_zero hre
  have hd := (hasDerivAt_φ (ρ + 1) (t := 0) (by norm_num)).tendsto_slope_zero_right
  have hφ0 : φ (ρ + 1) 0 = 1 := by simp [φ]
  have hφ1 : φ (ρ + 1 - 1) 0 = 1 := by simp [φ]
  rw [hφ1, mul_one] at hd
  have h2 := hd.div_const (ρ * (ρ + 1))
  have hlim : (ρ + 1) / (ρ * (ρ + 1)) = 1 / ρ := by field_simp
  rw [hlim] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : (δ : ℂ) ≠ 0 := ofReal_ne_zero.2 (ne_of_gt hδ)
  simp only [acoef, φ, zero_add, real_smul, ofReal_inv, add_zero, ofReal_one, one_cpow]
  field_simp

end Cramer.MeanSq
