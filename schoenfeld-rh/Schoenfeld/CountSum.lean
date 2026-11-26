import Schoenfeld.ZeroCount

/-!
# `G(T) = Σ_{γ > 0} m · min(1/γ, T/γ²)` from Rosser's zero count

For a zero with ordinate `γ > 0` (so `γ > 4.4`, from `|ρ|² ≥ 20`),

`min(1/γ, T/γ²) = ∫_{(4.4, T]} 1[γ < t] dt/t² + ∫_{(T, ∞)} 1[γ < t] 2T dt/t³`.

Summing over the zeros (`integral_tsum_of_summable_integral_norm`) turns `G(T)` into
`∫_{4.4}^T N(t) dt/t² + 2T ∫_T^∞ N(t) dt/t³`, where `N(t) = cnt t` is the zero count. Rosser's
bound gives `N(t) ≤ Nc(t) = (t/2π)(log t − log 2π − 1) + 2.463 + 0.3 log t` for `t ≥ 2`
(`cnt_le_Nc`, using `log log t ≤ log t / e`), and both integrals of `Nc` are elementary:
`G(T) ≤ Ub(T)` (`Gsum_le_Ub`).
-/

namespace Schoenfeld

open Real MeasureTheory Filter Topology Set

/-! ### Elementary functions -/

/-- The majorant of the zero count. -/
noncomputable def Nc (t : ℝ) : ℝ :=
  t / (2 * π) * (Real.log t - Real.log (2 * π) - 1) + 2.463 + 0.3 * Real.log t

/-- An antiderivative of `Nc(t)/t²`. -/
noncomputable def P1 (t : ℝ) : ℝ :=
  Real.log t ^ 2 / (4 * π) - (Real.log (2 * π) + 1) / (2 * π) * Real.log t
    - (2.463 + 0.3) * t⁻¹ - 0.3 * (Real.log t * t⁻¹)

/-- `R_T(t)`, an antiderivative of `Nc(t) · 2T/t³` that tends to `0`. -/
noncomputable def Rt (T t : ℝ) : ℝ :=
  2 * T * (-(1 / (2 * π)) * (Real.log t * t⁻¹) + Real.log (2 * π) / (2 * π) * t⁻¹
    - (2.463 / 2 + 0.3 / 4) * t⁻¹ ^ 2 - 0.3 / 2 * (Real.log t * t⁻¹) * t⁻¹)

/-- The bound for `G(T)`. -/
noncomputable def Ub (T : ℝ) : ℝ :=
  P1 T - P1 4.4 + (Real.log T - Real.log (2 * π)) / π + (2.463 + 0.3 / 2) / T
    + 0.3 * Real.log T / T

lemma Nc_pos {t : ℝ} (ht : 1 ≤ t) : 0 < Nc t := by
  have hp := Real.pi_pos
  have hy : 0 < t / (2 * π) := by positivity
  have h1 := Real.one_sub_inv_le_log_of_pos hy
  rw [Real.log_div (by linarith) (by positivity)] at h1
  have h2 : 0 ≤ Real.log t := Real.log_nonneg ht
  have h3 : t / (2 * π) * (Real.log t - Real.log (2 * π) - 1) ≥ -1 := by
    have : t / (2 * π) * (1 - (t / (2 * π))⁻¹) = t / (2 * π) - 1 := by field_simp
    nlinarith
  unfold Nc; linarith

lemma hasDerivAt_P1 {t : ℝ} (ht : 0 < t) : HasDerivAt P1 (Nc t / t ^ 2) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have hi := hasDerivAt_inv ht.ne'
  have h := ((((hl.pow 2).div_const (4 * π)).sub (hl.const_mul ((Real.log (2 * π) + 1) / (2 * π)))).sub
    (hi.const_mul (2.463 + 0.3))).sub ((hl.mul hi).const_mul 0.3)
  convert h using 1
  · funext y; simp only [P1, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  have ht' : t ≠ 0 := ht.ne'
  unfold Nc
  field_simp
  ring

lemma hasDerivAt_Rt (T : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (Rt T) (Nc t * (2 * T / t ^ 3)) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have hi := hasDerivAt_inv ht.ne'
  have h := (((((hl.mul hi).const_mul (-(1 / (2 * π)))).add
    (hi.const_mul (Real.log (2 * π) / (2 * π)))).sub ((hi.pow 2).const_mul (2.463 / 2 + 0.3 / 4))).sub
    (((hl.mul hi).mul hi).const_mul (0.3 / 2))).const_mul (2 * T)
  convert h using 1
  · funext y; simp only [Rt, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]; ring
  simp only [Pi.mul_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  have ht' : t ≠ 0 := ht.ne'
  unfold Nc
  field_simp
  ring

lemma tendsto_Rt (T : ℝ) : Tendsto (Rt T) atTop (𝓝 0) := by
  have hL : Tendsto (fun t : ℝ => Real.log t * t⁻¹) atTop (𝓝 0) := by
    have := tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    refine this.congr fun t => ?_
    simp [div_eq_mul_inv]
  have hI : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h := ((((hL.const_mul (-(1 / (2 * π)))).add (hI.const_mul (Real.log (2 * π) / (2 * π)))).sub
    ((hI.pow 2).const_mul (2.463 / 2 + 0.3 / 4))).sub ((hL.mul hI).const_mul (0.3 / 2))).const_mul
    (2 * T)
  simp only [mul_zero, add_zero, sub_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at h
  refine h.congr fun t => ?_
  simp only [Rt]; ring

/-! ### One zero -/

lemma im_gt_of_pos (hRH : RiemannHypothesis) (ρ : Zeros) (h : 0 < (ρ : ℂ).im) :
    4.4 < (ρ : ℂ).im := by
  have h1 := normSq_of_re (re_eq_half hRH ρ)
  have h2 := twenty_le_normSq hRH ρ
  nlinarith

/-- `∫ₐᵇ c/t² = c(1/a − 1/b)`. -/
lemma integral_div_sq {a b : ℝ} (c : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, c / t ^ 2 = c * (1 / a - 1 / b) := by
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun t => -c * t⁻¹) (c / x ^ 2) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    convert (hasDerivAt_inv hx0).const_mul (-c) using 1
    field_simp
  have hc : ContinuousOn (fun t : ℝ => c / t ^ 2) (uIcc a b) := by
    refine continuousOn_const.div (continuousOn_pow 2) fun x hx => ?_
    rw [uIcc_of_le hab] at hx
    have : 0 < x := by linarith [hx.1]
    exact (pow_pos this 2).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  field_simp
  ring

/-- `m · 2T/t³` has the antiderivative `−mT/t²`. -/
lemma hasDerivAt_cube (m T : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => -(m * T) * (s ^ 2)⁻¹) (m * (2 * T / t ^ 3)) t := by
  have h := ((hasDerivAt_pow 2 t).inv (by positivity)).const_mul (-(m * T))
  convert h using 1
  field_simp
  ring

lemma tendsto_cube (m T : ℝ) : Tendsto (fun s : ℝ => -(m * T) * (s ^ 2)⁻¹) atTop (𝓝 0) := by
  have := (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (n := 2) two_ne_zero)).const_mul
    (-(m * T))
  simpa using this

/-- The first piece. -/
noncomputable def aF (ρ : Zeros) : ℝ → ℝ :=
  if 0 < (ρ : ℂ).im then (Ioi (ρ : ℂ).im).indicator (fun t => mult ρ / t ^ 2) else 0

/-- The tail piece. -/
noncomputable def bF (T : ℝ) (ρ : Zeros) : ℝ → ℝ :=
  if 0 < (ρ : ℂ).im then (Ioi (ρ : ℂ).im).indicator (fun t => mult ρ * (2 * T / t ^ 3)) else 0

lemma aF_nonneg (ρ : Zeros) (t : ℝ) : 0 ≤ aF ρ t := by
  unfold aF
  split_ifs
  · exact indicator_nonneg (fun _ _ => div_nonneg (mult_nonneg ρ) (sq_nonneg _)) t
  · exact le_rfl

lemma bF_nonneg {T : ℝ} (hT : 0 ≤ T) (ρ : Zeros) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ bF T ρ t := by
  unfold bF
  split_ifs
  · exact indicator_nonneg (fun _ _ => mul_nonneg (mult_nonneg ρ)
      (div_nonneg (by linarith) (pow_nonneg ht 3))) t
  · exact le_rfl

lemma integrableOn_div_sq (c : ℝ) {T : ℝ} :
    IntegrableOn (fun t : ℝ => c / t ^ 2) (Ioc 4.4 T) := by
  refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
  refine continuousOn_const.div (continuousOn_pow 2) fun x hx => ?_
  have : 0 < x := by linarith [hx.1]
  exact (pow_pos this 2).ne'

lemma integrableOn_cube (m : ℝ) {T : ℝ} (hT : 0 < T) (hm : 0 ≤ m) {a : ℝ} (ha : T ≤ a) :
    IntegrableOn (fun t : ℝ => m * (2 * T / t ^ 3)) (Ioi a) := by
  refine integrableOn_Ioi_deriv_of_nonneg' (fun x hx => hasDerivAt_cube m T ?_)
    (fun x hx => ?_) (tendsto_cube m T)
  · have : T ≤ x := ha.trans hx; linarith
  · have : 0 < x := by have := hx.out; linarith
    positivity

lemma integral_aF (hRH : RiemannHypothesis) {T : ℝ} (hT : 4.4 ≤ T) (ρ : Zeros) :
    ∫ t in Ioc 4.4 T, aF ρ t
      = if 0 < (ρ : ℂ).im then mult ρ * (if (ρ : ℂ).im < T then 1 / (ρ : ℂ).im - 1 / T else 0)
        else 0 := by
  unfold aF
  by_cases h : 0 < (ρ : ℂ).im
  · simp only [if_pos h]
    have hg := im_gt_of_pos hRH ρ h
    rw [setIntegral_indicator measurableSet_Ioi, Ioc_inter_Ioi, max_eq_right hg.le]
    by_cases hl : (ρ : ℂ).im < T
    · rw [if_pos hl, ← intervalIntegral.integral_of_le hl.le, integral_div_sq _ h hl.le]
    · rw [if_neg hl, Ioc_eq_empty hl, Measure.restrict_empty, integral_zero_measure, mul_zero]
  · simp [h]

lemma integral_bF (hRH : RiemannHypothesis) {T : ℝ} (hT : 4.4 ≤ T) (ρ : Zeros) :
    ∫ t in Ioi T, bF T ρ t
      = if 0 < (ρ : ℂ).im then mult ρ * (T / (max T (ρ : ℂ).im) ^ 2) else 0 := by
  unfold bF
  by_cases h : 0 < (ρ : ℂ).im
  · simp only [if_pos h]
    rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi]
    have hm : 0 < max T (ρ : ℂ).im := lt_max_of_lt_left (by linarith)
    rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun x hx => hasDerivAt_cube (mult ρ) T
      (lt_of_lt_of_le hm hx)) (fun x hx => ?_) (tendsto_cube (mult ρ) T)]
    · field_simp
      ring
    · have : 0 < x := lt_trans hm hx
      exact mul_nonneg (mult_nonneg ρ) (by positivity)
  · simp [h]

lemma posTerm_eq (hRH : RiemannHypothesis) {T : ℝ} (hT : 4.4 ≤ T) (ρ : Zeros) :
    posTerm T ρ = (∫ t in Ioc 4.4 T, aF ρ t) + ∫ t in Ioi T, bF T ρ t := by
  rw [integral_aF hRH hT, integral_bF hRH hT]
  unfold posTerm gmin
  by_cases h : 0 < (ρ : ℂ).im
  · simp only [if_pos h]
    set g := (ρ : ℂ).im
    have hg := im_gt_of_pos hRH ρ h
    by_cases hl : g < T
    · rw [if_pos hl, max_eq_left hl.le, min_eq_left]
      · field_simp; ring
      · rw [div_le_div_iff₀ h (by positivity)]; nlinarith
    · push Not at hl
      rw [if_neg (not_lt.mpr hl), max_eq_right hl, min_eq_right]
      · ring
      · rw [div_le_div_iff₀ (by positivity) h]; nlinarith
  · simp [h]

/-! ### The count -/

/-- `m · 1[0 < γ ≤ t]`. -/
noncomputable def ind (t : ℝ) (ρ : Zeros) : ℝ :=
  if 0 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ t then mult ρ else 0

lemma ind_nonneg (t : ℝ) (ρ : Zeros) : 0 ≤ ind t ρ := by
  unfold ind; split_ifs
  · exact mult_nonneg ρ
  · exact le_rfl

lemma ind_le (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 ≤ t) (ρ : Zeros) :
    ind t ρ ≤ (1 / 4 + t ^ 2) * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by
  have h1 := normSq_of_re (re_eq_half hRH ρ)
  have h2 := twenty_le_normSq hRH ρ
  have hm := mult_nonneg ρ
  unfold ind
  split_ifs with h
  · rw [mul_div_assoc', le_div_iff₀ (by positivity), h1]
    have : (ρ : ℂ).im ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ h.1.le h.2 2
    nlinarith
  · positivity

lemma ind_summable (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 ≤ t) : Summable (ind t) :=
  Summable.of_nonneg_of_le (ind_nonneg t) (ind_le hRH ht)
    ((zeroSum_summable hRH).mul_left _)

lemma cnt_eq (t : ℝ) : cnt t = ∑' ρ, ind t ρ := rfl

lemma aF_le (ρ : Zeros) {t : ℝ} : aF ρ t ≤ ind t ρ / t ^ 2 := by
  unfold aF ind
  by_cases h : 0 < (ρ : ℂ).im
  · rw [if_pos h]
    by_cases hl : (ρ : ℂ).im < t
    · rw [indicator_of_mem (show t ∈ Ioi (ρ : ℂ).im from hl), if_pos ⟨h, hl.le⟩]
    · rw [indicator_of_notMem (show t ∉ Ioi (ρ : ℂ).im from hl)]
      split_ifs
      · exact div_nonneg (mult_nonneg ρ) (sq_nonneg _)
      · simp
  · rw [if_neg h]
    simp only [Pi.zero_apply]
    split_ifs
    · exact div_nonneg (mult_nonneg ρ) (sq_nonneg _)
    · simp

lemma bF_le {T : ℝ} (hT : 0 ≤ T) (ρ : Zeros) {t : ℝ} (ht : 0 ≤ t) :
    bF T ρ t ≤ ind t ρ * (2 * T / t ^ 3) := by
  have hc : 0 ≤ 2 * T / t ^ 3 := by positivity
  unfold bF ind
  by_cases h : 0 < (ρ : ℂ).im
  · rw [if_pos h]
    by_cases hl : (ρ : ℂ).im < t
    · rw [indicator_of_mem (show t ∈ Ioi (ρ : ℂ).im from hl), if_pos ⟨h, hl.le⟩]
    · rw [indicator_of_notMem (show t ∉ Ioi (ρ : ℂ).im from hl)]
      split_ifs
      · exact mul_nonneg (mult_nonneg ρ) hc
      · simp
  · rw [if_neg h]
    simp only [Pi.zero_apply]
    split_ifs
    · exact mul_nonneg (mult_nonneg ρ) hc
    · simp

/-- Rosser's bound, in the form used here. -/
theorem cnt_le_Nc (hR : RosserZeroCount) {t : ℝ} (ht : 2 ≤ t) : cnt t ≤ Nc t := by
  have h := (abs_lt.mp (hR t ht)).2
  rw [positiveZeroCount_eq] at h
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  have hll : Real.log (Real.log t) ≤ Real.log t / Real.exp 1 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < Real.log t / Real.exp 1 by positivity)
    rw [Real.log_div hl.ne' (Real.exp_pos 1).ne', Real.log_exp] at h1
    linarith
  have he : 0.443 / Real.exp 1 ≤ 0.163 := by
    rw [div_le_iff₀ (Real.exp_pos 1)]; nlinarith [Real.exp_one_gt_d9]
  have hll' : 0.443 * Real.log (Real.log t) ≤ 0.163 * Real.log t := by
    calc 0.443 * Real.log (Real.log t) ≤ 0.443 * (Real.log t / Real.exp 1) := by gcongr
      _ = 0.443 / Real.exp 1 * Real.log t := by ring
      _ ≤ 0.163 * Real.log t := by gcongr
  have hd : Real.log (t / (2 * π)) = Real.log t - Real.log (2 * π) :=
    Real.log_div (by linarith) (by positivity)
  rw [hd] at h
  unfold Nc
  nlinarith

/-! ### Summing over the zeros -/

theorem Gsum_le_Ub (hRH : RiemannHypothesis) (hR : RosserZeroCount) {T : ℝ} (hT : 4.4 ≤ T) :
    Gsum T ≤ Ub T := by
  have hT0 : 0 < T := by linarith
  -- integrability of each piece
  have hAi : ∀ ρ, Integrable (aF ρ) (volume.restrict (Ioc (4.4 : ℝ) T)) := by
    intro ρ; unfold aF
    split_ifs
    · exact (integrableOn_div_sq (mult ρ)).indicator measurableSet_Ioi
    · exact integrable_zero _ _ _
  have hBi : ∀ ρ, Integrable (bF T ρ) (volume.restrict (Ioi T)) := by
    intro ρ; unfold bF
    split_ifs
    · exact (integrableOn_cube (mult ρ) hT0 (mult_nonneg ρ) le_rfl).indicator measurableSet_Ioi
    · exact integrable_zero _ _ _
  have hA0 : ∀ ρ, 0 ≤ ∫ t in (Ioc (4.4 : ℝ) T), aF ρ t := fun ρ => integral_nonneg (aF_nonneg ρ)
  have hB0 : ∀ ρ, 0 ≤ ∫ t in (Ioi T), bF T ρ t := fun ρ =>
    setIntegral_nonneg measurableSet_Ioi fun t ht => bF_nonneg hT0.le ρ (by linarith [ht.out])
  have hps := posTerm_summable hRH hT0.le
  have hAs : Summable fun ρ => ∫ t in (Ioc (4.4 : ℝ) T), aF ρ t :=
    Summable.of_nonneg_of_le hA0 (fun ρ => by rw [posTerm_eq hRH hT ρ]; linarith [hB0 ρ]) hps
  have hBs : Summable fun ρ => ∫ t in (Ioi T), bF T ρ t :=
    Summable.of_nonneg_of_le hB0 (fun ρ => by rw [posTerm_eq hRH hT ρ]; linarith [hA0 ρ]) hps
  have hAn : Summable fun ρ => ∫ t in (Ioc (4.4 : ℝ) T), ‖aF ρ t‖ := by
    refine hAs.congr fun ρ => ?_
    exact integral_congr_ae (ae_of_all _ fun t => (Real.norm_of_nonneg (aF_nonneg ρ t)).symm)
  have hBn : Summable fun ρ => ∫ t in (Ioi T), ‖bF T ρ t‖ := by
    refine hBs.congr fun ρ => ?_
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    exact (Real.norm_of_nonneg (bF_nonneg hT0.le ρ (by linarith [ht.out]))).symm
  have eA := integral_tsum_of_summable_integral_norm hAi hAn
  have eB := integral_tsum_of_summable_integral_norm hBi hBn
  have eG : Gsum T = (∑' ρ, ∫ t in (Ioc (4.4 : ℝ) T), aF ρ t) + ∑' ρ, ∫ t in (Ioi T), bF T ρ t := by
    rw [Gsum, ← hAs.tsum_add hBs]
    exact tsum_congr (posTerm_eq hRH hT)
  rw [eG, eA, eB]
  -- the first integral
  have hA : ∫ t in (Ioc (4.4 : ℝ) T), (∑' ρ, aF ρ t) ≤ P1 T - P1 4.4 := by
    have hI : IntegrableOn (fun t => Nc t / t ^ 2) (Ioc (4.4 : ℝ) T) := by
      refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hx1 : x ≠ 0 := hx0.ne'
      have hx2 : x ^ 2 ≠ 0 := by positivity
      unfold Nc
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := assumption)
    have hle : ∫ t in (Ioc (4.4 : ℝ) T), (∑' ρ, aF ρ t) ≤ ∫ t in (Ioc (4.4 : ℝ) T), Nc t / t ^ 2 := by
      refine integral_mono_of_nonneg (ae_of_all _ fun t => tsum_nonneg (aF_nonneg · t)) hI ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_)
      have ht0 : 0 ≤ t := by linarith [ht.1]
      have hs := ind_summable hRH ht0
      calc ∑' ρ, aF ρ t ≤ ∑' ρ, ind t ρ / t ^ 2 :=
            (Summable.of_nonneg_of_le (aF_nonneg · t) (fun ρ => aF_le ρ) (hs.div_const _)).tsum_le_tsum
              (fun ρ => aF_le ρ) (hs.div_const _)
        _ = cnt t / t ^ 2 := by rw [tsum_div_const, cnt_eq]
        _ ≤ Nc t / t ^ 2 := by
            gcongr; exact cnt_le_Nc hR (by linarith [ht.1])
    refine hle.trans (le_of_eq ?_)
    rw [← intervalIntegral.integral_of_le hT]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
    · rw [uIcc_of_le hT] at hx; exact hasDerivAt_P1 (by linarith [hx.1])
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hI
  -- the tail integral
  have hB : ∫ t in (Ioi T), (∑' ρ, bF T ρ t)
      ≤ (Real.log T - Real.log (2 * π)) / π + (2.463 + 0.3 / 2) / T + 0.3 * Real.log T / T := by
    have hd : ∀ x ∈ Ici T, HasDerivAt (Rt T) (Nc x * (2 * T / x ^ 3)) x :=
      fun x hx => hasDerivAt_Rt T (by linarith [hx.out])
    have hpos : ∀ x ∈ Ioi T, 0 ≤ Nc x * (2 * T / x ^ 3) := fun x hx => by
      have : T < x := hx.out
      exact mul_nonneg (Nc_pos (by linarith)).le
        (div_nonneg (by linarith) (pow_nonneg (by linarith) 3))
    have hI := integrableOn_Ioi_deriv_of_nonneg' hd hpos (tendsto_Rt T)
    have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos (tendsto_Rt T)
    have hle : ∫ t in (Ioi T), (∑' ρ, bF T ρ t) ≤ ∫ t in (Ioi T), Nc t * (2 * T / t ^ 3) := by
      refine integral_mono_of_nonneg ?_ hI ?_
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
        exact tsum_nonneg fun ρ => bF_nonneg hT0.le ρ (by linarith [ht.out])
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
      have ht0 : 0 ≤ t := by linarith [ht.out]
      have hs := ind_summable hRH ht0
      have hb := fun ρ => bF_le hT0.le ρ ht0
      calc ∑' ρ, bF T ρ t ≤ ∑' ρ, ind t ρ * (2 * T / t ^ 3) :=
            (Summable.of_nonneg_of_le (fun ρ => bF_nonneg hT0.le ρ ht0) hb
              (hs.mul_right _)).tsum_le_tsum hb (hs.mul_right _)
        _ = cnt t * (2 * T / t ^ 3) := by rw [tsum_mul_right, cnt_eq]
        _ ≤ Nc t * (2 * T / t ^ 3) := by
            gcongr; exact cnt_le_Nc hR (by linarith [ht.out])
    refine hle.trans (le_of_eq ?_)
    rw [hval]
    unfold Rt
    field_simp
    ring
  unfold Ub
  linarith

end Schoenfeld
