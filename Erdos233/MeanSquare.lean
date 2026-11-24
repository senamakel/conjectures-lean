import Erdos233.MeanValue
import Erdos233.Coeff

/-!
# Step 6. Mean square of the zero contribution

`∫_x^{4x} (y^{3/2} |F δ (log y)|)² dy ≤ 64x³ ∫_x^{4x} |F(log y)|² dy
  = 64x³ ∫_{log x}^{log 4x} e^u |F(u)|² du ≤ 256 x⁴ ∫_{log x}^{log x + 2} |F|²`,
then `mean_value` and `coef_sums`: `≪ x⁴ δ³ log²(2/δ)`.
-/

namespace Erdos233

open Complex Erdos985.Analytic MeasureTheory intervalIntegral

theorem continuous_F (hRH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    Continuous (F δ) := by
  obtain ⟨C, -, hC⟩ := coef_sums hRH
  exact continuous_zeroWave (hC δ hδ hδ').1

theorem mean_square (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
    IntervalIntegrable (fun y => (y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖) ^ 2) volume x (4 * x) ∧
    ∫ y in x..4 * x, (y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖) ^ 2
      ≤ C * x ^ 4 * δ ^ 3 * Real.log (2 / δ) ^ 2 := by
  obtain ⟨Cm, hCm, hM⟩ := mean_value
  obtain ⟨Cc, hCc, hc⟩ := coef_sums hRH
  refine ⟨256 * Cm * Cc, by positivity, fun x hx δ hδ hδ' => ?_⟩
  obtain ⟨hs1, hs2, hsum⟩ := hc δ hδ hδ'
  have hFc : Continuous (F δ) := continuous_zeroWave hs1
  have hx0 : 0 < x := by linarith
  have hx4 : x ≤ 4 * x := by linarith
  -- continuity of the integrands on `[x, 4x]`
  have hlogc : ContinuousOn Real.log (Set.Icc x (4 * x)) :=
    Real.continuousOn_log.mono fun y hy => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact (lt_of_lt_of_le hx0 hy.1).ne'
  have hG : ContinuousOn (fun y => ‖F δ (Real.log y)‖ ^ 2) (Set.Icc x (4 * x)) :=
    ((hFc.comp_continuousOn hlogc).norm).pow 2
  have hpow : ContinuousOn (fun y : ℝ => y ^ (3 / 2 : ℝ)) (Set.Icc x (4 * x)) :=
    fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).continuousWithinAt
  have hInt : ContinuousOn (fun y => (y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖) ^ 2)
      (Set.Icc x (4 * x)) :=
    (hpow.mul ((hFc.comp_continuousOn hlogc).norm)).pow 2
  have hII : IntervalIntegrable (fun y => (y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖) ^ 2)
      volume x (4 * x) :=
    (hInt.mono (by rw [Set.uIcc_of_le hx4])).intervalIntegrable
  refine ⟨hII, ?_⟩
  have hGI : IntervalIntegrable (fun y => ‖F δ (Real.log y)‖ ^ 2) volume x (4 * x) :=
    (hG.mono (by rw [Set.uIcc_of_le hx4])).intervalIntegrable
  -- step 1: `y³ ≤ 64 x³`
  have h1 : ∫ y in x..4 * x, (y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖) ^ 2
      ≤ ∫ y in x..4 * x, 64 * x ^ 3 * ‖F δ (Real.log y)‖ ^ 2 := by
    refine integral_mono_on hx4 hII (hGI.const_mul _) fun y hy => ?_
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have e : (y ^ (3 / 2 : ℝ)) ^ 2 = y ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
    rw [mul_pow, e]
    have : y ^ 3 ≤ (4 * x) ^ 3 := pow_le_pow_left₀ hy0 hy.2 3
    have h0 : 0 ≤ ‖F δ (Real.log y)‖ ^ 2 := by positivity
    nlinarith
  -- step 2: substitution `y = e^u`
  have h2 : ∫ y in x..4 * x, ‖F δ (Real.log y)‖ ^ 2
      = ∫ u in Real.log x..Real.log (4 * x), ‖F δ u‖ ^ 2 * Real.exp u := by
    have hsub := integral_comp_mul_deriv' (a := Real.log x) (b := Real.log (4 * x))
      (f := Real.exp) (f' := Real.exp) (g := fun y => ‖F δ (Real.log y)‖ ^ 2)
      (fun u _ => Real.hasDerivAt_exp u) Real.continuous_exp.continuousOn (by
        refine ContinuousOn.pow (ContinuousOn.norm (hFc.comp_continuousOn ?_)) 2
        exact Real.continuousOn_log.mono fun y hy => by
          obtain ⟨u, -, rfl⟩ := hy
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact (Real.exp_pos u).ne')
    rw [Real.exp_log hx0, Real.exp_log (by linarith)] at hsub
    rw [← hsub]
    refine integral_congr fun u _ => ?_
    simp [Function.comp, Real.log_exp]
  have hlog4 : Real.log (4 * x) = Real.log x + Real.log 4 := by
    rw [Real.log_mul (by norm_num) hx0.ne']; ring
  have hlog4' : Real.log 4 < 2 := by
    have := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hl0 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hab : Real.log x ≤ Real.log (4 * x) := by rw [hlog4]; linarith
  have hFI : ∀ a b : ℝ, IntervalIntegrable (fun u => ‖F δ u‖ ^ 2) volume a b := fun a b =>
    ((hFc.norm).pow 2).intervalIntegrable _ _
  -- step 3: `e^u ≤ 4x`, then enlarge the interval
  have h3 : ∫ u in Real.log x..Real.log (4 * x), ‖F δ u‖ ^ 2 * Real.exp u
      ≤ 4 * x * ∫ u in Real.log x..Real.log x + 2, ‖F δ u‖ ^ 2 := by
    calc ∫ u in Real.log x..Real.log (4 * x), ‖F δ u‖ ^ 2 * Real.exp u
        ≤ ∫ u in Real.log x..Real.log (4 * x), 4 * x * ‖F δ u‖ ^ 2 := by
          refine integral_mono_on hab
            ((((hFc.norm).pow 2).mul Real.continuous_exp).intervalIntegrable _ _)
            ((hFI _ _).const_mul _) fun u hu => ?_
          have : Real.exp u ≤ 4 * x := by
            calc Real.exp u ≤ Real.exp (Real.log (4 * x)) := Real.exp_le_exp.2 hu.2
              _ = 4 * x := Real.exp_log (by linarith)
          have h0 : 0 ≤ ‖F δ u‖ ^ 2 := by positivity
          nlinarith
      _ = 4 * x * ∫ u in Real.log x..Real.log (4 * x), ‖F δ u‖ ^ 2 := integral_const_mul _ _
      _ ≤ 4 * x * ∫ u in Real.log x..Real.log x + 2, ‖F δ u‖ ^ 2 := by
          gcongr
          exact integral_mono_interval le_rfl hab (by rw [hlog4]; linarith)
            (Filter.Eventually.of_forall fun u => by positivity) (hFI _ _)
  have h4 := hM (fun ρ => coef δ ρ) hs1 hs2 (Real.log x)
  have hF_eq : (fun u => ‖F δ u‖ ^ 2) = fun u => ‖zeroWave (fun ρ => coef δ ρ) u‖ ^ 2 := rfl
  have hI0 : 0 ≤ ∫ u in Real.log x..Real.log x + 2, ‖F δ u‖ ^ 2 :=
    integral_nonneg (by linarith) fun u _ => by positivity
  calc ∫ y in x..4 * x, (y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖) ^ 2
      ≤ ∫ y in x..4 * x, 64 * x ^ 3 * ‖F δ (Real.log y)‖ ^ 2 := h1
    _ = 64 * x ^ 3 * ∫ y in x..4 * x, ‖F δ (Real.log y)‖ ^ 2 := integral_const_mul _ _
    _ ≤ 64 * x ^ 3 * (4 * x * ∫ u in Real.log x..Real.log x + 2, ‖F δ u‖ ^ 2) := by
        rw [h2]; gcongr
    _ = 256 * x ^ 4 * ∫ u in Real.log x..Real.log x + 2, ‖F δ u‖ ^ 2 := by ring
    _ ≤ 256 * x ^ 4 * (Cm * (Cc * δ ^ 3 * Real.log (2 / δ) ^ 2)) := by
        gcongr
        exact h4.trans (mul_le_mul_of_nonneg_left hsum hCm.le)
    _ = 256 * Cm * Cc * x ^ 4 * δ ^ 3 * Real.log (2 / δ) ^ 2 := by ring

end Erdos233
