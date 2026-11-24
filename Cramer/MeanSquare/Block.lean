import Erdos233.MeanValue
import Cramer.MeanSquare.Explicit
import Cramer.MeanSquare.Psi

/-!
# Mean square, step 4: one block `[Y, 4Y]`

With `δ = 1/Y` and `y ∈ [Y, 4Y]`, the step `h = δy` lies in `[1, 4]`, so

`|ψ(y) − y| ≤ B + √y ‖G δ (log y)‖ + 4 log(y + 4)`

(`first_diff_bound` and `psi1_diff_bounds`). The mean value theorem for zero waves
(erdos-233's `mean_value`, a Gaussian weight against the unit-window zero count) and
`acoef_sums` give `∫_Y^{4Y} y ‖G δ (log y)‖² dy ≤ C Y²` uniformly in `δ`, hence
`∫_Y^{4Y} (ψ(y) − y)² dy ≤ C Y²`.
-/

namespace Cramer.MeanSq

open Complex Erdos985.Analytic Erdos233 MeasureTheory intervalIntegral Chebyshev

theorem G_mean_square (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
    IntervalIntegrable (fun y => y * ‖G δ (Real.log y)‖ ^ 2) volume x (4 * x) ∧
    ∫ y in x..4 * x, y * ‖G δ (Real.log y)‖ ^ 2 ≤ C * x ^ 2 := by
  obtain ⟨Cm, hCm, hM⟩ := mean_value
  obtain ⟨Ca, hCa, hc⟩ := acoef_sums hRH
  refine ⟨16 * Cm * Ca, by positivity, fun x hx δ hδ hδ' => ?_⟩
  obtain ⟨hs1, hs2, hsum⟩ := hc δ hδ hδ'
  have hFc : Continuous (G δ) := continuous_zeroWave hs1
  have hx0 : 0 < x := by linarith
  have hx4 : x ≤ 4 * x := by linarith
  have hlogc : ContinuousOn Real.log (Set.Icc x (4 * x)) :=
    Real.continuousOn_log.mono fun y hy => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact (lt_of_lt_of_le hx0 hy.1).ne'
  have hG : ContinuousOn (fun y => ‖G δ (Real.log y)‖ ^ 2) (Set.Icc x (4 * x)) :=
    ((hFc.comp_continuousOn hlogc).norm).pow 2
  have hInt : ContinuousOn (fun y => y * ‖G δ (Real.log y)‖ ^ 2) (Set.Icc x (4 * x)) :=
    continuousOn_id.mul hG
  have hII : IntervalIntegrable (fun y => y * ‖G δ (Real.log y)‖ ^ 2) volume x (4 * x) :=
    (hInt.mono (by rw [Set.uIcc_of_le hx4])).intervalIntegrable
  refine ⟨hII, ?_⟩
  have hGI : IntervalIntegrable (fun y => ‖G δ (Real.log y)‖ ^ 2) volume x (4 * x) :=
    (hG.mono (by rw [Set.uIcc_of_le hx4])).intervalIntegrable
  have h1 : ∫ y in x..4 * x, y * ‖G δ (Real.log y)‖ ^ 2
      ≤ ∫ y in x..4 * x, 4 * x * ‖G δ (Real.log y)‖ ^ 2 := by
    refine integral_mono_on hx4 hII (hGI.const_mul _) fun y hy => ?_
    have h0 : 0 ≤ ‖G δ (Real.log y)‖ ^ 2 := by positivity
    nlinarith [hy.2]
  have h2 : ∫ y in x..4 * x, ‖G δ (Real.log y)‖ ^ 2
      = ∫ u in Real.log x..Real.log (4 * x), ‖G δ u‖ ^ 2 * Real.exp u := by
    have hsub := integral_comp_mul_deriv' (a := Real.log x) (b := Real.log (4 * x))
      (f := Real.exp) (f' := Real.exp) (g := fun y => ‖G δ (Real.log y)‖ ^ 2)
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
  have hFI : ∀ a b : ℝ, IntervalIntegrable (fun u => ‖G δ u‖ ^ 2) volume a b := fun a b =>
    ((hFc.norm).pow 2).intervalIntegrable _ _
  have h3 : ∫ u in Real.log x..Real.log (4 * x), ‖G δ u‖ ^ 2 * Real.exp u
      ≤ 4 * x * ∫ u in Real.log x..Real.log x + 2, ‖G δ u‖ ^ 2 := by
    calc ∫ u in Real.log x..Real.log (4 * x), ‖G δ u‖ ^ 2 * Real.exp u
        ≤ ∫ u in Real.log x..Real.log (4 * x), 4 * x * ‖G δ u‖ ^ 2 := by
          refine integral_mono_on hab
            ((((hFc.norm).pow 2).mul Real.continuous_exp).intervalIntegrable _ _)
            ((hFI _ _).const_mul _) fun u hu => ?_
          have : Real.exp u ≤ 4 * x := by
            calc Real.exp u ≤ Real.exp (Real.log (4 * x)) := Real.exp_le_exp.2 hu.2
              _ = 4 * x := Real.exp_log (by linarith)
          have h0 : 0 ≤ ‖G δ u‖ ^ 2 := by positivity
          nlinarith
      _ = 4 * x * ∫ u in Real.log x..Real.log (4 * x), ‖G δ u‖ ^ 2 := integral_const_mul _ _
      _ ≤ 4 * x * ∫ u in Real.log x..Real.log x + 2, ‖G δ u‖ ^ 2 := by
          gcongr
          exact integral_mono_interval le_rfl hab (by rw [hlog4]; linarith)
            (Filter.Eventually.of_forall fun u => by positivity) (hFI _ _)
  have h4 := hM (fun ρ => acoef δ ρ) hs1 hs2 (Real.log x)
  have hI0 : 0 ≤ ∫ u in Real.log x..Real.log x + 2, ‖G δ u‖ ^ 2 :=
    integral_nonneg (by linarith) fun u _ => by positivity
  calc ∫ y in x..4 * x, y * ‖G δ (Real.log y)‖ ^ 2
      ≤ ∫ y in x..4 * x, 4 * x * ‖G δ (Real.log y)‖ ^ 2 := h1
    _ = 4 * x * ∫ y in x..4 * x, ‖G δ (Real.log y)‖ ^ 2 := integral_const_mul _ _
    _ ≤ 4 * x * (4 * x * ∫ u in Real.log x..Real.log x + 2, ‖G δ u‖ ^ 2) := by
        rw [h2]; gcongr
    _ = 16 * x ^ 2 * ∫ u in Real.log x..Real.log x + 2, ‖G δ u‖ ^ 2 := by ring
    _ ≤ 16 * x ^ 2 * (Cm * Ca) := by
        gcongr
        exact h4.trans (mul_le_mul_of_nonneg_left hsum hCm.le)
    _ = 16 * Cm * Ca * x ^ 2 := by ring

lemma log_sq_le {t : ℝ} (ht : 1 ≤ t) : Real.log t ^ 2 ≤ 4 * t := by
  have h0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have h1 := Real.log_le_rpow_div (x := t) (by linarith) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at h1
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt (by linarith)
  have : Real.log t ≤ 2 * Real.sqrt t := by linarith
  nlinarith [Real.sqrt_nonneg t]

/-- **One block.** Under RH, `∫_Y^{4Y} (ψ(y) − y)² dy ≤ C Y²` for every `Y ≥ 2`. -/
theorem block_bound (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 2 ≤ Y →
    ∫ y in Y..4 * Y, (ψ y - y) ^ 2 ≤ C * Y ^ 2 := by
  obtain ⟨B, hB0, hB⟩ := first_diff_bound hRH
  obtain ⟨Cg, hCg, hG⟩ := G_mean_square hRH
  refine ⟨9 * B ^ 2 + 3456 + 3 * Cg, by positivity, fun Y hY => ?_⟩
  have hY0 : 0 < Y := by linarith
  set δ : ℝ := 1 / Y with hδdef
  have hδ : 0 < δ := by positivity
  have hδ' : δ ≤ 1 / 2 := by
    rw [hδdef, div_le_div_iff₀ hY0 (by norm_num)]; linarith
  obtain ⟨hII, hGint⟩ := hG Y (by linarith) δ hδ hδ'
  set g : ℝ → ℝ := fun y => (3 * B ^ 2 + 1152 * Y) + 3 * (y * ‖G δ (Real.log y)‖ ^ 2) with hg
  have hpt : ∀ y ∈ Set.Icc Y (4 * Y), (ψ y - y) ^ 2 ≤ g y := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hy0 : 0 < y := by linarith
    set h : ℝ := δ * y with hhdef
    have hh : h = y / Y := by rw [hhdef, hδdef]; ring
    have hh1 : 1 ≤ h := by rw [hh, le_div_iff₀ hY0]; linarith
    have hh4 : h ≤ 4 := by rw [hh, div_le_iff₀ hY0]; linarith
    have hfd := hB δ y hδ hδ' (by linarith) hh1 hh4
    have hyh : y * (1 + δ) = y + h := by rw [hhdef]; ring
    rw [hyh] at hfd
    obtain ⟨lo, hi⟩ := psi1_diff_bounds hy0.le (by linarith : 0 ≤ h)
    have hmono : ψ (y + h) ≤ ψ (y + 4) := psi_mono (by linarith)
    have h4 := psi_add_four_sub_le hy0.le
    set D := psi1 (y + h) - psi1 y with hD
    set P := B + Real.sqrt y * ‖G δ (Real.log y)‖ with hP
    set L := Real.log (y + 4) with hL
    have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
    have hP0 : 0 ≤ P := by positivity
    rw [abs_le] at hfd
    have hh0 : 0 < h := by linarith
    have up : ψ y - y ≤ P + 4 * L := by
      refine le_of_mul_le_mul_left ?_ hh0
      nlinarith
    have dn : -(P + 4 * L) ≤ ψ y - y := by
      refine le_of_mul_le_mul_left ?_ hh0
      nlinarith
    have hsq : (ψ y - y) ^ 2 ≤ (P + 4 * L) ^ 2 := by
      have : |ψ y - y| ≤ P + 4 * L := abs_le.2 ⟨dn, up⟩
      calc (ψ y - y) ^ 2 = |ψ y - y| ^ 2 := (sq_abs _).symm
        _ ≤ (P + 4 * L) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    have hs : (Real.sqrt y * ‖G δ (Real.log y)‖) ^ 2 = y * ‖G δ (Real.log y)‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hy0.le]
    have hLsq : L ^ 2 ≤ 4 * (y + 4) := log_sq_le (by linarith)
    have h3 : (P + 4 * L) ^ 2 ≤ 3 * (B ^ 2 + (Real.sqrt y * ‖G δ (Real.log y)‖) ^ 2
        + 16 * L ^ 2) := by
      rw [hP]
      nlinarith [sq_nonneg (B - Real.sqrt y * ‖G δ (Real.log y)‖),
        sq_nonneg (B - 4 * L), sq_nonneg (Real.sqrt y * ‖G δ (Real.log y)‖ - 4 * L)]
    simp only [hg]
    rw [hs] at h3
    nlinarith
  have hY4 : Y ≤ 4 * Y := by linarith
  have hgI : IntervalIntegrable g volume Y (4 * Y) := by
    simp only [hg]
    exact (intervalIntegrable_const).add (hII.const_mul 3)
  calc ∫ y in Y..4 * Y, (ψ y - y) ^ 2 ≤ ∫ y in Y..4 * Y, g y :=
        integral_mono_on hY4 (intervalIntegrable_sq _ _) hgI hpt
    _ = (4 * Y - Y) * (3 * B ^ 2 + 1152 * Y)
          + 3 * ∫ y in Y..4 * Y, y * ‖G δ (Real.log y)‖ ^ 2 := by
        simp only [hg]
        rw [integral_add intervalIntegrable_const (hII.const_mul 3), intervalIntegral.integral_const,
          intervalIntegral.integral_const_mul, smul_eq_mul]
    _ ≤ (4 * Y - Y) * (3 * B ^ 2 + 1152 * Y) + 3 * (Cg * Y ^ 2) := by gcongr
    _ ≤ (9 * B ^ 2 + 3456 + 3 * Cg) * Y ^ 2 := by
        have hYY : Y ≤ Y ^ 2 := by nlinarith
        nlinarith [sq_nonneg B]

end Cramer.MeanSq
