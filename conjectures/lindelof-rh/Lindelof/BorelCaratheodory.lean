import Lindelof.Transfer
import Lindelof.LogZeta

/-!
# Step 6: Borel–Carathéodory gives `‖M s‖ ≪_δ log (|t| + 2)` on `σ ≥ 1/2 + δ`

`Re M = log |zetaQ| ≤ C log (|t| + 2)` by `norm_zeta_le_poly`; apply
`Complex.borelCaratheodory` on discs centred at `5/2 + it` of radius `2 - δ/2`.
-/

namespace Lindelof

open Complex Metric

/-- `zetaQ` is continuous on `Re s > -1`. -/
theorem continuousOn_zetaQ : ContinuousOn zetaQ {s : ℂ | -1 < s.re} := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  apply (differentiable_riemannZeta₁.continuous.continuousAt).div (by fun_prop)
  intro h
  have := congrArg Complex.re h
  simp at this
  simp only [Set.mem_ofPred_eq] at hs
  linarith

/-- For `Re s ≥ 0` and `s ≠ 1`, `‖zetaQ s‖ ≤ ‖ζ s‖`. -/
theorem norm_zetaQ_le_norm_zeta {s : ℂ} (hs : 0 ≤ s.re) (hs1 : s ≠ 1) :
    ‖zetaQ s‖ ≤ ‖riemannZeta s‖ := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hadd : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h1 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul hs1]; field_simp
  have hle : ‖s - 1‖ ≤ ‖s + 1‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp; nlinarith
  have hpos : 0 < ‖s + 1‖ := norm_pos_iff.mpr hadd
  rw [zetaQ, h1, norm_div, norm_mul, div_le_iff₀ hpos]
  calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ ‖s + 1‖ * ‖riemannZeta s‖ := by gcongr
    _ = _ := by ring

/-- Under RH, `‖zetaQ s‖ ≤ K (|t| + 2)` on `1/2 ≤ σ ≤ 5`. -/
theorem norm_zetaQ_le (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 5 → ‖zetaQ s‖ ≤ K * (|s.im| + 2) := by
  obtain ⟨C, hC⟩ := norm_zeta_le_poly hRH
  have hcpt : IsCompact (closedBall (3 : ℂ) (7 / 2)) := isCompact_closedBall _ _
  have hcont : ContinuousOn zetaQ (closedBall (3 : ℂ) (7 / 2)) := by
    refine continuousOn_zetaQ.mono fun z hz => ?_
    have h1 := abs_re_le_norm (z - 3)
    rw [mem_closedBall, dist_eq_norm] at hz
    simp only [sub_re, Set.mem_ofPred_eq] at h1 ⊢
    norm_num at h1
    have := (abs_le.mp (h1.trans hz)).1
    linarith
  obtain ⟨B, hB⟩ := hcpt.exists_bound_of_continuousOn hcont
  refine ⟨max 1 (max B C), le_max_left _ _, fun s hs1 hs5 => ?_⟩
  have hK : 0 ≤ max 1 (max B C) := le_trans zero_le_one (le_max_left _ _)
  have ht : 0 ≤ |s.im| := abs_nonneg _
  by_cases hsm : 1 ≤ |s.im|
  · have hne : s ≠ 1 := by rintro rfl; simp at hsm; linarith
    calc ‖zetaQ s‖ ≤ ‖riemannZeta s‖ := norm_zetaQ_le_norm_zeta (by linarith) hne
      _ ≤ C * |s.im| := hC s hs1 hsm
      _ ≤ max 1 (max B C) * |s.im| := by gcongr; exact le_trans (le_max_right _ _) (le_max_right _ _)
      _ ≤ _ := by nlinarith
  · push Not at hsm
    have hmem : s ∈ closedBall (3 : ℂ) (7 / 2) := by
      rw [mem_closedBall, dist_eq_norm]
      refine (norm_le_abs_re_add_abs_im _).trans ?_
      simp only [sub_re, sub_im]
      norm_num
      have : |s.re - 3| ≤ 5 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    calc ‖zetaQ s‖ ≤ B := hB s hmem
      _ ≤ max 1 (max B C) := le_trans (le_max_left _ _) (le_max_right _ _)
      _ ≤ _ := by nlinarith

/-- If `exp M = g` and `‖g‖ ≤ K (|t| + 2)`, then `Re M ≤ log K + log (|t| + 2)` on
`1/2 < σ ≤ 5`. -/
theorem re_le_of_exp_eq {g M : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K)
    (hKb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 5 → ‖g s‖ ≤ K * (|s.im| + 2))
    (hexp : ∀ s ∈ halfPlane, exp (M s) = g s) {s : ℂ} (hs : 1 / 2 < s.re) (hs5 : s.re ≤ 5) :
    (M s).re ≤ Real.log K + Real.log (|s.im| + 2) := by
  have h := hKb s hs.le hs5
  rw [← hexp s hs, Complex.norm_exp] at h
  rw [← Real.log_mul (by positivity) (by positivity)]
  rw [← Real.log_exp (M s).re]
  exact Real.log_le_log (Real.exp_pos _) h

/-- **Generic Step 6.** Let `M` be a holomorphic logarithm of `g` on `σ > 1/2` with
`‖g‖ ≤ K (|t| + 2)` on `1/2 ≤ σ ≤ 5` and `M` bounded on `2 ≤ σ ≤ 5`. Then for each `δ > 0`,
`‖M s‖ ≤ C_δ log (|t| + 2)` on `1/2 + δ ≤ σ ≤ 2` (Borel–Carathéodory on discs centred at
`5/2 + it`). -/
theorem norm_log_le_of_bounds {g M : ℂ → ℂ} {K : ℝ} (hK1 : 1 ≤ K)
    (hKb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 5 → ‖g s‖ ≤ K * (|s.im| + 2))
    (hM : DifferentiableOn ℂ M halfPlane) (hexp : ∀ s ∈ halfPlane, exp (M s) = g s)
    (hbd : ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → s.re ≤ 5 → ‖M s‖ ≤ C) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ s : ℂ, 1 / 2 + δ ≤ s.re → s.re ≤ 2 →
      ‖M s‖ ≤ C * Real.log (|s.im| + 2) := by
  intro δ hδ
  obtain ⟨C₀, hC₀⟩ := hbd
  set d := min δ 1 with hd
  have hd0 : 0 < d := lt_min hδ one_pos
  have hd1 : d ≤ 1 := min_le_right _ _
  have hdδ : d ≤ δ := min_le_left _ _
  set C₁ := max C₀ 0
  have hC₁ : 0 ≤ C₁ := le_max_right _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  refine ⟨8 / d * (Real.log K / Real.log 2 + 2 + C₁ / Real.log 2), fun s hs hs2 => ?_⟩
  set t := s.im with ht
  set L := Real.log (|t| + 2) with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log two_pos (by linarith [abs_nonneg t])
  have hL0 : 0 < L := hlog2.trans_le hL2
  set c : ℂ := (5 / 2 : ℝ) + t * I with hc
  have hcre : c.re = 5 / 2 := by simp [hc]
  have hcim : c.im = t := by simp [hc]
  set R : ℝ := 2 - d / 2 with hR
  set Mx : ℝ := Real.log K + Real.log (|t| + 4) with hMx
  have hlog4 : 0 < Real.log (|t| + 4) := Real.log_pos (by linarith [abs_nonneg t])
  have hMx0 : 0 < Mx := by positivity
  set f : ℂ → ℂ := fun z => M (c + z) with hf
  -- the disc `c + ball 0 R` lies in the strip `1/2 + d/2 < σ < 9/2`
  have hball : ∀ z ∈ ball (0 : ℂ) R, 1 / 2 < (c + z).re ∧ (c + z).re ≤ 5 ∧
      |(c + z).im| ≤ |t| + 2 := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    have h1 := abs_le.mp ((abs_re_le_norm z).trans hz.le)
    have h2 := (abs_im_le_norm z).trans hz.le
    simp only [add_re, add_im, hcre, hcim]
    refine ⟨by linarith, by linarith, ?_⟩
    calc |t + z.im| ≤ |t| + |z.im| := abs_add_le _ _
      _ ≤ |t| + 2 := by linarith
  have hfd : DifferentiableOn ℂ f (ball 0 R) := by
    intro z hz
    have hmem : c + z ∈ halfPlane := (hball z hz).1
    have : DifferentiableAt ℂ M (c + z) :=
      hM.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds hmem)
    exact (this.comp z (by fun_prop)).differentiableWithinAt
  have hfre : Set.MapsTo f (ball 0 R) {w | w.re ≤ Mx} := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hball z hz
    have := re_le_of_exp_eq hK1 hKb hexp h1 h2
    simp only [Set.mem_ofPred_eq, hf, hMx]
    refine this.trans (add_le_add le_rfl (Real.log_le_log (by positivity) (by linarith)))
  -- the point
  set z₀ := s - c with hz₀
  have hz₀n : ‖z₀‖ ≤ 2 - d := by
    refine (norm_le_abs_re_add_abs_im _).trans ?_
    simp only [hz₀, sub_re, sub_im, hcre, hcim, ht, sub_self, abs_zero, add_zero]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hR0 : 0 < R := by rw [hR]; linarith
  have hz₀b : z₀ ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; linarith
  have hBC := Complex.borelCaratheodory hMx0 hfd hfre hR0 hz₀b
  have hfz : f z₀ = M s := by simp [hf, hz₀]
  have hf0 : ‖f 0‖ ≤ C₁ := by
    simp only [hf, add_zero]
    exact (hC₀ c (by rw [hcre]; norm_num) (by rw [hcre]; norm_num)).trans (le_max_left _ _)
  rw [hfz] at hBC
  set r := ‖z₀‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hRr : d / 2 ≤ R - r := by rw [hR]; linarith
  have hRr0 : 0 < R - r := by linarith
  have key : ‖M s‖ ≤ (2 * Mx * 2 + C₁ * 4) / (d / 2) := by
    refine hBC.trans ?_
    rw [← add_div]
    calc (2 * Mx * r + ‖f 0‖ * (R + r)) / (R - r) ≤ (2 * Mx * 2 + C₁ * 4) / (R - r) := by
          gcongr
          · linarith
          · linarith
      _ ≤ _ := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hRr
  -- convert to `log (|t| + 2)`
  have hlt4 : Real.log (|t| + 4) ≤ L + L := by
    rw [hL, ← Real.log_mul (by positivity) (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    nlinarith [abs_nonneg t]
  have hKL : Real.log K ≤ Real.log K / Real.log 2 * L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hL2 hlogK
  have hCL : C₁ ≤ C₁ / Real.log 2 * L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hL2 hC₁
  refine key.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have : 8 / d * (Real.log K / Real.log 2 + 2 + C₁ / Real.log 2) * L * (d / 2)
      = 4 * (Real.log K / Real.log 2 * L + 2 * L + C₁ / Real.log 2 * L) := by
    field_simp
    norm_num
  rw [this]
  linarith

theorem norm_log_zetaQ_le (hRH : RiemannHypothesis) {M : ℂ → ℂ}
    (hM : DifferentiableOn ℂ M halfPlane) (hexp : ∀ s ∈ halfPlane, exp (M s) = zetaQ s)
    (hbd : ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → s.re ≤ 5 → ‖M s‖ ≤ C) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ s : ℂ, 1 / 2 + δ ≤ s.re → s.re ≤ 2 →
      ‖M s‖ ≤ C * Real.log (|s.im| + 2) := by
  obtain ⟨K, hK1, hKb⟩ := norm_zetaQ_le hRH
  exact norm_log_le_of_bounds hK1 hKb hM hexp hbd

end Lindelof
