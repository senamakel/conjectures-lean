import Mathlib

/-!
# The series `ψ(w) − ψ(1) = Σ_k (1/(k+1) − 1/(k+w))`

For real `x` this follows from the recurrence `ψ(x+n) = ψ(x) + Σ_{k<n} 1/(x+k)` and the bounds
`log (x−1) ≤ ψ(x) ≤ log x` (convexity of `log Γ`), which give `ψ(x+n) − ψ(1+n) → 0`.
The complex case `Re w > 1/2` follows by the identity theorem.
-/

open Complex Filter Topology Set

namespace Erdos985.Analytic.BoundsAux

/-- Real logarithmic derivative of `Γ`. -/
noncomputable def rD (x : ℝ) : ℝ := deriv (Real.log ∘ Real.Gamma) x

lemma digamma_ofReal {x : ℝ} (hx : 0 < x) : digamma (x : ℂ) = (rD x : ℂ) := by
  have hne : ∀ m : ℕ, (x : ℂ) ≠ -m := fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [m.cast_nonneg (α := ℝ)]
  have hneR : ∀ m : ℕ, x ≠ -m := fun m h => by linarith [m.cast_nonneg (α := ℝ)]
  have h1 := ((Complex.differentiableAt_Gamma _ hne).hasDerivAt).comp_ofReal
  have h2 := ((Real.differentiableAt_Gamma hneR).hasDerivAt).ofReal_comp
  have heq : (fun t : ℝ => Complex.Gamma (t : ℂ)) = fun t => ((Real.Gamma t : ℝ) : ℂ) :=
    funext Complex.Gamma_ofReal
  rw [heq] at h1
  have hd := h1.unique h2
  rw [digamma_def, logDeriv_apply, hd, Complex.Gamma_ofReal, rD, Function.comp_def,
    deriv.log (Real.differentiableAt_Gamma hneR) (Real.Gamma_pos_of_pos hx).ne']
  push_cast
  rfl

lemma rD_bounds {x : ℝ} (hx : 1 < x) : Real.log (x - 1) ≤ rD x ∧ rD x ≤ Real.log x := by
  let f := Real.log ∘ Real.Gamma
  have hc : ConvexOn ℝ (Ioi 0) f := Real.convexOn_log_Gamma
  have h_rec (y : ℝ) (hy : 0 < y) : f (y + 1) = f y + Real.log y := by
    simp only [f, Function.comp_apply, Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]
  have hder {y : ℝ} (hy : 0 < y) : DifferentiableAt ℝ f y := by
    refine ((Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_)) <;>
    exact fun m ↦ ne_of_gt (by linarith [m.cast_nonneg (α := ℝ)])
  constructor
  · refine (le_of_eq ?_).trans (hc.slope_le_deriv (mem_Ioi.mpr (by linarith : (0:ℝ) < x - 1))
      (mem_Ioi.mpr (by linarith : (0:ℝ) < x)) (by linarith) (hder (by linarith)))
    rw [slope_def_field, show x - (x - 1) = (1:ℝ) by ring, div_one]
    have := h_rec (x - 1) (by linarith)
    rw [show x - 1 + 1 = x by ring] at this
    linarith
  · refine (hc.deriv_le_slope (mem_Ioi.mpr (by linarith : (0:ℝ) < x))
      (mem_Ioi.mpr (by linarith : (0:ℝ) < x + 1)) (by linarith) (hder (by linarith))).trans
      (le_of_eq ?_)
    rw [slope_def_field, show x + 1 - x = (1:ℝ) by ring, div_one, h_rec x (by linarith)]
    ring

lemma log_sub_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Real.log a - Real.log b ≤ a / b - 1 := by
  rw [← Real.log_div ha.ne' hb.ne']
  exact Real.log_le_sub_one_of_pos (by positivity)

lemma tendsto_rD_sub {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => rD (x + n) - rD (1 + n)) atTop (𝓝 0) := by
  have hC := tendsto_const_div_atTop_nhds_zero_nat (x + 4)
  have hC' := hC.neg
  rw [neg_zero] at hC'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hC' hC ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    obtain ⟨l1, -⟩ := rD_bounds (x := x + n) (by linarith)
    obtain ⟨-, u2⟩ := rD_bounds (x := 1 + n) (by linarith)
    have := log_sub_log_le (a := 1 + n) (b := x + n - 1) (by linarith) (by linarith)
    have hq : (1 + n) / (x + n - 1) - 1 ≤ (x + 4) / n := by
      rw [div_sub_one (by linarith), div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    linarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    obtain ⟨-, u1⟩ := rD_bounds (x := x + n) (by linarith)
    obtain ⟨l2, -⟩ := rD_bounds (x := 1 + n) (by linarith)
    rw [show 1 + (n : ℝ) - 1 = n by ring] at l2
    have := log_sub_log_le (a := x + n) (b := n) (by linarith) (by linarith)
    have hq : (x + n) / n - 1 ≤ (x + 4) / n := by
      rw [div_sub_one (by linarith)]
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    linarith

lemma norm_term_le {w : ℂ} (hw : 1 / 2 < w.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)‖ ≤ 2 * (‖w‖ + 1) / ((k : ℝ) + 1) ^ 2 := by
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have hre : ((k : ℝ) + 1) / 2 ≤ ‖(k : ℂ) + w‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp
    linarith [k.cast_nonneg (α := ℝ)]
  have hkw : ((k : ℂ) + w) ≠ 0 := by
    intro h; rw [h, norm_zero] at hre; linarith [k.cast_nonneg (α := ℝ)]
  rw [div_sub_div _ _ hk1 hkw, norm_div, norm_mul]
  have e1 : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (k + 1)
  rw [e1]
  have hnum : ‖1 * ((k : ℂ) + w) - (k + 1) * 1‖ ≤ ‖w‖ + 1 := by
    rw [show 1 * ((k : ℂ) + w) - (k + 1) * 1 = w - 1 by ring]
    exact (norm_sub_le _ _).trans (by simp)
  have hk0 : (0 : ℝ) < k + 1 := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ ‖w‖ + 1 := by positivity
  calc ‖1 * ((k : ℂ) + w) - (k + 1) * 1‖ * ((k : ℝ) + 1) ^ 2
      ≤ (‖w‖ + 1) * ((k : ℝ) + 1) ^ 2 := by gcongr
    _ ≤ 2 * (‖w‖ + 1) * (((k : ℝ) + 1) * ‖(k : ℂ) + w‖) := by
      nlinarith [mul_le_mul_of_nonneg_left hre (by positivity : 0 ≤ 2 * (‖w‖ + 1) * ((k : ℝ) + 1))]

lemma summable_inv_sq_succ : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using this

lemma summable_term {w : ℂ} (hw : 1 / 2 < w.re) :
    Summable fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w) := by
  refine Summable.of_norm_bounded ?_ (norm_term_le hw)
  exact (summable_inv_sq_succ.mul_left (2 * (‖w‖ + 1))).congr (fun k => by ring)

lemma hasSum_digamma_real {x : ℝ} (hx : 1 / 2 < x) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + x)) (digamma x - digamma 1) := by
  have hx0 : 0 < x := by linarith
  have hx' : ∀ m : ℕ, (x : ℂ) ≠ -m := fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [m.cast_nonneg (α := ℝ)]
  have h1' : ∀ m : ℕ, (1 : ℂ) ≠ -m := fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [m.cast_nonneg (α := ℝ)]
  have hpart : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + x)) =
      (digamma x - digamma 1) - (digamma ((x + n : ℝ) : ℂ) - digamma ((1 + n : ℝ) : ℂ)) := by
    intro n
    push_cast
    rw [digamma_apply_add_nat hx' n, digamma_apply_add_nat h1' n, Finset.sum_sub_distrib]
    simp only [one_div, add_comm (1 : ℂ), add_comm (x : ℂ)]
    ring
  have hs := summable_term (w := (x : ℂ)) (by simpa using hx)
  rw [hs.hasSum_iff_tendsto_nat]
  simp_rw [hpart]
  rw [show nhds (digamma (x : ℂ) - digamma 1) = nhds (digamma (x : ℂ) - digamma 1 - 0) by simp]
  refine tendsto_const_nhds.sub ?_
  have : (fun n : ℕ => digamma ((x + n : ℝ) : ℂ) - digamma ((1 + n : ℝ) : ℂ)) =
      fun n : ℕ => ((rD (x + n) - rD (1 + n) : ℝ) : ℂ) := by
    funext n
    rw [digamma_ofReal (by positivity), digamma_ofReal (by positivity)]
    push_cast; ring
  rw [this, show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp]
  exact (Complex.continuous_ofReal.tendsto _).comp (tendsto_rD_sub hx0)

lemma differentiableOn_digamma :
    DifferentiableOn ℂ digamma {z : ℂ | 0 < z.re} := by
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hne : ∀ z ∈ {z : ℂ | 0 < z.re}, ∀ m : ℕ, z ≠ -m := fun z hz m h => by
    rw [h] at hz; simp at hz; linarith [m.cast_nonneg (α := ℝ)]
  have hG : DifferentiableOn ℂ Gamma {z : ℂ | 0 < z.re} := fun z hz =>
    (Complex.differentiableAt_Gamma z (hne z hz)).differentiableWithinAt
  have : digamma = fun z => deriv Gamma z / Gamma z := by
    funext z; rw [digamma_def, logDeriv_apply]
  rw [this]
  exact (hG.deriv ho).div hG (fun z hz => Complex.Gamma_ne_zero_of_re_pos hz)

lemma differentiableOn_tsum_term (R : ℝ) :
    DifferentiableOn ℂ (fun z => ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)))
      ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 R) := by
  refine differentiableOn_tsum_of_summable_norm (u := fun k : ℕ => 2 * (R + 1) / ((k : ℝ) + 1) ^ 2)
    (F := fun (k : ℕ) (z : ℂ) => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z))
    ?_ (fun k => ?_) ((isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball)
    (fun k z hz => ?_)
  · exact (summable_inv_sq_succ.mul_left (2 * (R + 1))).congr (fun k => by ring)
  · intro z hz
    have hkz : (k : ℂ) + z ≠ 0 := by
      intro h
      have h1 := congrArg Complex.re h
      have h2 : 1 / 2 < z.re := hz.1
      simp only [add_re, natCast_re, zero_re] at h1
      linarith [k.cast_nonneg (α := ℝ)]
    have : DifferentiableAt ℂ (fun z : ℂ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)) z := by
      fun_prop (disch := exact hkz)
    exact this.differentiableWithinAt
  · refine (norm_term_le hz.1 k).trans ?_
    have hz2 : ‖z‖ < R := by simpa using hz.2
    gcongr

lemma frequently_eq_one :
    ∃ᶠ z in 𝓝[≠] (1 : ℂ), (digamma z - digamma 1) =
      ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)) := by
  let u : ℕ → ℂ := fun n => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hu : Tendsto u atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall (fun n => ?_)⟩
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ))
      rw [add_zero] at this
      have := (Complex.continuous_ofReal.tendsto _).comp this
      simpa [u, Function.comp_def] using this
    · simp only [mem_compl_iff, mem_singleton_iff, u]
      intro h
      have h1 := congrArg Complex.re h
      simp only [ofReal_re, one_re] at h1
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  refine hu.frequently (Frequently.of_forall (fun n => ?_))
  have hx : 1 / 2 < (1 + 1 / ((n : ℝ) + 1)) := by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  exact (hasSum_digamma_real hx).tsum_eq.symm

theorem hasSum_digamma {w : ℂ} (hw : 1 / 2 < w.re) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)) (digamma w - digamma 1) := by
  have hUo : IsOpen ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) :=
    (isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball
  have hUc : IsPreconnected ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) :=
    ((convex_halfSpace_re_gt _).inter (convex_ball _ _)).isPreconnected
  have hF : DifferentiableOn ℂ (fun z => digamma z - digamma 1)
      ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) := by
    refine (differentiableOn_digamma.mono (fun z hz => ?_)).sub_const _
    have h : 1 / 2 < z.re := hz.1
    show 0 < z.re
    linarith
  have h1U : (1 : ℂ) ∈ ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) :=
    ⟨by norm_num, by rw [Metric.mem_ball, dist_zero_right, norm_one]; linarith [norm_nonneg w]⟩
  have heq := (hF.analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq
    ((differentiableOn_tsum_term _).analyticOnNhd hUo) hUc h1U frequently_eq_one
  have hwU : w ∈ ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) := ⟨hw, by simp⟩
  have := heq hwU
  simp only at this
  rw [this]
  exact (summable_term hw).hasSum

end Erdos985.Analytic.BoundsAux
