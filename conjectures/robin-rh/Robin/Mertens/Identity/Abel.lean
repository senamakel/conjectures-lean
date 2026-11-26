import Robin.Defs

/-!
# Analytic ingredients for `mertens_RH`

Abel summation for `Σ 1/p` against `θ`, the resulting constancy of
`D₁(x) = Σ_{p≤x} 1/p − log log x − (θ x − x)/(x log x) + ∫_x^∞ (θ t − t) w(t) dt`,
bounds on the error terms under `|θ t − t| ≤ C t^{3/4}`, and the convergent sum
`K = Σ_p (c_p − 1/p)`.
-/

namespace Robin

open Filter Topology Real Chebyshev MeasureTheory Set

lemma wM_pos {t : ℝ} (ht : 2 ≤ t) : 0 < wM t := by
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  have : 0 < t := by linarith
  unfold wM; positivity

lemma wM_le {t : ℝ} (ht : 2 ≤ t) : wM t ≤ 4 / t ^ 2 := by
  have h2 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hl2 := Real.log_two_gt_d9
  have hl : 0 < Real.log t := by linarith
  have htp : 0 < t := by linarith
  unfold wM
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (1 + Real.log t) ≤ 4 * Real.log t ^ 2 := by nlinarith
  have ht2 : 0 < t ^ 2 := by positivity
  nlinarith

lemma measurable_wM : Measurable wM := by unfold wM; fun_prop

lemma measurable_theta : Measurable θ := theta_mono.measurable

section Err

variable {C : ℝ} (hC : ∀ t : ℝ, 2 ≤ t → |θ t - t| ≤ C * t ^ ((3 : ℝ) / 4))
include hC

lemma norm_err_mul_wM_le {x : ℝ} (hx : 2 ≤ x) :
    ∀ t ∈ Ioi x, ‖(θ t - t) * wM t‖ ≤ 4 * C * t ^ (-(5 / 4 : ℝ)) := by
  intro t ht
  have ht2 : 2 ≤ t := le_trans hx (le_of_lt ht)
  have htp : 0 < t := by linarith
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (wM_pos ht2)]
  have h1 := hC t ht2
  have h2 := wM_le ht2
  have hrp : t ^ (-(5 / 4 : ℝ)) = t ^ ((3 : ℝ) / 4) / t ^ 2 := by
    rw [show (-(5 / 4 : ℝ)) = (3 : ℝ) / 4 - 2 by norm_num, Real.rpow_sub htp, Real.rpow_two]
  rw [hrp]
  calc |θ t - t| * wM t ≤ (C * t ^ ((3 : ℝ) / 4)) * (4 / t ^ 2) :=
        mul_le_mul h1 h2 (wM_pos ht2).le (le_trans (abs_nonneg _) h1)
    _ = 4 * C * (t ^ ((3 : ℝ) / 4) / t ^ 2) := by ring

lemma integrableOn_err {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (fun t => (θ t - t) * wM t) (Ioi x) := by
  have hg : IntegrableOn (fun t : ℝ => 4 * C * t ^ (-(5 / 4 : ℝ))) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by linarith)).const_mul _
  refine Integrable.mono' hg ?_ ?_
  · exact ((measurable_theta.sub measurable_id).mul measurable_wM).aestronglyMeasurable
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall (norm_err_mul_wM_le hC hx))

lemma norm_integral_err_le {x : ℝ} (hx : 2 ≤ x) :
    ‖∫ t in Ioi x, (θ t - t) * wM t‖ ≤ 16 * C * x ^ (-(1 / 4 : ℝ)) := by
  have hxp : 0 < x := by linarith
  have hg : IntegrableOn (fun t : ℝ => 4 * C * t ^ (-(5 / 4 : ℝ))) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hxp).const_mul _
  calc _ ≤ ∫ t in Ioi x, 4 * C * t ^ (-(5 / 4 : ℝ)) :=
        norm_integral_le_of_norm_le hg ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall (norm_err_mul_wM_le hC hx)))
    _ = _ := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hxp,
          show (-(5 / 4 : ℝ) + 1) = -(1 / 4 : ℝ) by norm_num]
        ring

lemma abs_err_div_le {x : ℝ} (hx : 2 ≤ x) :
    |(θ x - x) / (x * Real.log x)| ≤ 2 * C * x ^ (-(1 / 4 : ℝ)) := by
  have hxp : 0 < x := by linarith
  have hl2 := Real.log_two_gt_d9
  have hl : 1 / 2 ≤ Real.log x := by
    have := Real.log_le_log (by norm_num) hx; linarith
  have h1 := hC x hx
  have hrp : x ^ ((3 : ℝ) / 4) = x ^ (-(1 / 4 : ℝ)) * x := by
    rw [← Real.rpow_add_one hxp.ne']; norm_num
  have hC0 : 0 ≤ C * x ^ (-(1 / 4 : ℝ)) * x := by
    have := le_trans (abs_nonneg _) h1
    rw [hrp] at this; linarith
  rw [abs_div, abs_of_pos (by positivity : 0 < x * Real.log x), div_le_iff₀ (by positivity)]
  calc |θ x - x| ≤ C * x ^ ((3 : ℝ) / 4) := h1
    _ = C * x ^ (-(1 / 4 : ℝ)) * x * 1 := by rw [hrp]; ring
    _ ≤ C * x ^ (-(1 / 4 : ℝ)) * x * (2 * Real.log x) :=
        mul_le_mul_of_nonneg_left (by linarith) hC0
    _ = 2 * C * x ^ (-(1 / 4 : ℝ)) * (x * Real.log x) := by ring

lemma tendsto_err_div :
    Tendsto (fun x : ℝ => (θ x - x) / (x * Real.log x)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => 2 * C * x ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul (2 * C)
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [Real.norm_eq_abs]; exact abs_err_div_le hC hx

lemma tendsto_integral_err :
    Tendsto (fun x : ℝ => ∫ t in Ioi x, (θ t - t) * wM t) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => 16 * C * x ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul (16 * C)
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop 2] with x hx
  exact norm_integral_err_le hC hx

end Err

lemma hasDerivAt_inv_mul_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun u => 1 / (u * Real.log u)) (-wM t) t := by
  have htp : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  have h1 : HasDerivAt (fun u => u * Real.log u) (1 * Real.log t + t * t⁻¹) t :=
    (hasDerivAt_id t).mul (Real.hasDerivAt_log htp.ne')
  have h2 := h1.inv (by positivity)
  convert h2 using 1
  · ext u; simp [one_div]
  · unfold wM; field_simp; ring

lemma continuousOn_wM {a b : ℝ} (ha : 1 < a) : ContinuousOn wM (Icc a b) := by
  intro t ht
  have htp : t ≠ 0 := by linarith [ht.1]
  have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
  have : t ^ 2 * Real.log t ^ 2 ≠ 0 := by positivity
  apply ContinuousAt.continuousWithinAt
  unfold wM
  fun_prop (disch := assumption)

/-- Abel summation: `Σ_{y<p≤x} 1/p = θ(x)/(x log x) − θ(y)/(y log y) + ∫_y^x θ w`. -/
lemma primeSum_inv_sub {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    primeSum (fun p => 1 / (p : ℝ)) x - primeSum (fun p => 1 / (p : ℝ)) y =
      θ x / (x * Real.log x) - θ y / (y * Real.log y) + ∫ t in Ioc y x, θ t * wM t := by
  set c : ℕ → ℝ := fun k => if k.Prime then Real.log k else 0 with hc
  set f : ℝ → ℝ := fun u => 1 / (u * Real.log u) with hf
  have hθc : ∀ t, θ t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k := fun t => by
    rw [theta_eq_sum_Icc, Finset.sum_filter]
  have hderiv : ∀ t ∈ Icc y x, deriv f t = -wM t := fun t ht =>
    (hasDerivAt_inv_mul_log (by linarith [ht.1])).deriv
  have hint : IntegrableOn (deriv f) (Icc y x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).congr_fun (fun t ht => (hderiv t ht).symm)
      measurableSet_Icc
    exact (continuousOn_wM (by linarith)).neg
  have habel := sum_mul_eq_sub_sub_integral_mul c (f := f) (by linarith) hyx
    (fun t ht => (hasDerivAt_inv_mul_log (by linarith [ht.1])).differentiableAt) hint
  have hI : ∫ t in Ioc y x, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k =
      -∫ t in Ioc y x, θ t * wM t := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    rw [hderiv t (Ioc_subset_Icc_self ht), ← hθc]; ring
  rw [hI, ← hθc, ← hθc] at habel
  have hS : ∀ z : ℝ, primeSum (fun p => 1 / (p : ℝ)) z =
      ∑ k ∈ Finset.Iic ⌊z⌋₊, (if k.Prime then 1 / (k : ℝ) else 0) := fun z => by
    unfold primeSum; rw [Finset.sum_filter]
  have hfl : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor hyx
  have hsplit : Finset.Iic ⌊x⌋₊ = Finset.Iic ⌊y⌋₊ ∪ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊ := by
    ext k; simp only [Finset.mem_Iic, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Iic ⌊y⌋₊) (Finset.Ioc ⌊y⌋₊ ⌊x⌋₊) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Finset.mem_Iic, Finset.mem_Ioc] at h1 h2; omega
  rw [hS, hS, hsplit, Finset.sum_union hdisj, add_sub_cancel_left]
  have hterm : ∑ k ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (if k.Prime then 1 / (k : ℝ) else 0) =
      ∑ k ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, f k * c k := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : k.Prime
    · have hk1 : (1 : ℝ) < k := by exact_mod_cast hk.one_lt
      have hl : Real.log k ≠ 0 := (Real.log_pos hk1).ne'
      have hk0 : (k : ℝ) ≠ 0 := by linarith
      simp only [hk, ite_true, hf, hc]
      field_simp
    · simp [hk, hc]
  rw [hterm, habel]
  simp only [hf]
  ring

lemma integral_mul_wM {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    ∫ t in Ioc y x, t * wM t =
      (Real.log (Real.log x) - 1 / Real.log x) - (Real.log (Real.log y) - 1 / Real.log y) := by
  rw [← intervalIntegral.integral_of_le hyx]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hyx] at ht
    have htp : 0 < t := by linarith [ht.1]
    have hl : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have h1 := (Real.hasDerivAt_log htp.ne').log hl.ne'
    have h2 := (Real.hasDerivAt_log htp.ne').inv hl.ne'
    convert h1.sub h2 using 1
    · ext u; simp [one_div]
    · unfold wM; field_simp; ring
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hyx]
    exact continuousOn_id.mul (continuousOn_wM (by linarith))

/-- `D₁(x) = Σ_{p≤x} 1/p − log log x − (θ x − x)/(x log x) + ∫_x^∞ (θ t − t) w(t) dt`. -/
noncomputable def D1 (x : ℝ) : ℝ :=
  primeSum (fun p => 1 / (p : ℝ)) x - Real.log (Real.log x) - (θ x - x) / (x * Real.log x)
    + ∫ t in Ioi x, (θ t - t) * wM t

lemma D1_eq {C : ℝ} (hC : ∀ t : ℝ, 2 ≤ t → |θ t - t| ≤ C * t ^ ((3 : ℝ) / 4))
    {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) : D1 x = D1 y := by
  have hIy := integrableOn_err hC hy
  have hIx := integrableOn_err hC (hy.trans hyx)
  have hsplit : ∫ t in Ioi y, (θ t - t) * wM t =
      (∫ t in Ioc y x, (θ t - t) * wM t) + ∫ t in Ioi x, (θ t - t) * wM t := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hIy.mono_set Ioc_subset_Ioi_self) hIx, Ioc_union_Ioi_eq_Ioi hyx]
  have htw : IntegrableOn (fun t => t * wM t) (Ioc y x) :=
    ((continuousOn_id.mul (continuousOn_wM (by linarith))).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have hθw : IntegrableOn (fun t => θ t * wM t) (Ioc y x) :=
    ((hIy.mono_set Ioc_subset_Ioi_self).add htw).congr_fun (fun t _ => by simp only [Pi.add_apply]; ring)
      measurableSet_Ioc
  have hdiff : ∫ t in Ioc y x, (θ t - t) * wM t =
      (∫ t in Ioc y x, θ t * wM t) - ∫ t in Ioc y x, t * wM t := by
    rw [← integral_sub hθw htw]; congr 1; ext t; ring
  have hab := primeSum_inv_sub hy hyx
  have hxl : 0 < Real.log x := Real.log_pos (by linarith)
  have hyl : 0 < Real.log y := Real.log_pos (by linarith)
  have hx0 : x ≠ 0 := by linarith
  have hy0 : y ≠ 0 := by linarith
  have ex : (θ x - x) / (x * Real.log x) = θ x / (x * Real.log x) - 1 / Real.log x := by
    field_simp
  have ey : (θ y - y) / (y * Real.log y) = θ y / (y * Real.log y) - 1 / Real.log y := by
    field_simp
  unfold D1
  rw [hsplit, hdiff, integral_mul_wM hy hyx, ex, ey]
  linarith

/-! ### The convergent sum `K = Σ_p (c_p − 1/p)` -/

/-- `a n = c_n − 1/n` on primes, `0` otherwise. -/
noncomputable def aK (n : ℕ) : ℝ := if n.Prime then cp n - 1 / (n : ℝ) else 0

lemma cp_sub_bounds {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ cp n - 1 / (n : ℝ) ∧ cp n - 1 / (n : ℝ) ≤ 2 * (1 / (n : ℝ) ^ 2) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < 1 - 1 / (n : ℝ) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  unfold cp
  constructor
  · have := Real.log_le_sub_one_of_pos hpos; linarith
  · have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at h
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have key : (1 - 1 / (n : ℝ))⁻¹ - 1 - 1 / n = 1 / (n * (n - 1)) := by
      field_simp; ring
    have hb : 1 / ((n : ℝ) * (n - 1)) ≤ 2 * (1 / (n : ℝ) ^ 2) := by
      rw [mul_one_div, div_le_div_iff₀ (by nlinarith) (by positivity)]; nlinarith
    linarith

lemma aK_nonneg (n : ℕ) : 0 ≤ aK n := by
  unfold aK; split_ifs with h
  · exact (cp_sub_bounds h.two_le).1
  · exact le_rfl

lemma aK_le (n : ℕ) : aK n ≤ 2 * (1 / (n : ℝ) ^ 2) := by
  unfold aK; split_ifs with h
  · exact (cp_sub_bounds h.two_le).2
  · positivity

lemma summable_aK : Summable aK :=
  Summable.of_nonneg_of_le aK_nonneg aK_le
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 2)

lemma primeSum_aK (x : ℝ) :
    primeSum (fun p => cp p - 1 / (p : ℝ)) x = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), aK n := by
  unfold primeSum aK; rw [Finset.sum_filter]
  congr 1; ext k; simp only [Finset.mem_Iic, Finset.mem_range]; omega

lemma tendsto_primeSum_aK :
    Tendsto (fun x : ℝ => primeSum (fun p => cp p - 1 / (p : ℝ)) x) atTop
      (𝓝 (∑' n, aK n)) := by
  simp_rw [primeSum_aK]
  exact summable_aK.hasSum.tendsto_sum_nat.comp
    ((tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop)

lemma primeSum_aK_le (x : ℝ) :
    primeSum (fun p => cp p - 1 / (p : ℝ)) x ≤ ∑' n, aK n := by
  rw [primeSum_aK]
  exact summable_aK.sum_le_tsum _ (fun i _ => aK_nonneg i)

lemma primeSum_cp_split (x : ℝ) :
    primeSum cp x = primeSum (fun p => 1 / (p : ℝ)) x
      + primeSum (fun p => cp p - 1 / (p : ℝ)) x := by
  unfold primeSum; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

end Robin
