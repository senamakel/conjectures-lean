import Robin.RH.Psi1
import Robin.Mertens.Identity

/-!
# The tail `∫_x^∞ (t − θ(t)) w(t) dt` for `x ≥ e^{30}`

`t − θ = (t − ψ) + (ψ − θ)`. The first part is integrated by parts against `E = Ψ₁ − t²/2`
(`|E(t)| ≤ t^{3/2}/20 + 4t`, right derivative `ψ(t) − t`), giving `≤ 0.32/(√x log x)`. The second
uses `ψ − θ ≤ ψ(√t) + ψ(t^{1/3}) + ψ(t^{1/5})` and `ψ(s) ≤ s + s^{3/4}`; its main part is
`∫_x^∞ √t w(t) dt ≤ (31/30)·2/(√x log x)`.
-/

namespace Robin

open Filter Topology Real Chebyshev MeasureTheory Set

/-- `w(t) ≤ (31/30)/(L t²)` when `log t ≥ L ≥ 30`. -/
lemma wM_le_of_log {t L : ℝ} (hL : 30 ≤ L) (ht0 : 0 < t) (ht : L ≤ Real.log t) :
    wM t ≤ (31 / 30) / (L * t ^ 2) := by
  have hl : 0 < Real.log t := by linarith
  have hL0 : 0 < L := by linarith
  unfold wM
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : L * (1 + Real.log t) ≤ (31 / 30) * Real.log t ^ 2 := by nlinarith
  have ht2 : 0 < t ^ 2 := by positivity
  calc (1 + Real.log t) * (L * t ^ 2) = t ^ 2 * (L * (1 + Real.log t)) := by ring
    _ ≤ t ^ 2 * ((31 / 30) * Real.log t ^ 2) := mul_le_mul_of_nonneg_left h1 ht2.le
    _ = 31 / 30 * (t ^ 2 * Real.log t ^ 2) := by ring

/-- The derivative of `w`. -/
noncomputable def wM' (t : ℝ) : ℝ :=
  -(2 * Real.log t ^ 2 + 3 * Real.log t + 2) / (t ^ 3 * Real.log t ^ 3)

lemma hasDerivAt_wM {t : ℝ} (ht : 1 < t) : HasDerivAt wM (wM' t) t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  have hN : HasDerivAt (fun u => 1 + Real.log u) (1 / t) t := by
    simpa using (Real.hasDerivAt_log ht0.ne').const_add 1
  have hD : HasDerivAt (fun u => u ^ 2 * Real.log u ^ 2)
      (2 * t * Real.log t ^ 2 + t ^ 2 * (2 * Real.log t * (1 / t))) t := by
    have h1 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 : HasDerivAt (fun u => Real.log u ^ 2) (2 * Real.log t * (1 / t)) t := by
      have h := (Real.hasDerivAt_log ht0.ne').mul (Real.hasDerivAt_log ht0.ne')
      have e : (fun u => Real.log u ^ 2) = fun u => Real.log u * Real.log u := by
        funext u; ring
      rw [e]; convert h using 1; field_simp; ring
    exact h1.mul h2
  have hDn : t ^ 2 * Real.log t ^ 2 ≠ 0 := by positivity
  have := hN.div hD hDn
  unfold wM
  convert this using 1
  unfold wM'
  field_simp
  ring

lemma abs_wM'_le {t L : ℝ} (hL : 30 ≤ L) (ht0 : 0 < t) (ht : L ≤ Real.log t) :
    |wM' t| ≤ 2.103 / (L * t ^ 3) := by
  have hl : 0 < Real.log t := by linarith
  have hL0 : 0 < L := by linarith
  unfold wM'
  rw [abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  set l := Real.log t
  have h1 : L * (2 * l ^ 2 + 3 * l + 2) ≤ 2.103 * l ^ 3 := by
    have : L * (2 * l ^ 2 + 3 * l + 2) ≤ l * (2 * l ^ 2 + 3 * l + 2) :=
      mul_le_mul_of_nonneg_right ht (by positivity)
    nlinarith
  have ht3 : 0 < t ^ 3 := by positivity
  calc (2 * l ^ 2 + 3 * l + 2) * (L * t ^ 3) = t ^ 3 * (L * (2 * l ^ 2 + 3 * l + 2)) := by ring
    _ ≤ t ^ 3 * (2.103 * l ^ 3) := mul_le_mul_of_nonneg_left h1 ht3.le
    _ = 2.103 * (t ^ 3 * l ^ 3) := by ring

/-- `E(t) = Ψ₁(t) − t²/2`. -/
noncomputable def E1 (t : ℝ) : ℝ := psi1 t - t ^ 2 / 2

lemma E1_hasDerivWithinAt (t : ℝ) : HasDerivWithinAt E1 (ψ t - t) (Ioi t) t := by
  have h2 : HasDerivWithinAt (fun u : ℝ => u ^ 2 / 2) t (Ioi t) t := by
    have := ((hasDerivAt_pow 2 t).div_const 2).hasDerivWithinAt (s := Ioi t)
    convert this using 1; push_cast; ring
  exact (psi1_hasDerivWithinAt t).sub h2

lemma E1_continuous : Continuous E1 := by
  unfold E1; exact psi1_continuous.sub (by fun_prop)

lemma continuousAt_wM' {t : ℝ} (ht : 1 < t) : ContinuousAt wM' t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  unfold wM'
  exact ((((continuousAt_log ht0).pow 2).const_mul 2).add
    ((continuousAt_log ht0).const_mul 3) |>.add continuousAt_const).neg.div
    ((continuousAt_id.pow 3).mul ((continuousAt_log ht0).pow 3))
    (mul_ne_zero (pow_ne_zero 3 ht0) (pow_ne_zero 3 hl))

lemma psi_intervalIntegrable (a b : ℝ) : IntervalIntegrable ψ volume a b :=
  psi_mono.intervalIntegrable

/-- Integration by parts: `∫_x^y (t − ψ) w = E(x)w(x) − E(y)w(y) + ∫_x^y E w'`. -/
lemma integral_sub_psi_wM {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    ∫ t in x..y, (t - ψ t) * wM t = E1 x * wM x - E1 y * wM y + ∫ t in x..y, E1 t * wM' t := by
  have hcw : ContinuousOn wM (Icc x y) := continuousOn_wM hx
  have hcw' : ContinuousOn wM' (Icc x y) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    unfold wM'
    exact ((((continuousAt_log ht0).pow 2).const_mul 2).add
      ((continuousAt_log ht0).const_mul 3) |>.add continuousAt_const).neg.div
      ((continuousAt_id.pow 3).mul ((continuousAt_log ht0).pow 3))
      (mul_ne_zero (pow_ne_zero 3 ht0) (pow_ne_zero 3 hl)) |>.continuousWithinAt
  have hu' : IntervalIntegrable (fun t => ψ t - t) volume x y :=
    (psi_intervalIntegrable x y).sub (continuous_id.intervalIntegrable _ _)
  have hv' : IntervalIntegrable wM' volume x y :=
    (hcw'.intervalIntegrable_of_Icc hxy)
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    (u := E1) (v := wM) (u' := fun t => ψ t - t) (v' := wM') (a := x) (b := y)
    E1_continuous.continuousOn (by rw [uIcc_of_le hxy]; exact hcw)
    (fun t _ => E1_hasDerivWithinAt t)
    (fun t ht => by
      rw [min_eq_left hxy] at ht
      exact (hasDerivAt_wM (by linarith [ht.1])).hasDerivWithinAt) hu' hv'
  have hi1 : IntervalIntegrable (fun t => (ψ t - t) * wM t) volume x y :=
    hu'.mul_continuousOn (by rw [uIcc_of_le hxy]; exact hcw)
  have hi2 : IntervalIntegrable (fun t => E1 t * wM' t) volume x y :=
    (E1_continuous.continuousOn.mul hcw').intervalIntegrable_of_Icc hxy
  rw [intervalIntegral.integral_add hi1 hi2] at hibp
  have hneg : ∫ t in x..y, (t - ψ t) * wM t = -∫ t in x..y, (ψ t - t) * wM t := by
    rw [← intervalIntegral.integral_neg]; congr 1; ext t; ring
  rw [hneg]
  linarith

/-- `A(t) = t^{-1/2}/20 + 4 t^{-1}`, so that `|E(t)| ≤ t² A(t)`. -/
noncomputable def Abd (t : ℝ) : ℝ := t ^ (-(1 : ℝ) / 2) / 20 + 4 * t ^ (-(1 : ℝ))

lemma Abd_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ Abd t := by unfold Abd; positivity

lemma Abd_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : Abd y ≤ Abd x := by
  unfold Abd
  have h1 := Real.rpow_le_rpow_of_nonpos hx hxy (show -(1 : ℝ) / 2 ≤ 0 by norm_num)
  have h2 := Real.rpow_le_rpow_of_nonpos hx hxy (show -(1 : ℝ) ≤ 0 by norm_num)
  linarith

lemma E1_le_Abd (hB : Psi1NatBound) {t : ℝ} (ht : 16 ≤ t) : |E1 t| ≤ t ^ 2 * Abd t := by
  have ht0 : 0 < t := by linarith
  have h := psi1_bound hB ht
  have e1 : t ^ ((3 : ℝ) / 2) = t ^ 2 * t ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht0]; norm_num
  have e2 : 4 * t = t ^ 2 * (4 * t ^ (-(1 : ℝ))) := by
    rw [Real.rpow_neg_one]; field_simp
  unfold E1 Abd
  calc |psi1 t - t ^ 2 / 2| ≤ t ^ ((3 : ℝ) / 2) / 20 + 4 * t := h
    _ = t ^ 2 * (t ^ (-(1 : ℝ) / 2) / 20 + 4 * t ^ (-(1 : ℝ))) := by
      rw [e1, e2]; ring

lemma E1_wM_le (hB : Psi1NatBound) {t L : ℝ} (hL : 30 ≤ L) (ht16 : 16 ≤ t)
    (ht : L ≤ Real.log t) : |E1 t * wM t| ≤ (31 / 30) * Abd t / L := by
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := by linarith
  have hw0 : 0 < wM t := wM_pos (by linarith)
  rw [abs_mul, abs_of_pos hw0]
  calc |E1 t| * wM t ≤ (t ^ 2 * Abd t) * ((31 / 30) / (L * t ^ 2)) :=
        mul_le_mul (E1_le_Abd hB ht16) (wM_le_of_log hL ht0 ht) hw0.le
          (by have := Abd_nonneg ht0; positivity)
    _ = (31 / 30) * Abd t / L := by field_simp

lemma E1_wM'_le (hB : Psi1NatBound) {t L : ℝ} (hL : 30 ≤ L) (ht16 : 16 ≤ t)
    (ht : L ≤ Real.log t) :
    |E1 t * wM' t| ≤ (2.103 / L) * (t ^ (-(3 : ℝ) / 2) / 20 + 4 * t ^ (-(2 : ℝ))) := by
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := by linarith
  rw [abs_mul]
  have e : t ^ 2 * Abd t * (2.103 / (L * t ^ 3))
      = (2.103 / L) * (t ^ (-(3 : ℝ) / 2) / 20 + 4 * t ^ (-(2 : ℝ))) := by
    unfold Abd
    have e1 : t ^ (-(3 : ℝ) / 2) = t ^ (-(1 : ℝ) / 2) * t⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ht0]; norm_num
    have e2 : t ^ (-(2 : ℝ)) = t ^ (-(1 : ℝ)) * t⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ht0]; norm_num
    rw [e1, e2]; field_simp
  rw [← e]
  exact mul_le_mul (E1_le_Abd hB ht16) (abs_wM'_le hL ht0 ht) (abs_nonneg _)
    (by have := Abd_nonneg ht0; positivity)

/-- The interval bound for the `t − ψ` part. -/
lemma integral_sub_psi_wM_le (hB : Psi1NatBound) {x y : ℝ} (hx : Real.exp 30 ≤ x)
    (hxy : x ≤ y) :
    ∫ t in x..y, (t - ψ t) * wM t ≤
      2 * ((31 / 30) * Abd x / Real.log x)
        + (2.103 / Real.log x) * (x ^ (-(1 : ℝ) / 2) / 10 + 4 * x ^ (-(1 : ℝ))) := by
  have he30 : (31 : ℝ) ≤ Real.exp 30 := by
    have := Real.add_one_le_exp (30 : ℝ); linarith
  have hx0 : 0 < x := by linarith
  have hL : 30 ≤ Real.log x := by
    rw [← Real.log_exp 30]; exact Real.log_le_log (Real.exp_pos _) hx
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hlog : ∀ t, x ≤ t → L ≤ Real.log t := fun t ht => Real.log_le_log hx0 ht
  rw [integral_sub_psi_wM (by linarith) hxy]
  have h1 : E1 x * wM x ≤ (31 / 30) * Abd x / L :=
    (le_abs_self _).trans (E1_wM_le hB hL (by linarith) le_rfl)
  have h2 : -(E1 y * wM y) ≤ (31 / 30) * Abd x / L := by
    have := (neg_le_abs (E1 y * wM y)).trans (E1_wM_le hB hL (by linarith) (hlog y hxy))
    have hA := Abd_anti hx0 hxy
    have : (31 / 30) * Abd y / L ≤ (31 / 30) * Abd x / L := by
      apply div_le_div_of_nonneg_right _ hL0.le; linarith
    linarith
  -- the integral
  have hcont : ContinuousOn (fun t => (2.103 / L) * (t ^ (-(3 : ℝ) / 2) / 20 + 4 * t ^ (-(2 : ℝ))))
      (Icc x y) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (continuousAt_const.mul (((Real.continuousAt_rpow_const _ _ (Or.inl ht0)).div_const _).add
      (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl ht0))))).continuousWithinAt
  have hint1 : IntervalIntegrable (fun t => E1 t * wM' t) volume x y := by
    have hcw' : ContinuousOn wM' (Icc x y) := by
      intro t ht
      exact (continuousAt_wM' (by linarith [ht.1])).continuousWithinAt
    exact (E1_continuous.continuousOn.mul hcw').intervalIntegrable_of_Icc hxy
  have h3 : ∫ t in x..y, E1 t * wM' t ≤
      ∫ t in x..y, (2.103 / L) * (t ^ (-(3 : ℝ) / 2) / 20 + 4 * t ^ (-(2 : ℝ))) := by
    apply intervalIntegral.integral_mono_on hxy hint1 (hcont.intervalIntegrable_of_Icc hxy)
    intro t ht
    exact (le_abs_self _).trans (E1_wM'_le hB hL (by linarith [ht.1]) (hlog t ht.1))
  have h4 : ∫ t in x..y, (2.103 / L) * (t ^ (-(3 : ℝ) / 2) / 20 + 4 * t ^ (-(2 : ℝ)))
      ≤ (2.103 / L) * (x ^ (-(1 : ℝ) / 2) / 10 + 4 * x ^ (-(1 : ℝ))) := by
    have hy0 : 0 < y := by linarith
    have h0 : (0 : ℝ) ∉ uIcc x y := by
      rw [uIcc_of_le hxy]; intro h; linarith [h.1]
    have i1 : IntervalIntegrable (fun t : ℝ => t ^ (-(3 : ℝ) / 2)) volume x y :=
      intervalIntegral.intervalIntegrable_rpow (Or.inr h0)
    have i2 : IntervalIntegrable (fun t : ℝ => t ^ (-(2 : ℝ))) volume x y :=
      intervalIntegral.intervalIntegrable_rpow (Or.inr h0)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (i1.div_const _)
      (i2.const_mul _), intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inr ⟨by norm_num, h0⟩), integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hy1 : 0 ≤ y ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hy0.le _
    have hy2 : 0 ≤ y ^ (-(1 : ℝ)) := Real.rpow_nonneg hy0.le _
    have ex1 : (-(3 : ℝ) / 2 + 1) = -(1 : ℝ) / 2 := by norm_num
    have ex2 : (-(2 : ℝ) + 1) = -(1 : ℝ) := by norm_num
    rw [ex1, ex2]
    have : (y ^ (-(1 : ℝ) / 2) - x ^ (-(1 : ℝ) / 2)) / (-(1 : ℝ) / 2) / 20
        = (x ^ (-(1 : ℝ) / 2) - y ^ (-(1 : ℝ) / 2)) / 10 := by ring
    rw [this]
    have : 4 * ((y ^ (-(1 : ℝ)) - x ^ (-(1 : ℝ))) / (-(1 : ℝ)))
        = 4 * (x ^ (-(1 : ℝ)) - y ^ (-(1 : ℝ))) := by ring
    rw [this]
    linarith
  linarith

lemma exp30_ge {x : ℝ} (hx : Real.exp 30 ≤ x) : 31 ≤ x ∧ 0 < x ∧ 30 ≤ Real.log x := by
  have he30 : (31 : ℝ) ≤ Real.exp 30 := by
    have := Real.add_one_le_exp (30 : ℝ); linarith
  refine ⟨by linarith, by linarith, ?_⟩
  rw [← Real.log_exp 30]; exact Real.log_le_log (Real.exp_pos _) hx

lemma exp10_ge : (1000 : ℝ) ≤ Real.exp 10 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have : (2.7 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 := by gcongr; linarith
  linarith [show (1000 : ℝ) ≤ 2.7 ^ 10 by norm_num]

/-- `t^{1/k} ≥ 1000` for `t ≥ e^{30}`, `k ∈ {2, 3}`. -/
lemma root_ge_1000 {t a : ℝ} (ht : Real.exp 30 ≤ t) (ha : 0 < a) (ha3 : a ≤ 3) :
    1000 ≤ t ^ (a⁻¹) := by
  have h1 : (Real.exp 30) ^ (a⁻¹) ≤ t ^ (a⁻¹) :=
    Real.rpow_le_rpow (Real.exp_pos _).le ht (by positivity)
  rw [← Real.exp_mul] at h1
  have h2 : Real.exp 10 ≤ Real.exp (30 * a⁻¹) := by
    apply Real.exp_le_exp.mpr
    rw [show (30 : ℝ) * a⁻¹ = 30 / a by ring, le_div_iff₀ ha]; linarith
  linarith [exp10_ge]

/-- `ψ − θ ≤ t^{1/2} + t^{3/8} + t^{1/3} + t^{1/4} + 5.39 t^{1/5}` for `t ≥ e^{30}`. -/
lemma psi_sub_theta_le (hB : Psi1NatBound) {t : ℝ} (ht : Real.exp 30 ≤ t) :
    ψ t - θ t ≤ t ^ ((1 : ℝ) / 2) + t ^ ((3 : ℝ) / 8) + t ^ ((1 : ℝ) / 3) + t ^ ((1 : ℝ) / 4)
      + 5.39 * t ^ ((1 : ℝ) / 5) := by
  obtain ⟨-, ht0, -⟩ := exp30_ge ht
  have h := psi_sub_theta_le_psi_add_psi_add_psi t
  have h2 := psi_upper hB (root_ge_1000 ht (a := 2) (by norm_num) (by norm_num))
  have h3 := psi_upper hB (root_ge_1000 ht (a := 3) (by norm_num) (by norm_num))
  have h5 := psi_le_const_mul_self (Real.rpow_nonneg ht0.le ((5 : ℝ)⁻¹))
  have e2 : (t ^ (2 : ℝ)⁻¹) ^ ((3 : ℝ) / 4) = t ^ ((3 : ℝ) / 8) := by
    rw [← Real.rpow_mul ht0.le]; norm_num
  have e3 : (t ^ (3 : ℝ)⁻¹) ^ ((3 : ℝ) / 4) = t ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_mul ht0.le]; norm_num
  rw [e2] at h2
  rw [e3] at h3
  have hlog4 : Real.log 4 + 4 ≤ 5.39 := by
    have := Real.log_two_lt_d9
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have h5' : (Real.log 4 + 4) * t ^ (5 : ℝ)⁻¹ ≤ 5.39 * t ^ (5 : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_right hlog4 (Real.rpow_nonneg ht0.le _)
  simp only [one_div] at *
  linarith

/-- The dominating function for `(ψ − θ) w` on `(x, ∞)`. -/
noncomputable def hDom (L t : ℝ) : ℝ :=
  (31 / 30) / L * (t ^ (-(3 : ℝ) / 2) + t ^ (-(13 : ℝ) / 8) + t ^ (-(5 : ℝ) / 3)
    + t ^ (-(7 : ℝ) / 4) + 5.39 * t ^ (-(9 : ℝ) / 5))

lemma integrableOn_hDom (L : ℝ) {x : ℝ} (hx : 0 < x) : IntegrableOn (hDom L) (Ioi x) := by
  unfold hDom
  refine Integrable.const_mul ?_ _
  refine ((((integrableOn_Ioi_rpow_of_lt (by norm_num) hx).add
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hx)).add
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hx)).add
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hx)).add
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hx).const_mul _)

lemma integral_hDom (L : ℝ) {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi x, hDom L t = (31 / 30) / L * (2 * x ^ (-(1 : ℝ) / 2)
      + 8 / 5 * x ^ (-(5 : ℝ) / 8) + 3 / 2 * x ^ (-(2 : ℝ) / 3) + 4 / 3 * x ^ (-(3 : ℝ) / 4)
      + 5.39 * (5 / 4) * x ^ (-(4 : ℝ) / 5)) := by
  unfold hDom
  have i := fun (a : ℝ) (ha : a < -1) => integrableOn_Ioi_rpow_of_lt ha hx
  rw [integral_const_mul, integral_add, integral_add, integral_add, integral_add,
    integral_const_mul]
  · rw [integral_Ioi_rpow_of_lt (by norm_num) hx, integral_Ioi_rpow_of_lt (by norm_num) hx,
      integral_Ioi_rpow_of_lt (by norm_num) hx, integral_Ioi_rpow_of_lt (by norm_num) hx,
      integral_Ioi_rpow_of_lt (by norm_num) hx]
    congr 1
    norm_num
    ring
  all_goals first
    | exact i _ (by norm_num)
    | exact (i _ (by norm_num)).const_mul _
    | exact (i _ (by norm_num)).add (i _ (by norm_num))
    | exact ((i _ (by norm_num)).add (i _ (by norm_num))).add (i _ (by norm_num))
    | exact (((i _ (by norm_num)).add (i _ (by norm_num))).add (i _ (by norm_num))).add
        (i _ (by norm_num))

lemma psi_sub_theta_wM_le (hB : Psi1NatBound) {x t : ℝ} (hx : Real.exp 30 ≤ x) (ht : x ≤ t) :
    (ψ t - θ t) * wM t ≤ hDom (Real.log x) t := by
  obtain ⟨-, hx0, hL⟩ := exp30_ge hx
  have ht' : Real.exp 30 ≤ t := hx.trans ht
  have ht0 : 0 < t := by linarith
  have hw := wM_le_of_log hL ht0 (Real.log_le_log hx0 ht)
  have hw0 : 0 < wM t := wM_pos (by linarith [(exp30_ge ht').1])
  have hd := psi_sub_theta_le hB ht'
  have hnn : 0 ≤ ψ t - θ t := sub_nonneg.mpr (theta_le_psi t)
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  calc (ψ t - θ t) * wM t
      ≤ (t ^ ((1 : ℝ) / 2) + t ^ ((3 : ℝ) / 8) + t ^ ((1 : ℝ) / 3) + t ^ ((1 : ℝ) / 4)
          + 5.39 * t ^ ((1 : ℝ) / 5)) * ((31 / 30) / (L * t ^ 2)) :=
        mul_le_mul hd hw hw0.le (by positivity)
    _ = hDom L t := by
        unfold hDom
        have e : ∀ a : ℝ, t ^ a / t ^ 2 = t ^ (a - 2) := fun a => by
          rw [Real.rpow_sub ht0, Real.rpow_two]
        have e1 : t ^ ((1 : ℝ) / 2) / t ^ 2 = t ^ (-(3 : ℝ) / 2) := by rw [e]; norm_num
        have e2 : t ^ ((3 : ℝ) / 8) / t ^ 2 = t ^ (-(13 : ℝ) / 8) := by rw [e]; norm_num
        have e3 : t ^ ((1 : ℝ) / 3) / t ^ 2 = t ^ (-(5 : ℝ) / 3) := by rw [e]; norm_num
        have e4 : t ^ ((1 : ℝ) / 4) / t ^ 2 = t ^ (-(7 : ℝ) / 4) := by rw [e]; norm_num
        have e5 : t ^ ((1 : ℝ) / 5) / t ^ 2 = t ^ (-(9 : ℝ) / 5) := by rw [e]; norm_num
        rw [← e1, ← e2, ← e3, ← e4, ← e5]
        field_simp

/-- `∫_x^∞ (ψ − θ) w ≤ ∫_x^∞ hDom`. -/
lemma integral_psi_sub_theta_le (hB : Psi1NatBound) {x : ℝ} (hx : Real.exp 30 ≤ x) :
    IntegrableOn (fun t => (ψ t - θ t) * wM t) (Ioi x) ∧
    ∫ t in Ioi x, (ψ t - θ t) * wM t ≤ ∫ t in Ioi x, hDom (Real.log x) t := by
  obtain ⟨hx31, hx0, hL⟩ := exp30_ge hx
  have hmeas : AEStronglyMeasurable (fun t => (ψ t - θ t) * wM t) (volume.restrict (Ioi x)) :=
    ((psi_mono.measurable.sub theta_mono.measurable).mul measurable_wM).aestronglyMeasurable
  have hnn : ∀ t ∈ Ioi x, 0 ≤ (ψ t - θ t) * wM t := fun t ht =>
    mul_nonneg (sub_nonneg.mpr (theta_le_psi t)) (wM_pos (by linarith [ht.out])).le
  have hint : IntegrableOn (fun t => (ψ t - θ t) * wM t) (Ioi x) := by
    refine Integrable.mono' (integrableOn_hDom (Real.log x) hx0) hmeas ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn t ht)]
    exact psi_sub_theta_wM_le hB hx (le_of_lt ht)
  refine ⟨hint, setIntegral_mono_on hint (integrableOn_hDom _ hx0) measurableSet_Ioi ?_⟩
  intro t ht
  exact psi_sub_theta_wM_le hB hx (le_of_lt ht)

lemma integrableOn_sub_psi_wM (hB : Psi1NatBound) {x : ℝ} (hx : Real.exp 30 ≤ x) :
    IntegrableOn (fun t => (t - ψ t) * wM t) (Ioi x) := by
  obtain ⟨hx31, hx0, -⟩ := exp30_ge hx
  have hmeas : AEStronglyMeasurable (fun t => (t - ψ t) * wM t) (volume.restrict (Ioi x)) :=
    ((measurable_id.sub psi_mono.measurable).mul measurable_wM).aestronglyMeasurable
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (show -(5 : ℝ) / 4 < -1 by norm_num)
    hx0).const_mul 4) hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun t ht => ?_
  have ht : x < t := ht
  have ht0 : 0 < t := by linarith
  have h1000 : (1000 : ℝ) ≤ t := by
    have : (1000 : ℝ) ≤ Real.exp 30 := le_trans exp10_ge (Real.exp_le_exp.mpr (by norm_num))
    linarith
  have hu := psi_upper hB h1000
  have hl := psi_lower hB h1000
  have hw0 : 0 < wM t := wM_pos (by linarith)
  have hw := wM_le (show (2 : ℝ) ≤ t by linarith)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hw0]
  have habs : |t - ψ t| ≤ t ^ ((3 : ℝ) / 4) := abs_le.mpr ⟨by linarith, by linarith⟩
  calc |t - ψ t| * wM t ≤ t ^ ((3 : ℝ) / 4) * (4 / t ^ 2) :=
        mul_le_mul habs hw hw0.le (by positivity)
    _ = 4 * t ^ (-(5 : ℝ) / 4) := by
        have : t ^ (-(5 : ℝ) / 4) = t ^ ((3 : ℝ) / 4) / t ^ 2 := by
          rw [← Real.rpow_two, ← Real.rpow_sub ht0]; norm_num
        rw [this]; ring

theorem tail_bound (hB : Psi1NatBound) {x : ℝ} (hx : Real.exp 30 ≤ x) :
    -∫ t in Set.Ioi x, (θ t - t) * wM t ≤
      (2.4 + 3.3 * x ^ (-(1 : ℝ) / 8) + 26 * x ^ (-(1 : ℝ) / 4)) / (√x * Real.log x) := by
  obtain ⟨hx31, hx0, hL⟩ := exp30_ge hx
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hI1 := integrableOn_sub_psi_wM hB hx
  obtain ⟨hI2, hJ2⟩ := integral_psi_sub_theta_le hB hx
  have hsplit : -∫ t in Ioi x, (θ t - t) * wM t
      = (∫ t in Ioi x, (t - ψ t) * wM t) + ∫ t in Ioi x, (ψ t - θ t) * wM t := by
    rw [← integral_add hI1 hI2, ← integral_neg]
    congr 1; ext t; ring
  set B1 := 2 * ((31 / 30) * Abd x / L) + (2.103 / L) * (x ^ (-(1 : ℝ) / 2) / 10
    + 4 * x ^ (-(1 : ℝ)))
  have hJ1 : ∫ t in Ioi x, (t - ψ t) * wM t ≤ B1 := by
    have ht := intervalIntegral_tendsto_integral_Ioi x hI1 tendsto_id
    refine le_of_tendsto ht ?_
    rw [Filter.eventually_atTop]
    exact ⟨x, fun y hy => integral_sub_psi_wM_le hB hx hy⟩
  rw [integral_hDom L hx0] at hJ2
  rw [hsplit]
  set r := x ^ (-(1 : ℝ) / 8) with hr
  set s := x ^ (-(1 : ℝ) / 2) with hs
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hsx : 1 / √x = s := by
    rw [hs, Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hx0.le]; norm_num
  have hr0 : 0 ≤ r := Real.rpow_nonneg hx0.le _
  have hs0 : 0 ≤ s := Real.rpow_nonneg hx0.le _
  have pw : ∀ a b : ℝ, x ^ (a + b) = x ^ a * x ^ b := fun a b => Real.rpow_add hx0 a b
  have mono : ∀ a b : ℝ, a ≤ b → x ^ a ≤ x ^ b := fun a b h =>
    Real.rpow_le_rpow_of_exponent_le hx1 h
  have hr2 : x ^ (-(1 : ℝ) / 4) = r ^ 2 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have e58 : x ^ (-(5 : ℝ) / 8) = s * r := by rw [hs, hr, ← pw]; norm_num
  have e23 : x ^ (-(2 : ℝ) / 3) ≤ s * r := by
    rw [hs, hr, ← pw]; exact mono _ _ (by norm_num)
  have e34 : x ^ (-(3 : ℝ) / 4) = s * r ^ 2 := by
    rw [← hr2, hs, ← pw]; norm_num
  have e45 : x ^ (-(4 : ℝ) / 5) ≤ s * r ^ 2 := by
    rw [← hr2, hs, ← pw]; exact mono _ _ (by norm_num)
  have e1 : x ^ (-(1 : ℝ)) ≤ s * r ^ 2 := by
    rw [← hr2, hs, ← pw]; exact mono _ _ (by norm_num)
  have hAbd : Abd x = s / 20 + 4 * x ^ (-(1 : ℝ)) := rfl
  rw [e58, e34] at hJ2
  have key : 2 * ((31 / 30) * (s / 20 + 4 * x ^ (-(1 : ℝ)))) + 2.103 * (s / 10
      + 4 * x ^ (-(1 : ℝ))) + (31 / 30) * (2 * s + 8 / 5 * (s * r)
      + 3 / 2 * x ^ (-(2 : ℝ) / 3) + 4 / 3 * (s * r ^ 2) + 5.39 * (5 / 4) * x ^ (-(4 : ℝ) / 5))
      ≤ (2.4 + 3.3 * r + 26 * r ^ 2) * s := by
    nlinarith [mul_nonneg hs0 hr0, mul_nonneg hs0 (sq_nonneg r)]
  have hsum : B1 + (31 / 30) / L * (2 * s + 8 / 5 * (s * r) + 3 / 2 * x ^ (-(2 : ℝ) / 3)
      + 4 / 3 * (s * r ^ 2) + 5.39 * (5 / 4) * x ^ (-(4 : ℝ) / 5))
      = (2 * ((31 / 30) * (s / 20 + 4 * x ^ (-(1 : ℝ)))) + 2.103 * (s / 10
      + 4 * x ^ (-(1 : ℝ))) + (31 / 30) * (2 * s + 8 / 5 * (s * r)
      + 3 / 2 * x ^ (-(2 : ℝ) / 3) + 4 / 3 * (s * r ^ 2) + 5.39 * (5 / 4) * x ^ (-(4 : ℝ) / 5)))
        / L := by
    simp only [B1, hAbd]; rw [← hs]; field_simp
  have hfin : (2.4 + 3.3 * r + 26 * r ^ 2) * s / L
      = (2.4 + 3.3 * r + 26 * r ^ 2) / (√x * L) := by
    rw [← hsx]; field_simp
  have hdiv := div_le_div_of_nonneg_right key hL0.le
  rw [hr2]
  linarith

end Robin
