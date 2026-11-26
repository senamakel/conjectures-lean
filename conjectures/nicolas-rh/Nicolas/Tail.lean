import Robin.Main.Tail

/-!
# A lower bound for `J(x) = ∫_x^∞ (t − θ(t)) w(t) dt` for `x ≥ 10^5`

`t − θ = (t − ψ) + (ψ − θ)`, as in robin-rh's `Robin/Main/Tail.lean`, but with the inequalities
reversed and constants for `log x ≥ 11` instead of `log x ≥ 30`:

* `∫_x^∞ (t − ψ) w ≥ −(2·(12/11)·A(x) + 2.29·(x^{−1/2}/10 + 4/x))/log x` by parts against
  `E = Ψ₁ − t²/2` (`|E(t)| ≤ t^{3/2}/20 + 4t` under RH, robin-rh's `E1_le_Abd`);
* `ψ(t) − θ(t) ≥ ψ(√t) ≥ 0.68 √t` (Mathlib's Costa Pereira lower bound and
  `psi_ge_of_seven_le`, both unconditional), and `∫_x^∞ √t w ≥ (12/13) · 2/(√x log x)`
  (comparison with `−d/dt (2/(√t log t))`).

Together: `J(x) ≥ 0.86/(√x log x)` (`tail_lower`).
-/

namespace Nicolas

open Filter Topology Real Chebyshev MeasureTheory Set Robin

/-- `w(t) ≤ (12/11)/(L t²)` when `log t ≥ L ≥ 11`. -/
lemma wM_le_of_log' {t L : ℝ} (hL : 11 ≤ L) (ht0 : 0 < t) (ht : L ≤ Real.log t) :
    wM t ≤ (12 / 11) / (L * t ^ 2) := by
  have hl : 0 < Real.log t := by linarith
  have hL0 : 0 < L := by linarith
  unfold wM
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : L * (1 + Real.log t) ≤ (12 / 11) * Real.log t ^ 2 := by nlinarith
  have ht2 : 0 < t ^ 2 := by positivity
  calc (1 + Real.log t) * (L * t ^ 2) = t ^ 2 * (L * (1 + Real.log t)) := by ring
    _ ≤ t ^ 2 * ((12 / 11) * Real.log t ^ 2) := mul_le_mul_of_nonneg_left h1 ht2.le
    _ = 12 / 11 * (t ^ 2 * Real.log t ^ 2) := by ring

lemma abs_wM'_le' {t L : ℝ} (hL : 11 ≤ L) (ht0 : 0 < t) (ht : L ≤ Real.log t) :
    |wM' t| ≤ 2.29 / (L * t ^ 3) := by
  have hl : 0 < Real.log t := by linarith
  have hL0 : 0 < L := by linarith
  unfold wM'
  rw [abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  set l := Real.log t
  have h1 : L * (2 * l ^ 2 + 3 * l + 2) ≤ 2.29 * l ^ 3 := by
    have : L * (2 * l ^ 2 + 3 * l + 2) ≤ l * (2 * l ^ 2 + 3 * l + 2) :=
      mul_le_mul_of_nonneg_right ht (by positivity)
    nlinarith
  have ht3 : 0 < t ^ 3 := by positivity
  calc (2 * l ^ 2 + 3 * l + 2) * (L * t ^ 3) = t ^ 3 * (L * (2 * l ^ 2 + 3 * l + 2)) := by ring
    _ ≤ t ^ 3 * (2.29 * l ^ 3) := mul_le_mul_of_nonneg_left h1 ht3.le
    _ = 2.29 * (t ^ 3 * l ^ 3) := by ring

lemma E1_wM_le' (hB : Psi1NatBound) {t L : ℝ} (hL : 11 ≤ L) (ht16 : 16 ≤ t)
    (ht : L ≤ Real.log t) : |E1 t * wM t| ≤ (12 / 11) * Abd t / L := by
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := by linarith
  have hw0 : 0 < wM t := wM_pos (by linarith)
  rw [abs_mul, abs_of_pos hw0]
  calc |E1 t| * wM t ≤ (t ^ 2 * Abd t) * ((12 / 11) / (L * t ^ 2)) :=
        mul_le_mul (E1_le_Abd hB ht16) (wM_le_of_log' hL ht0 ht) hw0.le
          (by have := Abd_nonneg ht0; positivity)
    _ = (12 / 11) * Abd t / L := by field_simp

lemma E1_wM'_le' (hB : Psi1NatBound) {t L : ℝ} (hL : 11 ≤ L) (ht16 : 16 ≤ t)
    (ht : L ≤ Real.log t) :
    |E1 t * wM' t| ≤ (2.29 / L) * (t ^ (-(3 : ℝ) / 2) / 20 + 4 * t ^ (-(2 : ℝ))) := by
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := by linarith
  rw [abs_mul]
  have e : t ^ 2 * Abd t * (2.29 / (L * t ^ 3))
      = (2.29 / L) * (t ^ (-(3 : ℝ) / 2) / 20 + 4 * t ^ (-(2 : ℝ))) := by
    unfold Abd
    have e1 : t ^ (-(3 : ℝ) / 2) = t ^ (-(1 : ℝ) / 2) * t⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ht0]; norm_num
    have e2 : t ^ (-(2 : ℝ)) = t ^ (-(1 : ℝ)) * t⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ht0]; norm_num
    rw [e1, e2]; field_simp
  rw [← e]
  exact mul_le_mul (E1_le_Abd hB ht16) (abs_wM'_le' hL ht0 ht) (abs_nonneg _)
    (by have := Abd_nonneg ht0; positivity)

/-- The interval lower bound for the `t − ψ` part. -/
lemma integral_sub_psi_wM_ge (hB : Psi1NatBound) {x y : ℝ} (hx16 : 16 ≤ x)
    (hL : 11 ≤ Real.log x) (hxy : x ≤ y) :
    -(2 * ((12 / 11) * Abd x / Real.log x)
        + (2.29 / Real.log x) * (x ^ (-(1 : ℝ) / 2) / 10 + 4 * x ^ (-(1 : ℝ))))
      ≤ ∫ t in x..y, (t - ψ t) * wM t := by
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hlog : ∀ t, x ≤ t → L ≤ Real.log t := fun t ht => Real.log_le_log hx0 ht
  rw [integral_sub_psi_wM (by linarith) hxy]
  have h1 : -((12 / 11) * Abd x / L) ≤ E1 x * wM x :=
    (neg_le_neg (E1_wM_le' hB hL hx16 le_rfl)).trans (neg_abs_le _)
  have h2 : -((12 / 11) * Abd x / L) ≤ -(E1 y * wM y) := by
    have := (E1_wM_le' hB hL (by linarith) (hlog y hxy)).trans' (le_abs_self (E1 y * wM y))
    have hA := Abd_anti hx0 hxy
    have : (12 / 11) * Abd y / L ≤ (12 / 11) * Abd x / L := by
      apply div_le_div_of_nonneg_right _ hL0.le; linarith
    linarith
  have hcont : ContinuousOn (fun t => (2.29 / L) * (t ^ (-(3 : ℝ) / 2) / 20 + 4 * t ^ (-(2 : ℝ))))
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
  have h3 : ∫ t in x..y, -((2.29 / L) * (t ^ (-(3 : ℝ) / 2) / 20 + 4 * t ^ (-(2 : ℝ))))
      ≤ ∫ t in x..y, E1 t * wM' t := by
    apply intervalIntegral.integral_mono_on hxy (hcont.neg.intervalIntegrable_of_Icc hxy) hint1
    intro t ht
    exact (neg_le_neg (E1_wM'_le' hB hL (by linarith [ht.1]) (hlog t ht.1))).trans (neg_abs_le _)
  have h4 : ∫ t in x..y, (2.29 / L) * (t ^ (-(3 : ℝ) / 2) / 20 + 4 * t ^ (-(2 : ℝ)))
      ≤ (2.29 / L) * (x ^ (-(1 : ℝ) / 2) / 10 + 4 * x ^ (-(1 : ℝ))) := by
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
  rw [intervalIntegral.integral_neg] at h3
  linarith

/-- `(t − ψ) w` is integrable on `(x, ∞)` for `x ≥ 1000` (RH: `|ψ(t) − t| ≤ t^{3/4}`). -/
lemma integrableOn_sub_psi_wM' (hB : Psi1NatBound) {x : ℝ} (hx : 1000 ≤ x) :
    IntegrableOn (fun t => (t - ψ t) * wM t) (Ioi x) := by
  have hx0 : 0 < x := by linarith
  have hmeas : AEStronglyMeasurable (fun t => (t - ψ t) * wM t) (volume.restrict (Ioi x)) :=
    ((measurable_id.sub psi_mono.measurable).mul measurable_wM).aestronglyMeasurable
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (show -(5 : ℝ) / 4 < -1 by norm_num)
    hx0).const_mul 4) hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun t ht => ?_
  have ht : x < t := ht
  have ht0 : 0 < t := by linarith
  have h1000 : (1000 : ℝ) ≤ t := by linarith
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

/-- `ψ(s) ≥ 0.68 s` for `s ≥ 100` (unconditional, from `ψ(n) ≥ n log 2`). -/
lemma psi_ge_068 {s : ℝ} (hs : 100 ≤ s) : 0.68 * s ≤ ψ s := by
  have hn : 7 ≤ ⌊s⌋₊ := Nat.le_floor (by norm_num; linarith)
  have h := psi_ge_of_seven_le hn
  rw [← psi_eq_psi_coe_floor] at h
  have hfl : s - 1 ≤ (⌊s⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one s]
  have hl2 := Real.log_two_gt_d9
  nlinarith

/-- `g(t) = 2/(√t log t)` and `G = −g'`. -/
noncomputable def gN (t : ℝ) : ℝ := -(2 * t ^ (-(1 : ℝ) / 2) / Real.log t)

noncomputable def GN (t : ℝ) : ℝ := t ^ (-(3 : ℝ) / 2) * (Real.log t + 2) / Real.log t ^ 2

lemma hasDerivAt_gN {t : ℝ} (ht : 1 < t) : HasDerivAt gN (GN t) t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  have h1 : HasDerivAt (fun u : ℝ => u ^ (-(1 : ℝ) / 2)) ((-(1 : ℝ) / 2) * t ^ (-(1 : ℝ) / 2 - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht0.ne')
  have h2 := ((h1.const_mul 2).div (Real.hasDerivAt_log ht0.ne') hl.ne').neg
  unfold gN
  convert h2 using 1
  unfold GN
  have e : t ^ (-(1 : ℝ) / 2 - 1) = t ^ (-(3 : ℝ) / 2) := by norm_num
  have e2 : t ^ (-(1 : ℝ) / 2) = t ^ (-(3 : ℝ) / 2) * t := by
    rw [← Real.rpow_add_one ht0.ne']; norm_num
  rw [e, e2]
  field_simp
  ring

lemma tendsto_gN : Tendsto gN atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
    refine this.congr fun t => ?_
    congr 1; ring
  have h2 : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  have h := ((h1.const_mul 2).mul h2).neg
  simp only [mul_zero, neg_zero] at h
  refine h.congr fun t => ?_
  unfold gN; ring

lemma GN_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ GN t := by
  have hl : 0 < Real.log t := Real.log_pos ht
  unfold GN; have := Real.rpow_nonneg (show (0 : ℝ) ≤ t by linarith) (-(3 : ℝ) / 2); positivity

lemma integral_GN {x : ℝ} (hx : 1 < x) :
    IntegrableOn GN (Ioi x) ∧ ∫ t in Ioi x, GN t = 2 * x ^ (-(1 : ℝ) / 2) / Real.log x := by
  have hcont : ContinuousWithinAt gN (Ici x) x := (hasDerivAt_gN hx).continuousAt.continuousWithinAt
  have hder : ∀ t ∈ Ioi x, HasDerivAt gN (GN t) t := fun t ht => hasDerivAt_gN (hx.trans ht)
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hder
    (fun t ht => GN_nonneg (hx.trans ht)) tendsto_gN
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hder hint tendsto_gN]
  unfold gN; ring

/-- `(ψ(t) − θ(t)) w(t) ≥ 0.68·(12/13)·G(t)` for `t ≥ x`, `x ≥ 10^4`, `log x ≥ 11`. -/
lemma psi_sub_theta_wM_ge {x t : ℝ} (hx : 10000 ≤ x) (hL : 11 ≤ Real.log x) (ht : x ≤ t) :
    0.68 * (12 / 13) * GN t ≤ (ψ t - θ t) * wM t := by
  have ht0 : 0 < t := by linarith
  have hl : 11 ≤ Real.log t := hL.trans (Real.log_le_log (by linarith) ht)
  have hl0 : 0 < Real.log t := by linarith
  have hsq : 100 ≤ t ^ (2 : ℝ)⁻¹ := by
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      show (100 : ℝ) = √(100 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hψ := psi_ge_068 hsq
  have hCP := psi_sub_theta_ge_psi_add_psi_add_psi ht0.le
  have h3 := psi_nonneg (t ^ (3 : ℝ)⁻¹)
  have h7 := psi_nonneg (t ^ (7 : ℝ)⁻¹)
  have hd : 0.68 * t ^ (2 : ℝ)⁻¹ ≤ ψ t - θ t := by linarith
  have hw0 : 0 < wM t := wM_pos (by linarith)
  have key : 0.68 * (12 / 13) * GN t ≤ 0.68 * t ^ (2 : ℝ)⁻¹ * wM t := by
    unfold GN wM
    have e : t ^ (2 : ℝ)⁻¹ = t ^ (-(3 : ℝ) / 2) * t ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add ht0]; norm_num
    rw [e]
    have hp : 0 < t ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos ht0 _
    rw [show 0.68 * (t ^ (-(3 : ℝ) / 2) * t ^ 2) * ((1 + Real.log t) / (t ^ 2 * Real.log t ^ 2))
        = 0.68 * (t ^ (-(3 : ℝ) / 2) * (1 + Real.log t) / Real.log t ^ 2) by field_simp]
    have : (12 / 13) * (t ^ (-(3 : ℝ) / 2) * (Real.log t + 2) / Real.log t ^ 2)
        ≤ t ^ (-(3 : ℝ) / 2) * (1 + Real.log t) / Real.log t ^ 2 := by
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
      nlinarith
    nlinarith
  exact key.trans (mul_le_mul_of_nonneg_right hd hw0.le)

/-- **Tail lower bound.** Under `Psi1NatBound` (RH), for `x ≥ 10^5`,
`∫_x^∞ (t − θ(t)) w(t) dt ≥ 0.86/(√x log x)`. -/
theorem tail_lower (hB : Psi1NatBound) {x : ℝ} (hx : 100000 ≤ x) (hL : 11 ≤ Real.log x) :
    IntegrableOn (fun t => (θ t - t) * wM t) (Ioi x) ∧
    0.86 / (√x * Real.log x) ≤ -∫ t in Ioi x, (θ t - t) * wM t := by
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  obtain ⟨C, hC⟩ := theta_sub_bound hB
  have hIθ := integrableOn_err hC (show (2 : ℝ) ≤ x by linarith)
  refine ⟨hIθ, ?_⟩
  have hI1 := integrableOn_sub_psi_wM' hB (show (1000 : ℝ) ≤ x by linarith)
  have hI2 : IntegrableOn (fun t => (ψ t - θ t) * wM t) (Ioi x) :=
    (hIθ.neg.sub hI1).congr_fun (fun t _ => by simp only [Pi.neg_apply, Pi.sub_apply]; ring)
      measurableSet_Ioi
  have hsplit : -∫ t in Ioi x, (θ t - t) * wM t
      = (∫ t in Ioi x, (t - ψ t) * wM t) + ∫ t in Ioi x, (ψ t - θ t) * wM t := by
    rw [← integral_add hI1 hI2, ← integral_neg]
    congr 1; ext t; ring
  set B1 := 2 * ((12 / 11) * Abd x / L) + (2.29 / L) * (x ^ (-(1 : ℝ) / 2) / 10
    + 4 * x ^ (-(1 : ℝ)))
  have hJ1 : -B1 ≤ ∫ t in Ioi x, (t - ψ t) * wM t := by
    have ht := intervalIntegral_tendsto_integral_Ioi x hI1 tendsto_id
    refine ge_of_tendsto ht ?_
    rw [Filter.eventually_atTop]
    exact ⟨x, fun y hy => integral_sub_psi_wM_ge hB (by linarith) hL hy⟩
  obtain ⟨hIG, hG⟩ := integral_GN (show 1 < x by linarith)
  have hJ2 : 0.68 * (12 / 13) * (2 * x ^ (-(1 : ℝ) / 2) / L)
      ≤ ∫ t in Ioi x, (ψ t - θ t) * wM t := by
    rw [← hG, ← integral_const_mul]
    exact setIntegral_mono_on (hIG.const_mul _) hI2 measurableSet_Ioi
      fun t ht => psi_sub_theta_wM_ge (by linarith) hL (le_of_lt ht)
  rw [hsplit]
  set s := x ^ (-(1 : ℝ) / 2) with hs
  have hsx : 1 / √x = s := by
    rw [hs, Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hx0.le]; norm_num
  have hs0 : 0 ≤ s := Real.rpow_nonneg hx0.le _
  have h316 : (316 : ℝ) ≤ √x := by
    rw [show (316 : ℝ) = √(316 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs1 : s ≤ 1 / 316 := by
    rw [← hsx]
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hx0) (by norm_num)]
    linarith
  have hx1 : x ^ (-(1 : ℝ)) = s ^ 2 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hAbd : Abd x = s / 20 + 4 * s ^ 2 := by rw [← hx1]; rfl
  have key : 0.86 * s ≤ -(2 * ((12 / 11) * (s / 20 + 4 * s ^ 2)) + 2.29 * (s / 10 + 4 * s ^ 2))
      + 0.68 * (12 / 13) * (2 * s) := by
    nlinarith [mul_nonneg hs0 hs0]
  have hsum : -B1 + 0.68 * (12 / 13) * (2 * s / L)
      = (-(2 * ((12 / 11) * (s / 20 + 4 * s ^ 2)) + 2.29 * (s / 10 + 4 * s ^ 2))
      + 0.68 * (12 / 13) * (2 * s)) / L := by
    simp only [B1, hAbd, hx1, ← hs]; field_simp
  have hfin : 0.86 * s / L = 0.86 / (√x * L) := by
    rw [← hsx]; field_simp
  have hdiv := div_le_div_of_nonneg_right key hL0.le
  linarith

end Nicolas
