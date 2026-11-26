import LLS.Sharp.Principal.Laurent
import Robin.Main.Tail

/-!
# `∫₁^∞ (Ψ₁(t) − t²/2) t^{−3} dt = −γ/2 − 3/4`

For real `s > 1`, `∫₁^∞ Ψ₁(t) t^{−s−2} dt = Σ Λ(n) n^{−s}/(s(s+1))` (Tonelli, termwise:
`∫_n^∞ (t − n) t^{−s−2} dt = n^{−s}/(s(s+1))`), so
`∫₁^∞ E(t) t^{−s−2} dt = L(s)/(s(s+1)) − 1/(2(s−1))` with `E = Ψ₁ − t²/2`, `L = −ζ'/ζ`.
Let `s → 1⁺`: the left side tends to `∫₁^∞ E(t) t^{−3}` by dominated convergence, and the right
side to `−γ/2 − 3/4` by `L(s) − 1/(s−1) → −γ`.
-/

namespace LLS.Sharp.Principal

open Filter Topology Real MeasureTheory Set ArithmeticFunction Robin Chebyshev

lemma rpow_add_one' {c : ℝ} (hc : 0 < c) (a : ℝ) : c ^ (a + 1) = c ^ a * c :=
  Real.rpow_add_one hc.ne' a

/-- `∫_{Ioi c} t^a = c^{a+1}/(−(a+1))` for `a < −1`. -/
lemma integral_Ioi_rpow' {c a : ℝ} (ha : a < -1) (hc : 0 < c) :
    ∫ t in Ioi c, t ^ a = c ^ (a + 1) / (-(a + 1)) := by
  rw [integral_Ioi_rpow_of_lt ha hc, div_neg, neg_div]

lemma integrableOn_Ioi_rpow' {c a : ℝ} (ha : a < -1) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ a) (Ioi c) :=
  integrableOn_Ioi_rpow_of_lt ha hc

/-- The term `(t − n) t^{−s−2}` as a difference of powers. -/
lemma sub_mul_rpow_eq {s n t : ℝ} (ht : 0 < t) :
    (t - n) * t ^ (-s - 2) = t ^ (-s - 1) - n * t ^ (-s - 2) := by
  have : t ^ (-s - 1) = t ^ (-s - 2) * t := by
    rw [← rpow_add_one' ht]; ring_nf
  rw [this]; ring

lemma integrableOn_sub_mul_rpow {s n c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (t - n) * t ^ (-s - 2)) (Ioi c) := by
  refine ((integrableOn_Ioi_rpow' (a := -s - 1) (by linarith) hc).sub
    ((integrableOn_Ioi_rpow' (a := -s - 2) (by linarith) hc).const_mul n)).congr_fun
    (fun t ht => (sub_mul_rpow_eq (lt_trans hc ht)).symm) measurableSet_Ioi

lemma integral_sub_mul_rpow {s n : ℝ} (hs : 0 < s) (hn : 0 < n) :
    ∫ t in Ioi n, (t - n) * t ^ (-s - 2) = n ^ (-s) / (s * (s + 1)) := by
  have e : ∫ t in Ioi n, (t - n) * t ^ (-s - 2)
      = ∫ t in Ioi n, (t ^ (-s - 1) - n * t ^ (-s - 2)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => sub_mul_rpow_eq (lt_trans hn ht)
  rw [e, integral_sub (integrableOn_Ioi_rpow' (by linarith) hn)
    ((integrableOn_Ioi_rpow' (by linarith) hn).const_mul n), integral_const_mul,
    integral_Ioi_rpow' (by linarith) hn, integral_Ioi_rpow' (by linarith) hn]
  have h1 : -s - 1 + 1 = -s := by ring
  have h2 : n ^ (-s - 2 + 1) = n ^ (-s) / n := by
    rw [show -s - 2 + 1 = -s - 1 by ring]
    have : n ^ (-s) = n ^ (-s - 1) * n := by rw [← rpow_add_one' hn]; ring_nf
    rw [this]; field_simp
  rw [show -(-s - 1 + 1) = s by ring, show -(-s - 2 + 1) = s + 1 by ring, h1, h2]
  have hs1 : s + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The `n`-th term of the series for `Ψ₁(t) t^{−s−2}`. -/
noncomputable def mT (s : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (Λ n : ℝ) * (Ici (n : ℝ)).indicator (fun t => (t - n) * t ^ (-s - 2)) t

lemma psi1_mul_rpow_eq_tsum (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    psi1 t * t ^ (-s - 2) = ∑' n, mT s n t := by
  rw [tsum_eq_sum (s := Finset.range (⌊t⌋₊ + 1))]
  · rw [psi1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n hn => ?_
    have : (n : ℝ) ≤ t := (Nat.le_floor_iff ht).mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
    simp [mT, indicator_of_mem (show t ∈ Ici (n : ℝ) from this), mul_assoc]
  · intro n hn
    have : ⌊t⌋₊ < n := by simpa [Nat.lt_succ_iff] using hn
    have : t < n := Nat.lt_of_floor_lt this
    simp [mT, indicator_of_notMem (show t ∉ Ici (n : ℝ) by simpa using this)]

lemma mT_nonneg (s : ℝ) (n : ℕ) (t : ℝ) : 0 ≤ mT s n t := by
  unfold mT
  apply mul_nonneg vonMangoldt_nonneg
  by_cases h : t ∈ Ici (n : ℝ)
  · rw [indicator_of_mem h]
    have h' : (n : ℝ) ≤ t := h
    have : (0 : ℝ) ≤ t := le_trans (Nat.cast_nonneg n) h'
    exact mul_nonneg (by linarith) (by positivity)
  · rw [indicator_of_notMem h]

lemma integrable_mT {s : ℝ} (hs : 0 < s) (n : ℕ) : IntegrableOn (mT s n) (Ioi 1) :=
  ((integrableOn_sub_mul_rpow (n := (n : ℝ)) hs one_pos).indicator measurableSet_Ici).const_mul _

lemma integral_mT {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∫ t in Ioi 1, mT s n t = (Λ n : ℝ) * (n : ℝ) ^ (-s) / (s * (s + 1)) := by
  unfold mT
  rw [integral_const_mul, setIntegral_indicator measurableSet_Ici]
  by_cases h0 : (Λ n : ℝ) = 0
  · simp [h0]
  have hpp : IsPrimePow n := by
    by_contra h; exact h0 (by simp [vonMangoldt_apply, h])
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hpp.two_le
  have hsub : Ioi (1 : ℝ) ∩ Ici (n : ℝ) = Ici (n : ℝ) :=
    inter_eq_right.mpr (fun x hx => lt_of_lt_of_le (show (1:ℝ) < n by linarith) (mem_Ici.mp hx))
  rw [hsub, integral_Ici_eq_integral_Ioi, integral_sub_mul_rpow hs (by linarith), mul_div_assoc]

/-- **Mellin transform of `Ψ₁`.** -/
theorem mellin_psi1 {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t => psi1 t * t ^ (-s - 2)) (Ioi 1) ∧
    ∫ t in Ioi 1, psi1 t * t ^ (-s - 2) = Lr s / (s * (s + 1)) := by
  have hs0 : 0 < s := by linarith
  have hnorm : ∀ n, ∫ t in Ioi 1, ‖mT s n t‖ = (Λ n : ℝ) * (n : ℝ) ^ (-s) / (s * (s + 1)) := by
    intro n
    rw [← integral_mT hs0 n]
    exact integral_congr_ae (Eventually.of_forall fun t => Real.norm_of_nonneg (mT_nonneg s n t))
  have hsum : Summable fun n => ∫ t in Ioi 1, ‖mT s n t‖ := by
    simp_rw [hnorm]
    exact (summable_Lr hs).div_const _
  have hHas := hasSum_integral_of_summable_integral_norm (integrable_mT hs0) hsum
  have heq : ∫ t in Ioi 1, psi1 t * t ^ (-s - 2) = ∫ t in Ioi 1, ∑' n, mT s n t :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht =>
      psi1_mul_rpow_eq_tsum s (le_of_lt (lt_trans zero_lt_one ht))
  have hval : ∫ t in Ioi 1, ∑' n, mT s n t = Lr s / (s * (s + 1)) := by
    rw [← hHas.tsum_eq]
    simp_rw [integral_mT hs0]
    rw [tsum_div_const, Lr]
  have hpos : 0 < Lr s := by
    refine (summable_Lr hs).tsum_pos
      (fun n => mul_nonneg vonMangoldt_nonneg (by positivity)) 2 ?_
    have : 0 < (Λ 2 : ℝ) := by
      rw [vonMangoldt_apply_prime Nat.prime_two]; exact Real.log_pos (by norm_num)
    positivity
  refine ⟨?_, by rw [heq, hval]⟩
  have hint : IntegrableOn (fun t => ∑' n, mT s n t) (Ioi 1) := by
    apply Integrable.of_integral_ne_zero
    rw [hval]; positivity
  refine hint.congr_fun (fun t ht => ?_) measurableSet_Ioi
  exact (psi1_mul_rpow_eq_tsum s (le_of_lt (lt_trans zero_lt_one ht))).symm

lemma sq_mul_rpow {t s : ℝ} (ht : 0 < t) : t ^ 2 * t ^ (-s - 2) = t ^ (-s) := by
  rw [← rpow_natCast, ← rpow_add ht]; norm_num

/-- **Mellin transform of `E = Ψ₁ − t²/2`.** -/
theorem mellin_E1 {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t => E1 t * t ^ (-s - 2)) (Ioi 1) ∧
    ∫ t in Ioi 1, E1 t * t ^ (-s - 2) = Lr s / (s * (s + 1)) - 1 / (2 * (s - 1)) := by
  obtain ⟨h1, h2⟩ := mellin_psi1 hs
  have h3 : IntegrableOn (fun t : ℝ => t ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have e : ∀ t ∈ Ioi (1 : ℝ), E1 t * t ^ (-s - 2) = psi1 t * t ^ (-s - 2) - 1 / 2 * t ^ (-s) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    rw [E1, sub_mul, ← sq_mul_rpow ht0]; ring
  refine ⟨(h1.sub (h3.const_mul _)).congr_fun (fun t ht => (e t ht).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_sub h1 (h3.const_mul _),
    integral_const_mul, h2, Robin.integral_Ioi_one_rpow_neg hs]
  have : s - 1 ≠ 0 := by linarith
  field_simp

/-- The bound function `q(u) = u^{−3/2}/20 + 4u^{−2}`. -/
noncomputable def qB (u : ℝ) : ℝ := u ^ (-(3 : ℝ) / 2) / 20 + 4 * u ^ (-(2 : ℝ))

lemma integrableOn_qB {x : ℝ} (hx : 0 < x) : IntegrableOn qB (Ioi x) :=
  ((integrableOn_Ioi_rpow' (by norm_num) hx).div_const _).add
    ((integrableOn_Ioi_rpow' (by norm_num) hx).const_mul _)

lemma integral_qB {x : ℝ} (hx : 0 < x) :
    ∫ u in Ioi x, qB u = x ^ (-(1 : ℝ) / 2) / 10 + 4 * x ^ (-(1 : ℝ)) := by
  unfold qB
  rw [integral_add ((integrableOn_Ioi_rpow' (by norm_num) hx).div_const _)
    ((integrableOn_Ioi_rpow' (by norm_num) hx).const_mul _), integral_div, integral_const_mul,
    integral_Ioi_rpow' (by norm_num) hx, integral_Ioi_rpow' (by norm_num) hx]
  norm_num
  ring

lemma qB_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ qB u := by unfold qB; positivity

/-- `|E(u)| u^{−3} ≤ q(u)` for `u ≥ 16`. -/
lemma abs_E1_mul_le (hB : Psi1NatBound) {u : ℝ} (hu : 16 ≤ u) :
    |E1 u| * u ^ (-(3 : ℝ)) ≤ qB u := by
  have hu0 : 0 < u := by linarith
  have h := E1_le_Abd hB hu
  have hr : 0 ≤ u ^ (-(3 : ℝ)) := by positivity
  have e1 : u ^ 2 * u ^ (-(1 : ℝ) / 2) * u ^ (-(3 : ℝ)) = u ^ (-(3 : ℝ) / 2) := by
    rw [← rpow_natCast, ← rpow_add hu0, ← rpow_add hu0]; norm_num
  have e2 : u ^ 2 * u ^ (-(1 : ℝ)) * u ^ (-(3 : ℝ)) = u ^ (-(2 : ℝ)) := by
    rw [← rpow_natCast, ← rpow_add hu0, ← rpow_add hu0]; norm_num
  calc |E1 u| * u ^ (-(3 : ℝ)) ≤ u ^ 2 * Abd u * u ^ (-(3 : ℝ)) :=
        mul_le_mul_of_nonneg_right h hr
    _ = qB u := by
        unfold Abd qB
        rw [← e1, ← e2]; ring

lemma continuousOn_rpow_const_pos (a : ℝ) : ContinuousOn (fun t : ℝ => t ^ a) (Ioi 0) :=
  fun t ht => (Real.continuousAt_rpow_const t a (Or.inl (ne_of_gt ht))).continuousWithinAt

lemma integrableOn_abs_E1_mul (hB : Psi1NatBound) :
    IntegrableOn (fun t => |E1 t| * t ^ (-(3 : ℝ))) (Ioi 1) := by
  have hc : ContinuousOn (fun t => |E1 t| * t ^ (-(3 : ℝ))) (Ioi 0) :=
    (E1_continuous.abs.continuousOn).mul (continuousOn_rpow_const_pos _)
  have hsplit : Ioi (1 : ℝ) = Ioc 1 16 ∪ Ioi 16 := (Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · exact ((hc.mono fun t (ht : t ∈ Icc (1:ℝ) 16) => show (0:ℝ) < t from
      lt_of_lt_of_le one_pos ht.1).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  · refine (integrableOn_qB (by norm_num : (0:ℝ) < 16)).mono' ?_ ?_
    · exact (hc.mono fun t (ht : t ∈ Ioi (16:ℝ)) => show (0:ℝ) < t by
        have : (16:ℝ) < t := ht; linarith).aestronglyMeasurable
        measurableSet_Ioi
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 16 < t) => ?_
      rw [Real.norm_of_nonneg (by positivity)]
      exact abs_E1_mul_le hB ht.le

/-- **The constant.** `∫₁^∞ E(t) t^{−3} dt = −γ/2 − 3/4`. -/
theorem integral_E1_mul_rpow (hB : Psi1NatBound) :
    ∫ t in Ioi 1, E1 t * t ^ (-(3 : ℝ)) = -Real.eulerMascheroniConstant / 2 - 3 / 4 := by
  have hdom := integrableOn_abs_E1_mul hB
  have hL : Tendsto (fun s : ℝ => ∫ t in Ioi 1, E1 t * t ^ (-s - 2)) (𝓝[>] 1)
      (𝓝 (∫ t in Ioi 1, E1 t * t ^ (-(3 : ℝ)))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => |E1 t| * t ^ (-(3 : ℝ)))
      ?_ ?_ hdom ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact (mellin_E1 hs).1.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 1 < t) => ?_
      have ht0 : 0 < t := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left
        (rpow_le_rpow_of_exponent_le ht.le (by linarith)) (abs_nonneg _)
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 1 < t) => ?_
      have ht0 : t ≠ 0 := by linarith
      have hc : ContinuousAt (fun s : ℝ => E1 t * t ^ (-s - 2)) 1 :=
        continuousAt_const.mul ((Real.continuousAt_const_rpow ht0).comp
          ((continuousAt_id.neg).sub continuousAt_const))
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1:ℝ)))
      convert this using 2
      norm_num
  have hR : Tendsto (fun s : ℝ => Lr s / (s * (s + 1)) - 1 / (2 * (s - 1))) (𝓝[>] 1)
      (𝓝 (-Real.eulerMascheroniConstant / 2 - 3 / 4)) := by
    have hp : Tendsto (fun s : ℝ => s * (s + 1)) (𝓝[>] 1) (𝓝 (1 * (1 + 1))) :=
      ((continuous_id.mul (continuous_id.add continuous_const)).tendsto 1).mono_left
        nhdsWithin_le_nhds
    have hq : Tendsto (fun s : ℝ => (s + 2) / (2 * s * (s + 1))) (𝓝[>] 1)
        (𝓝 ((1 + 2) / (2 * 1 * (1 + 1)))) :=
      (((continuous_id.add continuous_const).tendsto 1).div
        (((continuous_const.mul continuous_id).mul (continuous_id.add continuous_const)).tendsto 1)
        (by norm_num : (2:ℝ) * 1 * (1 + 1) ≠ 0)).mono_left nhdsWithin_le_nhds
    have h := (tendsto_Lr_sub.div hp (by norm_num : (1:ℝ) * (1 + 1) ≠ 0)).sub hq
    convert h.congr' ?_ using 2
    · norm_num
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    have h1 : s - 1 ≠ 0 := by linarith
    have h2 : s ≠ 0 := by linarith
    have h3 : s + 1 ≠ 0 := by linarith
    simp only [Pi.div_apply]
    field_simp
    ring
  exact tendsto_nhds_unique hL (hR.congr' (by
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    exact (mellin_E1 hs).2.symm))

end LLS.Sharp.Principal
