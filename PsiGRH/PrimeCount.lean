import PsiGRH.Progression

/-!
# From `ϑ(x; q, a)` to `π(x; q, a)` (Montgomery–Vaughan (13.21), (13.24))

Abel summation with weight `1/log t` (`primeCountAP_abel`, from Mathlib's
`sum_mul_eq_sub_sub_integral_mul`):
`π(x; q, a) = ϑ(x; q, a)/log x + ∫₂ˣ ϑ(t; q, a)/(t log² t) dt`.
Integration by parts (`li_eq`): `li(x) = x/log x − 2/log 2 + ∫₂ˣ dt/log² t`. With
`E(t) = ϑ(t; q, a) − t/φ(q)`,

`π(x; q, a) − li(x)/φ(q) = E(x)/log x + ∫₂ˣ E(t)/(t log² t) dt + 2/(φ(q) log 2)`.

If `|E(t)| ≤ K √t (log t)(log qt)` for `t ≥ 2`, the three terms are at most `K √x log qx`,
`(K log qx / log 2) ∫₂ˣ dt/√t ≤ 3K √x log qx` and `3 ≤ 5 √x log qx`, so
`PiAPBound (4K + 5)` (`piAPBound_of_thetaAPBound`).
-/

namespace PsiGRH

open Finset MeasureTheory intervalIntegral

/-- `w(n) = log n` for primes `n ≡ a (mod q)`, else `0`; its partial sums are `ϑ(t; q, a)`. -/
noncomputable def thetaWeight (q a : ℕ) (n : ℕ) : ℝ :=
  if n.Prime ∧ n ≡ a [MOD q] then Real.log n else 0

lemma sum_thetaWeight (q a : ℕ) (t : ℝ) :
    ∑ k ∈ Icc 0 ⌊t⌋₊, thetaWeight q a k = thetaAP q a t := by
  classical
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc]
  simp [thetaWeight, thetaAP, Finset.sum_filter, Nat.not_prime_zero]

lemma primeCountAP_eq_sum (q a : ℕ) (x : ℝ) :
    (primeCountAP q a x : ℝ) = ∑ k ∈ Icc 0 ⌊x⌋₊, (Real.log k)⁻¹ * thetaWeight q a k := by
  classical
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc]
  have h0 : (Real.log ((0 : ℕ) : ℝ))⁻¹ * thetaWeight q a 0 = 0 := by
    simp [thetaWeight, Nat.not_prime_zero]
  rw [h0, zero_add]
  unfold primeCountAP
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr (by simp) fun k _ => ?_
  unfold thetaWeight
  split_ifs with h
  · have hk : 0 < Real.log k := Real.log_pos (by exact_mod_cast h.1.one_lt)
    simp [hk.ne']
  · simp

lemma hasDerivAt_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t => (Real.log t)⁻¹) (-(t⁻¹) / Real.log t ^ 2) t :=
  (Real.hasDerivAt_log (by linarith : t ≠ 0)).inv (Real.log_pos ht).ne'

lemma continuousOn_inv_mul_log_sq {x : ℝ} :
    ContinuousOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) (Set.Icc 2 x) := by
  refine ContinuousOn.inv₀ (continuousOn_id.mul ((Real.continuousOn_log.mono ?_).pow 2)) ?_
  · intro t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
  · intro t ht
    have h1 : 1 < t := by linarith [ht.1]
    exact mul_ne_zero (by linarith) (pow_ne_zero 2 (Real.log_pos h1).ne')

/-- Abel summation: `π(x; q, a) = ϑ(x; q, a)/log x + ∫₂ˣ ϑ(t; q, a)/(t log² t) dt`. -/
theorem primeCountAP_abel (q a : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    (primeCountAP q a x : ℝ) = thetaAP q a x / Real.log x +
      ∫ t in (2 : ℝ)..x, thetaAP q a t / (t * Real.log t ^ 2) := by
  classical
  set f : ℝ → ℝ := fun t => (Real.log t)⁻¹ with hf
  have hderiv : ∀ t ∈ Set.Icc (2 : ℝ) x, HasDerivAt f (-(t⁻¹) / Real.log t ^ 2) t :=
    fun t ht => hasDerivAt_inv_log (by linarith [ht.1])
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x, DifferentiableAt ℝ f t :=
    fun t ht => (hderiv t ht).differentiableAt
  have hcont : ContinuousOn (fun t : ℝ => -(t⁻¹) / Real.log t ^ 2) (Set.Icc 2 x) := by
    refine ContinuousOn.div (ContinuousOn.neg (continuousOn_inv₀.mono ?_))
      ((Real.continuousOn_log.mono ?_).pow 2) ?_
    · intro t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
    · intro t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
    · intro t ht; exact pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne'
  have hint : IntegrableOn (deriv f) (Set.Icc 2 x) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => ((hderiv t ht).deriv).symm) measurableSet_Icc
  have hA := sum_mul_eq_sub_sub_integral_mul (thetaWeight q a) (by norm_num : (0 : ℝ) ≤ 2) hx
    hdiff hint
  have h2 : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  rw [h2] at hA
  simp only [sum_thetaWeight] at hA
  have hI : ∫ t in Set.Ioc 2 x, deriv f t * thetaAP q a t =
      -∫ t in (2 : ℝ)..x, thetaAP q a t / (t * Real.log t ^ 2) := by
    rw [integral_of_le hx, ← MeasureTheory.integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [(hderiv t ⟨ht.1.le, ht.2⟩).deriv]
    have ht0 : t ≠ 0 := by linarith [ht.1]
    field_simp
  rw [hI] at hA
  have h2le : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hsplit : ∑ k ∈ Icc (0 : ℕ) ⌊x⌋₊, (Real.log (k : ℝ))⁻¹ * thetaWeight q a k =
      ∑ k ∈ Icc (0 : ℕ) 2, (Real.log (k : ℝ))⁻¹ * thetaWeight q a k +
        ∑ k ∈ Ioc (2 : ℕ) ⌊x⌋₊, (Real.log (k : ℝ))⁻¹ * thetaWeight q a k := by
    rw [← Finset.sum_union]
    · congr 1
      ext k
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      omega
    · rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk hk'
      omega
  have hsmall : ∑ k ∈ Icc (0 : ℕ) 2, (Real.log (k : ℝ))⁻¹ * thetaWeight q a k =
      f 2 * ∑ k ∈ Icc (0 : ℕ) 2, thetaWeight q a k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    unfold thetaWeight
    split_ifs with h
    · have hk2 : k = 2 := by
        have := h.1.two_le
        simp only [Finset.mem_Icc] at hk
        omega
      subst hk2
      simp [hf]
    · simp
  rw [primeCountAP_eq_sum, hsplit, hsmall]
  simp only [hf] at hA ⊢
  rw [hA]
  ring

/-- Integration by parts: `li(x) = x/log x − 2/log 2 + ∫₂ˣ dt/log² t`. -/
lemma li_eq {x : ℝ} (hx : 2 ≤ x) :
    li x = x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
  have hpos : ∀ t ∈ Set.uIcc (2 : ℝ) x, 1 < t := fun t ht => by
    rw [Set.uIcc_of_le hx] at ht; linarith [ht.1]
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x,
      HasDerivAt (fun t => t / Real.log t) (1 / Real.log t - 1 / Real.log t ^ 2) t := by
    intro t ht
    have h1 := hpos t ht
    have hl : Real.log t ≠ 0 := (Real.log_pos h1).ne'
    have ht0 : t ≠ 0 := by linarith
    have := (hasDerivAt_id' t).div (Real.hasDerivAt_log ht0) hl
    have e : (1 * Real.log t - t * t⁻¹) / Real.log t ^ 2 =
        1 / Real.log t - 1 / Real.log t ^ 2 := by
      rw [mul_inv_cancel₀ ht0, one_mul]
      field_simp
    rw [← e]
    exact this
  have hlogc : ContinuousOn Real.log (Set.uIcc (2 : ℝ) x) :=
    Real.continuousOn_log.mono fun t ht => by
      have := hpos t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith
  have hlogne : ∀ t ∈ Set.uIcc (2 : ℝ) x, Real.log t ≠ 0 :=
    fun t ht => (Real.log_pos (hpos t ht)).ne'
  have hc1 : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.uIcc 2 x) :=
    continuousOn_const.div hlogc hlogne
  have hc2 : ContinuousOn (fun t : ℝ => 1 / Real.log t ^ 2) (Set.uIcc 2 x) :=
    continuousOn_const.div (hlogc.pow 2) fun t ht => pow_ne_zero 2 (hlogne t ht)
  have hint1 := hc1.intervalIntegrable (μ := volume)
  have hint2 := hc2.intervalIntegrable (μ := volume)
  have hF := integral_eq_sub_of_hasDerivAt hderiv (hint1.sub hint2)
  rw [integral_sub hint1 hint2] at hF
  unfold li
  linarith

/-- `∫₂ˣ dt/√t ≤ 2√x`. -/
lemma integral_inv_sqrt_le {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / Real.sqrt t ≤ 2 * Real.sqrt x := by
  have hpos : ∀ t ∈ Set.uIcc (2 : ℝ) x, 0 < t := fun t ht => by
    rw [Set.uIcc_of_le hx] at ht; linarith [ht.1]
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x,
      HasDerivAt (fun t => 2 * Real.sqrt t) (1 / Real.sqrt t) t := by
    intro t ht
    have h0 := hpos t ht
    have := (Real.hasDerivAt_sqrt h0.ne').const_mul 2
    convert this using 1
    have : 0 < Real.sqrt t := Real.sqrt_pos.mpr h0
    field_simp
  have hcont : ContinuousOn (fun t : ℝ => 1 / Real.sqrt t) (Set.uIcc 2 x) :=
    continuousOn_const.div Real.continuous_sqrt.continuousOn
      fun t ht => (Real.sqrt_pos.mpr (hpos t ht)).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable (μ := volume))]
  have : 0 ≤ 2 * Real.sqrt 2 := by positivity
  linarith

/-- `ThetaAPBound K` implies `PiAPBound (4K + 5)`. -/
theorem piAPBound_of_thetaAPBound {K : ℝ} (hK : 0 ≤ K) (h : ThetaAPBound K) :
    PiAPBound (4 * K + 5) := by
  intro q a hq ha x hx
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hl2 := Real.log_two_gt_d9
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  set L := Real.log (q * x) with hLdef
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hLx : Real.log x ≤ L := Real.log_le_log (by linarith) (by nlinarith)
  have hs1 : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  set E : ℝ → ℝ := fun t => thetaAP q a t - t / q.totient with hE
  -- integrability
  have hg : IntegrableOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) (Set.Icc 2 x) :=
    continuousOn_inv_mul_log_sq.integrableOn_Icc
  have hθint : IntervalIntegrable (fun t => thetaAP q a t / (t * Real.log t ^ 2)) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
    have := integrableOn_mul_sum_Icc (thetaWeight q a) (m := 0) (by norm_num : (0 : ℝ) ≤ 2) hg
    refine this.congr_fun (fun t _ => ?_) measurableSet_Icc
    simp only
    rw [sum_thetaWeight, div_eq_inv_mul]
  have hpos : ∀ t ∈ Set.uIcc (2 : ℝ) x, 1 < t := fun t ht => by
    rw [Set.uIcc_of_le hx] at ht; linarith [ht.1]
  have hcint : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.div ((Real.continuousOn_log.mono ?_).pow 2) ?_
    · intro t ht; have := hpos t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith
    · intro t ht; exact pow_ne_zero 2 (Real.log_pos (hpos t ht)).ne'
  -- the identity
  have hId : (primeCountAP q a x : ℝ) - li x / q.totient =
      E x / Real.log x + (∫ t in (2 : ℝ)..x, E t / (t * Real.log t ^ 2)) +
        2 / (q.totient * Real.log 2) := by
    have hsplit : ∫ t in (2 : ℝ)..x, E t / (t * Real.log t ^ 2) =
        (∫ t in (2 : ℝ)..x, thetaAP q a t / (t * Real.log t ^ 2)) -
          (1 / (q.totient : ℝ)) * ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
      rw [← intervalIntegral.integral_const_mul, ← integral_sub hθint (hcint.const_mul _)]
      refine integral_congr fun t ht => ?_
      have h1 := hpos t ht
      have hl : Real.log t ≠ 0 := (Real.log_pos h1).ne'
      have ht0 : t ≠ 0 := by linarith
      have hφ0 : (q.totient : ℝ) ≠ 0 := by linarith
      simp only [hE]
      field_simp
    rw [primeCountAP_abel q a hx, li_eq hx, hsplit]
    have hl : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
    have hl2' : Real.log 2 ≠ 0 := by linarith
    have hφ0 : (q.totient : ℝ) ≠ 0 := by linarith
    simp only [hE]
    field_simp
    ring
  rw [hId]
  -- first term
  have hEx := h q a hq ha x hx
  have hlx0 : 0 < Real.log x := by linarith
  have hT1 : |E x / Real.log x| ≤ K * Real.sqrt x * L := by
    rw [abs_div, abs_of_pos hlx0, div_le_iff₀ hlx0]
    calc |E x| ≤ K * Real.sqrt x * Real.log x * L := hEx
      _ = K * Real.sqrt x * L * Real.log x := by ring
  -- the integral
  have hbound : ∀ t ∈ Set.Ioc (2 : ℝ) x,
      ‖E t / (t * Real.log t ^ 2)‖ ≤ K * L / Real.log 2 * (1 / Real.sqrt t) := by
    intro t ht
    have ht2 : 2 ≤ t := ht.1.le
    have ht0 : 0 < t := by linarith
    have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
    have hlt0 : 0 < Real.log t := by linarith
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
    have hLt : Real.log (q * t) ≤ L := Real.log_le_log (by positivity) (by nlinarith [ht.2])
    have hEt := h q a hq ha t ht2
    have hden : 0 < t * Real.log t ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    have htd : t / Real.sqrt t = Real.sqrt t := by
      rw [div_eq_iff hst.ne']; exact hsq.symm
    have hrhs : K * L / Real.log 2 * (1 / Real.sqrt t) * (t * Real.log t ^ 2) =
        K * Real.sqrt t * Real.log t * L * (Real.log t / Real.log 2) := by
      calc K * L / Real.log 2 * (1 / Real.sqrt t) * (t * Real.log t ^ 2)
          = K * L / Real.log 2 * (t / Real.sqrt t) * Real.log t ^ 2 := by ring
        _ = _ := by rw [htd]; ring
    rw [hrhs]
    have h1 : 1 ≤ Real.log t / Real.log 2 := by rw [le_div_iff₀ (by linarith)]; linarith
    have h0 : 0 ≤ K * Real.sqrt t * Real.log t * L := by
      have : 0 ≤ L := by linarith
      positivity
    calc |E t| ≤ K * Real.sqrt t * Real.log t * Real.log (q * t) := hEt
      _ ≤ K * Real.sqrt t * Real.log t * L := by gcongr
      _ = K * Real.sqrt t * Real.log t * L * 1 := by ring
      _ ≤ _ := by gcongr
  have hsqrtint : IntervalIntegrable (fun t : ℝ => 1 / Real.sqrt t) volume 2 x := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.div Real.continuous_sqrt.continuousOn fun t ht => ?_
    exact (Real.sqrt_pos.mpr (by linarith [hpos t ht])).ne'
  have hT2 : |∫ t in (2 : ℝ)..x, E t / (t * Real.log t ^ 2)| ≤ 3 * K * Real.sqrt x * L := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le hx (Filter.Eventually.of_forall hbound)
      (hsqrtint.const_mul _)).trans ?_
    rw [intervalIntegral.integral_const_mul]
    have hI := integral_inv_sqrt_le hx
    have hL0 : 0 ≤ L := by linarith
    have hc : 0 ≤ K * L / Real.log 2 := by positivity
    calc K * L / Real.log 2 * ∫ t in (2 : ℝ)..x, 1 / Real.sqrt t
        ≤ K * L / Real.log 2 * (2 * Real.sqrt x) := by gcongr
      _ = (2 / Real.log 2) * (K * Real.sqrt x * L) := by ring
      _ ≤ 3 * (K * Real.sqrt x * L) := by
          gcongr
          rw [div_le_iff₀ (by linarith)]; linarith
      _ = 3 * K * Real.sqrt x * L := by ring
  -- the constant
  have hT3 : |2 / ((q.totient : ℝ) * Real.log 2)| ≤ 5 * Real.sqrt x * L := by
    have hd : 0 < (q.totient : ℝ) * Real.log 2 := by positivity
    have hl20 : 0 < Real.log 2 := by linarith
    have hL2 : Real.log 2 ≤ L := by linarith
    have hsL : Real.log 2 ≤ Real.sqrt x * L := by nlinarith
    rw [abs_of_pos (by positivity)]
    calc 2 / ((q.totient : ℝ) * Real.log 2) ≤ 2 / Real.log 2 := by
          apply div_le_div_of_nonneg_left (by norm_num) hl20
          nlinarith
      _ ≤ 5 * Real.sqrt x * L := by
          rw [div_le_iff₀ hl20]
          nlinarith
  calc |E x / Real.log x + (∫ t in (2 : ℝ)..x, E t / (t * Real.log t ^ 2)) +
        2 / ((q.totient : ℝ) * Real.log 2)|
      ≤ |E x / Real.log x| + |∫ t in (2 : ℝ)..x, E t / (t * Real.log t ^ 2)| +
          |2 / ((q.totient : ℝ) * Real.log 2)| := abs_add_three _ _ _
    _ ≤ K * Real.sqrt x * L + 3 * K * Real.sqrt x * L + 5 * Real.sqrt x * L := by linarith
    _ = (4 * K + 5) * Real.sqrt x * L := by ring

end PsiGRH
